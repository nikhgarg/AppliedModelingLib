import GHW01DigitalGoods.MainTheorems
import GHW01DigitalGoods.Assumptions
import GHW01DigitalGoods.BidIndependentBoundary
import GHW01DigitalGoods.BoundedSupply
import GHW01DigitalGoods.FixedSizeSampling
import GHW01DigitalGoods.RandomSamplingDirectional
import GHW01DigitalGoods.SourceDefinitions
import GHW01DigitalGoods.BoundedSourceDefinitions
import GHW01DigitalGoods.WeightedPairingSourceModel

/-!
# Paper Interface: Competitive Auctions and Digital Goods

This is the compact human-facing Lean surface for the Goldberg-Hartline-Wright
digital-goods paper.  It lists the paper definitions and direct source
theorem statements; supporting auction lemmas live in `MainTheorems.lean` and
the reusable auction library.
-/

namespace GHW01DigitalGoods.ProofBridge

open AppliedModelingLib.Auction
open scoped BigOperators

noncomputable section

/-! ## Paper Definitions -/

/-! ### Source outcome and mechanism model

These transparent aliases keep the paper's definitions on the public review
surface.  Their implementations live in `SourceDefinitions.lean`, where the
source set-of-winners outcome model is kept separate from the proof-oriented
`DigitalGoodsAuction` encoding.
-/

/-- Utility values indexed by bidders (source lines 195--196). -/
abbrev source_bidValues (Agent : Type*) :=
  SourceDefinitions.BidValues Agent

/-- Submitted bids indexed by bidders (source lines 108 and 195--196). -/
abbrev source_bidProfile (Agent : Type*) :=
  SourceDefinitions.BidProfile Agent

/-- The source input distinguishes utility values from reports. -/
abbrev source_auctionInput (Agent : Type*) :=
  SourceDefinitions.AuctionInput Agent

/-- The truthful-report convention `b_i = u_i` (source lines 215--227). -/
abbrev source_truthfulReports {Agent : Type*}
    (input : source_auctionInput Agent) : Prop :=
  SourceDefinitions.TruthfulReports input

/-- Ascending-index presentation of an ordered bid profile. -/
abbrev source_sortedBidConvention {n : ℕ}
    (bids : source_bidProfile (Fin n)) : Prop :=
  SourceDefinitions.SortedBids bids

/-- A finite winner set with one sale price per bidder (source lines 200--203). -/
abbrev source_auctionOutcome (Agent : Type*) :=
  SourceDefinitions.AuctionOutcome Agent

/-- Winners are served at prices no larger than their reports. -/
abbrev source_outcomeFillsAtOrBelow {Agent : Type*}
    (outcome : source_auctionOutcome Agent) (bids : source_bidProfile Agent) : Prop :=
  SourceDefinitions.AuctionOutcome.FillsAtOrBelow outcome bids

/-- One common sale price for every winner (source lines 67--70). -/
abbrev source_singlePriceOutcome {Agent : Type*}
    (outcome : source_auctionOutcome Agent) : Prop :=
  SourceDefinitions.AuctionOutcome.IsSinglePrice outcome

/-- An outcome realizing unequal winner prices (source lines 67--70). -/
abbrev source_differentPriceOutcome {Agent : Type*}
    (outcome : source_auctionOutcome Agent) : Prop :=
  SourceDefinitions.AuctionOutcome.UsesDifferentPrices outcome

/-- Every deterministic outcome uses one common winner price. -/
abbrev source_deterministicIsSinglePrice {Agent : Type*}
    (auction : SourceDefinitions.DeterministicAuction Agent) : Prop :=
  SourceDefinitions.DeterministicIsSinglePrice auction

/-- Every positive-probability randomized outcome uses one common price. -/
abbrev source_randomizedIsSinglePrice {Agent : Type*}
    (auction : SourceDefinitions.RandomizedAuction Agent) : Prop :=
  SourceDefinitions.RandomizedIsSinglePrice auction

/-- A deterministic mechanism realizes unequal winner prices somewhere. -/
abbrev source_deterministicUsesMultiplePrices {Agent : Type*}
    (auction : SourceDefinitions.DeterministicAuction Agent) : Prop :=
  SourceDefinitions.DeterministicUsesMultiplePrices auction

/-- A randomized mechanism can realize unequal winner prices. -/
abbrev source_randomizedUsesMultiplePrices {Agent : Type*}
    (auction : SourceDefinitions.RandomizedAuction Agent) : Prop :=
  SourceDefinitions.RandomizedUsesMultiplePrices auction

/-- Multi-price deterministic mechanisms may, but need not, use unequal prices. -/
abbrev source_deterministicMultiPriceAuction (Agent : Type*) :=
  SourceDefinitions.DeterministicAuction Agent

/-- Randomized mechanisms whose outcome prices are not restricted to one price. -/
abbrev source_randomizedMultiPriceAuction (Agent : Type*) :=
  SourceDefinitions.RandomizedAuction Agent

/-- Deterministic mechanisms map reports to outcomes. -/
abbrev source_deterministicAuction (Agent : Type*) :=
  SourceDefinitions.DeterministicAuction Agent

/-- Randomized mechanisms map reports to outcome distributions. -/
abbrev source_randomizedAuction (Agent : Type*) :=
  SourceDefinitions.RandomizedAuction Agent

/-- Unlimited supply imposes no winner-cardinality restriction. -/
abbrev source_unlimitedSupplyDeterministicAuction (Agent : Type*) :=
  SourceDefinitions.UnlimitedSupplyDeterministicAuction Agent

/-- Randomized unlimited-supply mechanism model. -/
abbrev source_unlimitedSupplyRandomizedAuction (Agent : Type*) :=
  SourceDefinitions.UnlimitedSupplyRandomizedAuction Agent

/-- Profit is value minus price for a winner and zero for a loser. -/
abbrev source_profitDefinition {Agent : Type*}
    (outcome : source_auctionOutcome Agent) (values : source_bidValues Agent)
    (i : Agent) : ℝ := by
  classical
  exact SourceDefinitions.AuctionOutcome.profit outcome values i

/-- Revenue of one outcome is the sum of its winner sale prices. -/
abbrev source_outcomeRevenue {Agent : Type*}
    (outcome : source_auctionOutcome Agent) : ℝ :=
  SourceDefinitions.AuctionOutcome.revenue outcome

/-- Deterministic revenue `R` (source lines 210--214). -/
abbrev source_deterministicRevenue {Agent : Type*}
    (auction : source_deterministicAuction Agent)
    (bids : source_bidProfile Agent) : ℝ :=
  SourceDefinitions.deterministicRevenue auction bids

/-- Randomized revenue `R` as an outcome-induced random variable. -/
abbrev source_randomizedRevenueLaw {Agent : Type*}
    (auction : source_randomizedAuction Agent)
    (bids : source_bidProfile Agent) :=
  SourceDefinitions.randomizedRevenueLaw auction bids

/-- Deterministic dominant-strategy truthfulness. -/
abbrev source_deterministicTruthful {Agent : Type*}
    (auction : source_deterministicAuction Agent) : Prop := by
  classical
  exact SourceDefinitions.DeterministicTruthful auction

/-- Expected-profit dominant-strategy truthfulness for randomized auctions. -/
abbrev source_randomizedTruthful {Agent : Type*}
    (auction : source_randomizedAuction Agent) : Prop := by
  classical
  exact SourceDefinitions.RandomizedTruthful auction

/-- Correct deterministic auctions are truthful and fill winners feasibly. -/
abbrev source_deterministicCorrect {Agent : Type*}
    (auction : source_deterministicAuction Agent) : Prop := by
  classical
  exact SourceDefinitions.DeterministicCorrect auction

/-- Correct randomized auctions are truthful and outcome-wise feasible. -/
abbrev source_randomizedCorrect {Agent : Type*}
    (auction : source_randomizedAuction Agent) : Prop := by
  classical
  exact SourceDefinitions.RandomizedCorrect auction

/-! ### Fixed prices and analysis conventions -/

/-- Fixed-price outcome at threshold `p` (source lines 97--102). -/
abbrev source_fixedPriceOutcome {Agent : Type*} [Fintype Agent]
    (bids : source_bidProfile Agent) (p : ℝ) : source_auctionOutcome Agent :=
  SourceDefinitions.fixedPriceOutcome bids p

/-- Fixed-price mechanism at a bid-independent threshold. -/
abbrev source_fixedPriceAuction {Agent : Type*} [Fintype Agent]
    (p : ℝ) : source_deterministicAuction Agent :=
  SourceDefinitions.fixedPriceAuction p

/-- Revenue obtained by a fixed price `p`. -/
abbrev source_fixedPriceRevenue {Agent : Type*} [Fintype Agent]
    (bids : source_bidProfile Agent) (p : ℝ) : ℝ :=
  SourceDefinitions.fixedPriceRevenue bids p

/-- `F`, the best fixed-price revenue over input-bid prices. -/
abbrev source_optimalFixedPriceRevenue {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent) : ℝ :=
  SourceDefinitions.optimalFixedPriceRevenue bids

/-- Relational source definition of a threshold attaining `F`. -/
abbrev source_isOptimalThreshold {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent) (p : ℝ) : Prop :=
  SourceDefinitions.IsOptimalThreshold bids p

/-- A tie-broken choice of the source `opt(B)`. -/
abbrev source_optimalThresholdDefinition {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent) : ℝ :=
  SourceDefinitions.optimalThreshold bids

/-- The optimal single-price outcome induced by `opt(B)`. -/
abbrev source_optimalSinglePriceOutcome {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent) : source_auctionOutcome Agent :=
  SourceDefinitions.optimalSinglePriceOutcome bids

/-- The source's optimal single-price mechanism. -/
abbrev source_optimalSinglePriceAuction {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] : source_deterministicAuction Agent :=
  SourceDefinitions.optimalSinglePriceAuction

/-- `n`, the number of bidders. -/
abbrev source_bidderCount (Agent : Type*) [Fintype Agent] : ℕ :=
  SourceDefinitions.bidderCount Agent

/-- `ℓ`, the smallest bid in a nonempty profile. -/
abbrev source_lowestBid {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent) : ℝ :=
  SourceDefinitions.lowestBid bids

/-- `h`, the largest bid in a nonempty profile. -/
abbrev source_highestBid {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent) : ℝ :=
  SourceDefinitions.highestBid bids

/-- The source normalization `ℓ = 1`. -/
abbrev source_normalizedBidScale {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent) : Prop :=
  SourceDefinitions.NormalizedBidScale bids

/-- Displayed performance ratio `R / B`. -/
abbrev source_performanceRatio (auctionRevenue benchmark : ℝ) : ℝ :=
  SourceDefinitions.performanceRatio auctionRevenue benchmark

/-- Uniform constant-factor lower-bound convention `R = Ω(B)`. -/
abbrev source_revenueBigOmega {Instance : Type*}
    (auctionRevenue benchmark : Instance → ℝ) : Prop :=
  SourceDefinitions.RevenueBigOmega auctionRevenue benchmark

/-- Uniform constant-factor upper-bound convention `R = O(B)`. -/
abbrev source_revenueBigO {Instance : Type*}
    (auctionRevenue benchmark : Instance → ℝ) : Prop :=
  SourceDefinitions.RevenueBigO auctionRevenue benchmark

/-- The source large-market condition `α h ≤ F`. -/
abbrev source_fixedPriceScaleCondition (alpha highest fixedPrice : ℝ) : Prop :=
  SourceDefinitions.fixedPriceScaleCondition alpha highest fixedPrice

/-- The weaker source condition `α h ≤ T`. -/
abbrev source_totalValueScaleCondition (alpha highest total : ℝ) : Prop :=
  SourceDefinitions.totalValueScaleCondition alpha highest total

/-- The positive-scale convention used by the source asymptotics. -/
abbrev source_positiveAlpha (alpha : ℝ) : Prop :=
  SourceDefinitions.PositiveAlpha alpha

/-- Uniform competitiveness on an admissible instance class. -/
abbrev source_competitiveDefinition {Instance : Type*}
    (admissible : Instance → Prop) (auctionRevenue benchmark : Instance → ℝ) : Prop :=
  SourceDefinitions.CompetitiveOn admissible auctionRevenue benchmark

/-- The source's `R / B = Ω(1)` formulation is exactly its uniform
competitiveness condition `R = Ω(B)` whenever the benchmark is positive on
the admissible instances.  The positivity premise records the source-domain
condition needed to divide by `B`; the competitive definition itself is
unchanged. -/
theorem source_competitive_iff_uniformPositiveRevenueBenchmarkRatio
    {Instance : Type*} (admissible : Instance → Prop)
    (auctionRevenue benchmark : Instance → ℝ)
    (hbenchmark_pos : ∀ x, admissible x → 0 < benchmark x) :
    source_competitiveDefinition admissible auctionRevenue benchmark ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x, admissible x →
        c ≤ source_performanceRatio (auctionRevenue x) (benchmark x) := by
  exact SourceDefinitions.competitiveOn_iff_uniformPositivePerformanceRatio
    admissible auctionRevenue benchmark hbenchmark_pos

/-! ### Vickrey and bid-independent families -/

/-- Source relational definition of a `k`-item Vickrey outcome. -/
abbrev source_kItemVickreyOutcome {Agent : Type*}
    [Fintype Agent] [DecidableEq Agent]
    (bids : source_bidProfile Agent) (k : ℕ)
    (outcome : source_auctionOutcome Agent) : Prop :=
  SourceDefinitions.IsKItemVickreyOutcome bids k outcome

/-- A mechanism implementing the `k`-item Vickrey rule on every profile. -/
abbrev source_kItemVickreyAuction {Agent : Type*}
    [Fintype Agent]
    (auction : source_deterministicAuction Agent) (k : ℕ) : Prop := by
  classical
  exact SourceDefinitions.IsKItemVickreyAuction auction k

/-- Admissible supply-size rule for the unlimited Vickrey family. -/
abbrev source_admissibleVickreySupplyRule (f : ℕ → ℕ) : Prop :=
  SourceDefinitions.AdmissibleVickreySupplyRule f

/-- Weak or strict acceptance at an offered threshold. -/
abbrev source_thresholdBoundaryConvention :=
  SourceDefinitions.ThresholdBoundary

/-- A bid-independent price together with its boundary convention. -/
abbrev source_thresholdOffer := SourceDefinitions.ThresholdOffer

/-- Acceptance under the selected weak or strict boundary. -/
abbrev source_acceptsThreshold
    (offer : source_thresholdOffer) (bid : ℝ) : Prop :=
  SourceDefinitions.accepts offer bid

/-- `B_i`, retaining repeated values while removing bidder `i`. -/
abbrev source_otherBids {Agent : Type*} [Fintype Agent]
    (bids : source_bidProfile Agent) (i : Agent) : Multiset ℝ := by
  classical
  exact SourceDefinitions.otherBids bids i

/-- Predetermined offers as a function of the other reports. -/
abbrev source_bidIndependentRule := SourceDefinitions.BidIndependentRule

/-- Outcome induced by a bid-independent offer rule. -/
abbrev source_bidIndependentOutcome {Agent : Type*}
    [Fintype Agent]
    (rule : source_bidIndependentRule) (bids : source_bidProfile Agent) :
    source_auctionOutcome Agent := by
  classical
  exact SourceDefinitions.bidIndependentOutcome rule bids

/-- The deterministic bid-independent auction induced by the rule. -/
abbrev source_bidIndependentAuction {Agent : Type*}
    [Fintype Agent]
    (rule : source_bidIndependentRule) : source_deterministicAuction Agent := by
  classical
  exact SourceDefinitions.bidIndependentAuction rule

/-! ### Sampling and weighted-pairing mechanisms -/

/-- Bid-independent sample law and threshold rule for random sampling. -/
abbrev source_randomSamplingPlan (Agent : Type*) :=
  SourceDefinitions.RandomSamplingPlan Agent

/-- The randomized directional sample mechanism as an outcome law. -/
abbrev source_randomSamplingAuction {Agent : Type*}
    [Fintype Agent]
    (plan : source_randomSamplingPlan Agent) : source_randomizedAuction Agent := by
  classical
  exact plan.directionalOutcomeLaw

/-- The randomized dual-price sample mechanism as an outcome law. -/
abbrev source_dualPriceRandomSamplingAuction {Agent : Type*}
    [Fintype Agent]
    (plan : source_randomSamplingPlan Agent) : source_randomizedAuction Agent := by
  classical
  exact plan.dualPriceOutcomeLaw

/-- Uniform law on samples containing exactly half of the bidders. -/
abbrev source_exactHalfSampleLaw
    (Agent : Type*) [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize) :=
  SourceDefinitions.exactHalfSampleLaw Agent sampleSize hsample_pos hhalf

/-- The exact-half optimal-threshold auction as a randomized source mechanism. -/
abbrev source_exactHalfOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (boundary : source_thresholdBoundaryConvention) :
    source_randomizedAuction Agent := by
  classical
  letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
  exact SourceDefinitions.exactHalfOptimalThresholdOutcomeLaw
    sampleSize hsample_pos hhalf boundary

/-- Independent fair-coin sampling used only for the source analysis. -/
abbrev source_independentHalfSamplingAnalysisLaw (Agent : Type*) :=
  SourceDefinitions.independentHalfSamplingAnalysisLaw Agent

/-- The weighted-pairing auction's genuine joint outcome law on the paper's
normalized, nonsingleton bid domain. -/
abbrev source_weightedPairingAuction {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i) := by
  classical
  exact SourceDefinitions.weightedPairingOutcomeLaw bids
    (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
      bids hbid_ge_one hdistinct)

/-- Finite expected revenue of the weighted-pairing joint outcome law. -/
abbrev source_weightedPairingOutcomeExpectedRevenue {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i) : ℝ := by
  classical
  exact SourceDefinitions.weightedPairingOutcomeExpectedRevenue bids
    (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
      bids hbid_ge_one hdistinct)

/-- `W`, the total expected revenue of the weighted-pairing auction. -/
abbrev source_weightedPairingW {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i) : ℝ := by
  classical
  exact SourceDefinitions.weightedPairingW bids
    (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
      bids hbid_ge_one hdistinct)

/-- The joint outcome sampler's finite expected revenue is exactly `W`. -/
theorem source_weightedPairingOutcomeExpectedRevenue_eq_W
    {Agent : Type*} [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i) :
    source_weightedPairingOutcomeExpectedRevenue bids hbid_ge_one hdistinct =
      source_weightedPairingW bids hbid_ge_one hdistinct := by
  classical
  exact SourceDefinitions.weightedPairingOutcomeExpectedRevenue_eq_W bids
    (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
      bids hbid_ge_one hdistinct)

/-- The deterministic auction offering bidder `i` the canonical `opt(B_i)`. -/
abbrev source_deterministicOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent]
    (hcard : 2 ≤ Fintype.card Agent) : DigitalGoodsAuction Agent := by
  classical
  letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
  exact SourceDefinitions.deterministicOptimalThresholdAuction hcard

/-! ### Bounded-supply definitions -/

/-- A binary auction allocating at most `k` units on every input. -/
abbrev source_boundedSupplyModel {Agent : Type*} [Fintype Agent]
    (auction : DigitalGoodsAuction Agent) (capacity : ℕ) : Prop :=
  SourceDefinitions.IsKItemBoundedSupplyAuction auction capacity

/-- `F_k`, optimal fixed-price revenue subject to capacity `k`. -/
abbrev source_boundedSupplyFk {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) : ℝ :=
  SourceDefinitions.boundedSupplyFk bids capacity

/-- Relational source predicate for a threshold attaining `F_k`. -/
abbrev source_isBoundedSupplyOptimalThreshold {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) (price : ℝ) : Prop :=
  SourceDefinitions.IsBoundedSupplyOptimalThreshold bids capacity price

/-- Scarce supply means some optimal price fills capacity at both `k` and
`k+1`; the two optimizer witnesses may differ. -/
abbrev source_scarceSupply {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) : Prop :=
  SourceDefinitions.scarceSupply bids capacity

/-- `T_k`, the largest total value of exactly `k` bids. -/
abbrev source_boundedSupplyTk {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ) (capacity : ℕ)
    (hcapacity : capacity ≤ Fintype.card Agent) : ℝ := by
  classical
  exact SourceDefinitions.boundedSupplyTk bids capacity hcapacity

/-- Canonical value-level threshold `opt_k` attaining `F_k`. -/
abbrev source_boundedSupplyOptK {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) : ℝ :=
  SourceDefinitions.boundedSupplyOptK bids capacity

/-- Uniform fixed-size bounded single-price sampling under `0 < m < n`, with
the explicit floor convention for `m*k/(n-m)` and a fixed exogenous bidder
priority implementing the source's arbitrary excess-rejection rule. -/
abbrev source_boundedSinglePriceSampling
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < Fintype.card Agent) (capacity : ℕ) :
    source_randomizedAuction Agent := by
  letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
  exact SourceDefinitions.boundedSinglePriceFixedSizeOutcomeLaw
    sampleSize hsample_pos hsample_lt capacity

/-- Bounded dual-price sampling on exact equal halves with explicitly even
total capacity `2 * halfCapacity` and the same fixed exogenous excess-rejection
priority. -/
abbrev source_boundedDualPriceSampling
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (halfCapacity : ℕ) : source_randomizedAuction Agent := by
  letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
  exact SourceDefinitions.boundedDualExactHalfOutcomeLaw
    sampleSize hsample_pos hhalf halfCapacity

/--
Digital-goods auction revenue: the sum of sale prices of selected bids.

The source outcome model represents an outcome as a set, so a selected bid is
encoded by allocation `1`. This definition deliberately excludes a payment
attached to every other library allocation value; the paper-facing theorem
below makes the required binary-outcome convention explicit.
-/
def revenue {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, if M.allocation values i = 1 then M.payment values i else 0

/-- The source sale-price definition applies to binary auction outcomes: its
revenue is exactly the sum of the prices attached to selected bids.

Source status: direct source definition.
-/
theorem revenue_source_definition
    {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (_hbinary : M.BinaryAllocation)
    (values : Agent → ℝ) :
    revenue M values =
      ∑ i : Agent, if M.allocation values i = 1 then M.payment values i else 0 := by
  rfl

/-- On an ordinary source auction outcome, winner-sale-price revenue agrees
with the library's total-payment revenue. -/
theorem revenue_eq_totalPayments_of_losersPayZero
    {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (hbinary : M.BinaryAllocation)
    (values : Agent → ℝ)
    (hlosers : M.LosersPayZero) :
    revenue M values = M.revenue values := by
  unfold revenue DigitalGoodsAuction.revenue
  apply Finset.sum_congr rfl
  intro i _
  by_cases hone : M.allocation values i = 1
  · simp [hone]
  · have hzero : M.allocation values i = 0 :=
      (hbinary values i).resolve_right hone
    simp [hone, hlosers values i hzero]

/--
Dominant-strategy truthfulness: truthful bidding weakly dominates replacing
one agent's value report by any alternative report.

Source status: direct source definition; the reviewed theorem immediately
below proves the definition unfolds to the exact dominant-strategy formula.
-/
def truthful {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

/--
The paper's truthfulness definition is exactly the displayed dominant-strategy
utility comparison, with every other report held fixed.

Source status: direct source definition.
-/
theorem truthful_iff_source_definition
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) :
    truthful M ↔
      ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
        M.utility values i (Function.update values i report) ≤
          M.utility values i values := by
  rfl

/-- Single-price revenue at price `p`. -/
def singlePriceRevenue {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Agent, if p ≤ values i then p else 0

/-- The paper's unlimited-supply fixed-price benchmark `F`. -/
def fixedPriceBenchmark {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) : ℝ :=
  finiteCandidateFixedPriceBenchmark values 1

/-- The paper's `opt(B)`: a candidate price attaining the unlimited-supply
fixed-price benchmark. -/
def optimalThreshold {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) : ℝ :=
  finiteCandidateOfferPrice values 1

/-- On the paper's normalized bid domain, `opt(B)` is an input bid and achieves
the fixed-price benchmark `F`.  The lower-bound premise rules out the
library's totalized zero-price fallback, which is not part of the source
`argmax_{b_i \in B}` definition.

Source status: direct source definition endpoint.
-/
theorem optimalThreshold_attains_fixedPriceBenchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i) :
    (∃ i : Agent, optimalThreshold values = values i) ∧
      singlePriceRevenue values (optimalThreshold values) =
        fixedPriceBenchmark values := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
  have hself_count : 1 ≤ saleCount values (values i) := by
    change 1 ≤ ((Finset.univ : Finset Agent).filter
      (fun j => values i ≤ values j)).card
    exact Finset.card_pos.mpr ⟨i, by simp⟩
  have hsingle_pos : 0 < singlePriceRevenue values (values i) := by
    change 0 < AppliedModelingLib.Auction.singlePriceRevenue values (values i)
    rw [AppliedModelingLib.Auction.singlePriceRevenue_eq_saleCount_mul]
    have hcount_pos : 0 < (saleCount values (values i) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hself_count)
    exact mul_pos hcount_pos (lt_of_lt_of_le zero_lt_one (hvalue_ge_one i))
  have hbenchmark_pos :
      0 < finiteCandidateFixedPriceBenchmark values 1 := by
    exact lt_of_lt_of_le hsingle_pos
      (singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
        values 1 i (le_trans zero_le_one (hvalue_ge_one i)) hself_count)
  have hprice_ge_one : 1 ≤ optimalThreshold values := by
    simpa [optimalThreshold] using
      finiteCandidateOfferPrice_ge_one_of_benchmark_pos values 1 hvalue_ge_one
        hbenchmark_pos
  have hprice_mem : optimalThreshold values ∈ finiteCandidatePriceSet values := by
    simpa [optimalThreshold] using finiteCandidateOfferPrice_mem_priceSet values 1
  have hprice_ne_zero : optimalThreshold values ≠ 0 := by
    linarith
  have hinput : ∃ i : Agent, optimalThreshold values = values i := by
    rw [finiteCandidatePriceSet] at hprice_mem
    rcases Finset.mem_insert.mp hprice_mem with hzero | himage
    · exact False.elim (hprice_ne_zero hzero)
    · rcases Finset.mem_image.mp himage with ⟨j, -, hj⟩
      exact ⟨j, hj.symm⟩
  exact ⟨hinput,
    singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark values 1⟩

/--
The paper's fixed-price benchmark `F` for the displayed Theorem 7.2
tightness family.  The source-family premise `2 ≤ s` supplies a top bid, so
this is exactly `fixedPriceBenchmark (ghwTightValue k s)` without an extra
nonemptiness assumption.
-/
noncomputable def ghwTightFixedPriceBenchmarkValue
    (k s : ℕ) (hs_two : 2 ≤ s) : ℝ :=
  have hs_pos : 0 < s := by omega
  letI : Nonempty (GhwTightAgent k s) := ⟨Sum.inr ⟨0, hs_pos⟩⟩
  fixedPriceBenchmark (ghwTightValue k s)

/--
Two-winner fixed-price benchmark `F^(2)`: the best single-price revenue selling
to at least two bidders.
-/
def twoWinnerBenchmark {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  twoWinnerFixedPriceBenchmarkValue values

/--
Total bid value `T = sum_i v_i`.

Source status: direct source text.
Source note: GHW define `T` as the sum of all bids in the input profile.
-/
def totalValue {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, values i

/-- For truthful source inputs, the paper's utility-profile total, its
bid-defined `T`, and the revenue obtained by serving every bidder at their bid
coincide.  Truthful reporting is visible here because only that convention
identifies utility values with submitted bids; `totalValue` itself remains an
unconditional sum.

Source: lines 215-232.
-/
theorem source_truthfulReports_totalValue_bridge
    {Agent : Type*} [Fintype Agent] (input : source_auctionInput Agent)
    (htruth : SourceDefinitions.TruthfulReports input) :
    totalValue input.values = SourceDefinitions.totalBidValue input.bids ∧
      SourceDefinitions.totalBidValue input.bids =
        (SourceDefinitions.fullValueOutcome input.bids).revenue := by
  simpa [totalValue] using
    SourceDefinitions.truthfulReports_utilitySum_eq_totalBidValue_and_fullValueRevenue
      input htruth

/-- Expected revenue of the weighted-pairing auction. -/
def weightedPairingRevenue {Agent : Type*}
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  weightedPairingExpectedRevenue values

/--
The source weighted-pairing definition, with its probability domain made
explicit.  The source's normalized lower-bid convention gives every bid value
at least one, and the instruction to sample a bid from `B_i` requires another
bidder for each bidder.  Lean derives nonnegativity and positive other-bid
mass from those source primitives, rather than accepting an opaque certificate
with those conclusions as a caller-supplied premise.

The conclusion exposes the three operational facts used by the source: no
self-selection, nonnegative normalized selection weights, and equality of the
operational expected revenue with `W`.

Source status: direct source definition under visible normalized-bid and non-singleton conventions.
-/
theorem weightedPairingRevenue_source_definition
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hhas_other_bidder : ∀ i : Agent, ∃ j : Agent, j ≠ i) :
    (∀ i j : Agent, 0 ≤ weightedPairingOfferProbability values i j) ∧
    (∀ i : Agent, weightedPairingOfferProbability values i i = 0) ∧
    (∀ i : Agent,
      ∑ j : Agent, weightedPairingOfferProbability values i j = 1) ∧
    weightedPairingSourceOperationalExpectedRevenue values
      (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
        values hbid_ge_one hhas_other_bidder) =
      weightedPairingRevenue values := by
  let source : WeightedPairingSourceProfile values :=
    weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
      values hbid_ge_one hhas_other_bidder
  change
    (∀ i j : Agent, 0 ≤ weightedPairingOfferProbability values i j) ∧
      (∀ i : Agent, weightedPairingOfferProbability values i i = 0) ∧
      (∀ i : Agent,
        ∑ j : Agent, weightedPairingOfferProbability values i j = 1) ∧
      weightedPairingSourceOperationalExpectedRevenue values source =
        weightedPairingRevenue values
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact weightedPairingOfferProbability_nonneg values source i j
  · intro i
    exact weightedPairingOfferProbability_self values i
  · intro i
    exact weightedPairingOfferProbability_sum_eq_one values source i
  · simpa [weightedPairingRevenue] using
      GHW01DigitalGoods.weightedPairingRevenue_source_definition values source

/--
Section 11's `F_k`: optimal fixed-price revenue selling at most `k` units.

Source status: direct source definition.
-/
def boundedBenchmark {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) : ℝ :=
  boundedSupplyFixedPriceBenchmark values capacity

/-- Internal bounded-supply top-value vocabulary.  The paper-facing source
definition is stated by `boundedTopKValue_source_definition`, which exposes
the exact-cardinality and nonnegative-bid conditions needed to identify this
at-most-`k` implementation with the paper's `T_k`. -/
def boundedTopKValue {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) : ℝ :=
  boundedSupplyTopKTotal values capacity

/--
Section 11's `T_k` is the maximum multi-price revenue with exactly `k`
satisfied bidders: the sum of the highest `k` bids.  On the source domain
`k ≤ n` and nonnegative bids, that is equal to the internal at-most-`k`
finite maximum.

Source status: direct source definition.
-/
theorem boundedTopKValue_source_definition
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ)
    (hcapacity : capacity ≤ Fintype.card Agent)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i) :
    boundedTopKValue values capacity =
      ((Finset.univ : Finset Agent).powerset.filter fun s =>
        s.card = capacity).sup'
        (by
          obtain ⟨s, hs_sub, hs_card⟩ :=
            Finset.exists_subset_card_eq
              (s := (Finset.univ : Finset Agent)) hcapacity
          exact ⟨s, Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr hs_sub, hs_card⟩⟩)
        (fun s => ∑ i ∈ s, values i) := by
  simpa [boundedTopKValue] using
    boundedSupplyTopKTotal_eq_exact_cardinality_of_nonneg
      values capacity hcapacity hvalues_nonneg

/--
Section 11's `opt_k`: a threshold attaining `F_k`.

Source status: direct source definition.
-/
def boundedOptimalThreshold {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) : ℝ :=
  boundedSupplyOptimalThreshold values capacity

/-- On the paper's normalized bid domain, `opt_k` is an input-bid threshold
attaining `F_k`; the capped revenue definition itself enforces the at-most-`k`
sale limit.

Source status: direct source definition endpoint.
-/
theorem boundedOptimalThreshold_attains_boundedBenchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i) :
    (∃ i : Agent,
      boundedOptimalThreshold values capacity = values i) ∧
      boundedSupplySinglePriceRevenue values capacity
          (boundedOptimalThreshold values capacity) =
        boundedBenchmark values capacity := by
  let i := boundedSupplyBenchmarkBidder values capacity
  have hi_nonneg : 0 ≤ values i :=
    le_trans zero_le_one (hvalue_ge_one i)
  have hthreshold : boundedOptimalThreshold values capacity = values i := by
    simp [boundedOptimalThreshold, boundedSupplyOptimalThreshold, i, hi_nonneg]
  refine ⟨⟨i, hthreshold⟩, ?_⟩
  exact boundedSupplyOptimalThreshold_revenue_eq_benchmark values capacity

/-! ## Source Theorems -/

/--
Theorem 4.1: high-value profiles have the printed logarithmic fixed-price
lower bound on the corrected domain `2 <= h`.

The source parameter `h` is the attained highest bid, not merely a numerical
upper bound.

Source status: approved corrected source target. The archival SODA endpoint
omits this nondegenerate domain and is retained separately in the audit record;
the Lean theorem does not claim to prove that archival statement.
-/
def theorem4_1_high_valueSpec : Prop :=
  ∀ {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {h : ℝ}
    (_hh_ge_two : 2 ≤ h)
    (_hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (_hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (_hhighest : ∃ i : Agent, values i = h),
    let _ : Nonempty Agent := ⟨Classical.choose _hhighest⟩
    totalValue values ≤
      (2 * Real.logb 2 h) * fixedPriceBenchmark values

theorem theorem4_1_high_value : theorem4_1_high_valueSpec := by
  intro Agent _ values h hh_ge_two hvalue_ge_one hvalue_le_h hhighest
  classical
  letI : Nonempty Agent := ⟨Classical.choose hhighest⟩
  have _hsource_attained : ∃ i : Agent, values i = h := hhighest
  simpa [totalValue, fixedPriceBenchmark] using
    paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
      values hh_ge_two hvalue_ge_one hvalue_le_h

/--
Corollary 4.2: truncating bids below `h / n` and applying Theorem 4.1 gives
the printed logarithmic fixed-price lower bound on the corrected domain
`2 <= n`.

Source status: approved corrected source target. The archival SODA endpoint is
retained separately in the audit record; this theorem does not claim to prove
it verbatim.
Source note: the cutoff truncation and scaled benchmark comparison are derived
internally from the source proof.  The source does not state `2 <= n`; its
real-log denominator is degenerate at `n = 1`, so this is a visible repair
condition rather than a source-implied premise.
-/
def corollary4_2_fixed_price_lower_boundSpec : Prop :=
  ∀ {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {h : ℝ}
    (_hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (_hh_pos : 0 < h)
    (_hmax : ∃ i : Agent, values i = h)
    (_hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (_hcard_ge_two : 2 ≤ (Fintype.card Agent : ℝ)),
    let _ : Nonempty Agent := ⟨Classical.choose _hmax⟩
    totalValue values ≤
      (4 * Real.logb 2 (Fintype.card Agent : ℝ)) *
        fixedPriceBenchmark values

theorem corollary4_2_fixed_price_lower_bound :
    corollary4_2_fixed_price_lower_boundSpec := by
  intro Agent _ values h hvalues_nonneg hh_pos hmax hvalue_le_h hcard_ge_two
  classical
  letI : Nonempty Agent := ⟨Classical.choose hmax⟩
  simpa [totalValue, fixedPriceBenchmark] using
    paper_corollary4_2_fixed_price_lower_bound_exact_logb_of_card_two_le
      values hvalues_nonneg hh_pos hmax hvalue_le_h hcard_ge_two

/--
Lemma 6.1: a uniform `k`-element subset has the paper's exact
without-replacement multiplicative lower-tail bound.

Source status: direct source statement.
-/
def lemma6_1_fixed_sizeSpec : Prop := by
  classical
  exact ∀ {α : Type*}
    {A B : Finset α} (_hBA : B ⊆ A) {k : ℕ}
    (_hk_pos : 0 < k) (_hk_lt : k < A.card)
    {δ : ℝ} (_hδ_pos : 0 < δ) (_hδ_le_one : δ ≤ 1),
    fixedSizeSampleProbability A k
        (fun sample =>
          (fixedSizeHitCount B sample : ℝ) <
            (1 - δ) * (B.card : ℝ) * (k : ℝ) / (A.card : ℝ)) <
      Real.exp
        (-((B.card : ℝ) * (k : ℝ) * δ ^ 2 /
          (2 * (A.card : ℝ))))

theorem lemma6_1_fixed_size : lemma6_1_fixed_sizeSpec := by
  classical
  intro α A B hBA k hk_pos hk_lt δ hδ_pos hδ_le_one
  exact lemma6_1_fixed_size_lower_tail
    hBA hk_pos hk_lt hδ_pos hδ_le_one

/-- Fair-coin specialization used internally by the Theorem 6.2 proof. -/
theorem lemma6_1_fair_coin
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (AppliedModelingLib.FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp (-(s.card : ℝ) / 36) := by
  exact paper_aux_theorem6_2_fair_coin_lower_tail_relaxed s keep

/-- Every realized directional random-sampling auction is dominant-strategy
truthful: sample reports determine only the opposite market's price, while a
market bidder cannot affect that price. -/
theorem theorem6_2_random_sampling_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    truthful (randomSamplingOptimalThresholdAuction side sampleSide minWinners) := by
  simpa [truthful] using
    randomSamplingOptimalThresholdAuction_truthful side sampleSide minWinners

/-- The directional random-sampling auction is individually rational for every
realized partition. -/
theorem theorem6_2_random_sampling_individually_rational
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).IndividuallyRational := by
  exact
    randomSamplingOptimalThresholdAuction_individuallyRational
      side sampleSide minWinners

/-- The directional random-sampling auction has no positive transfers for every
realized partition. -/
theorem theorem6_2_random_sampling_no_positive_transfers
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).NoPositiveTransfers := by
  exact
    randomSamplingOptimalThresholdAuction_noPositiveTransfers
      side sampleSide minWinners

/-- Every rejected bid in the directional auction is charged zero, so its
library total-payment revenue is the paper's winner-sale-price revenue. -/
theorem theorem6_2_random_sampling_losers_pay_zero
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).LosersPayZero := by
  exact DigitalGoodsAuction.losersPayZero_of_individuallyRational_noPositiveTransfers
    _ (theorem6_2_random_sampling_individually_rational side sampleSide minWinners)
    (theorem6_2_random_sampling_no_positive_transfers side sampleSide minWinners)

/--
Theorem 6.2: the source directional random-sampling auction revenue guarantee
on an exact uniform half-sample.

Source status: source theorem endpoint under visible model conventions.  The
population is explicitly `Fin (m + m)`, the sample is a uniform `m`-element
subset, the price is learned from the sampled side, and only the complementary
side is offered it.  Source `h` is represented by the visible attained-maximum
premise for `highValue`. The current `alpha : Nat` is not claimed as a silent
rounding of a real source parameter. The technical `[NeZero (m + m)]` carrier
instance is implied by the explicit `0 < m` premise.
-/
def theorem6_2_random_samplingSpec : Prop :=
  ∀ (m : ℕ) (_hm_pos : 0 < m),
    let _ : NeZero (m + m) := ⟨by omega⟩
    ∀
    (values : Fin (m + m) → ℝ) {alpha : ℕ} {highValue : ℝ}
    (_hhigh_pos : 0 < highValue)
    (_hvalue_bound : ∀ i, values i ≤ highValue)
    (_hhighest : ∃ i, values i = highValue)
    (_halpha_highValue :
      (alpha : ℝ) * highValue ≤ fixedPriceBenchmark values),
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw m (by
          rw [Fintype.card_fin]
          omega))
        (fun sample =>
          fixedPriceBenchmark values ≤
            6 *
              revenue
                (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true 1)
                values)

theorem theorem6_2_random_sampling : theorem6_2_random_samplingSpec := by
  intro m hm_pos
  letI : NeZero (m + m) := ⟨by omega⟩
  dsimp only
  intro values alpha highValue hhigh_pos hvalue_bound hhighest
    halpha_highValue
  have _hsource_attained : ∃ i, values i = highValue := hhighest
  have hsource_revenue :
      ∀ sample : FixedSizeSampleSpace (Fin (m + m)) m,
        revenue
            (randomSamplingOptimalThresholdAuction
              (sampledSideAssignment sample.1) true 1)
            values =
          (randomSamplingOptimalThresholdAuction
            (sampledSideAssignment sample.1) true 1).revenue values := by
    intro sample
    exact revenue_eq_totalPayments_of_losersPayZero _
      (randomSamplingOptimalThresholdAuction_binaryAllocation
        (sampledSideAssignment sample.1) true 1)
      values
      (theorem6_2_random_sampling_losers_pay_zero
        (sampledSideAssignment sample.1) true 1)
  have hevent :
      (fun sample : FixedSizeSampleSpace (Fin (m + m)) m =>
        fixedPriceBenchmark values ≤
          6 *
            revenue
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true 1)
              values) =
        (fun sample : FixedSizeSampleSpace (Fin (m + m)) m =>
          fixedPriceBenchmark values ≤
            6 *
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true 1).revenue values) := by
    funext sample
    rw [hsource_revenue sample]
  rw [hevent]
  change
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw m (by
          rw [Fintype.card_fin]
          omega))
        (fun sample =>
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true 1).revenue
                values)
  change
    (alpha : ℝ) * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1 at halpha_highValue
  exact
    theorem6_2_directional_fixed_half_revenue_bound_of_finite_candidate_benchmark_all_alpha
      values m hm_pos (by simp) hhigh_pos hvalue_bound halpha_highValue

/--
Independent fair-coin analysis counterpart for Theorem 6.2.

Source status: support only, not the literal theorem endpoint.  The source
uses independent `p = 1/2` sampling as a different analysis device after
stating the exact-half auction; no checked law or outcome comparison silently
identifies this support theorem with the exact-half mechanism above.
-/
theorem theorem6_2_random_sampling_fair_coin_support
    {n : ℕ} [NeZero n]
    (values : Fin n → ℝ) (keep : Bool) {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤ fixedPriceBenchmark values) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (AppliedModelingLib.FairCoin.productMeasure (Fin n)).real
        {side |
          fixedPriceBenchmark values ≤
            6 *
              revenue (randomSamplingOptimalThresholdAuction side keep 1) values} := by
  have hsource_revenue :
      ∀ side,
        revenue (randomSamplingOptimalThresholdAuction side keep 1) values =
          (randomSamplingOptimalThresholdAuction side keep 1).revenue values := by
    intro side
    exact revenue_eq_totalPayments_of_losersPayZero _
      (randomSamplingOptimalThresholdAuction_binaryAllocation side keep 1)
      values
      (theorem6_2_random_sampling_losers_pay_zero side keep 1)
  have hevent :
      {side |
        fixedPriceBenchmark values ≤
          6 * revenue (randomSamplingOptimalThresholdAuction side keep 1) values} =
        {side |
          fixedPriceBenchmark values ≤
            6 * (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
    ext side
    simp only [Set.mem_setOf_eq]
    rw [hsource_revenue side]
  rw [hevent]
  change
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (AppliedModelingLib.FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue
                values}
  change
    (alpha : ℝ) * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1 at halpha_highValue
  exact
    theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
      values keep hhigh_pos hvalue_bound halpha_highValue

/--
Technical rounded-dyadic certificate for Theorem 7.1.  The paper-facing
endpoint below removes the additive rounding term on the nondegenerate
`h >= 2` source domain.
-/
theorem theorem7_1_weighted_pairing_rounded_log_support
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {h total : ℝ}
    (htotal : total = totalValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hlarge : 4 * h ≤ total) :
    ∃ source : WeightedPairingSourceProfile values,
      total ≤ 192 * (Real.logb 2 h + 2) *
        weightedPairingSourceOperationalExpectedRevenue values source := by
  have htotal_bid : total = totalBidValue values := by
    simpa [totalValue, totalBidValue] using htotal
  have hh_lt_total : h < total := by
    nlinarith [hh_ge_one, hlarge]
  let source : WeightedPairingSourceProfile values :=
    weightedPairingSourceProfile_of_nonnegative_and_denominator_pos values
      (fun i => le_trans zero_le_one (hvalue_ge_one i))
      (paper_weighted_pairing_den_pos_of_high_value_bound
        values htotal_bid hvalue_le_h hh_lt_total)
  refine ⟨source, ?_⟩
  rw [GHW01DigitalGoods.weightedPairingRevenue_source_definition values source]
  simpa [totalValue, weightedPairingRevenue] using
    paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hlarge

/--
Theorem 7.1: if `4h <= T`, weighted pairing has the paper's logarithmic
guarantee.  The visible `2 <= h` premise is the finite nondegeneracy domain
for the source expression `T / log_2 h`; it turns the rounded dyadic
certificate into an explicit `Omega(T / log h)` bound. The source `h` is
explicitly required to occur as a highest bid.

Source status: approved corrected source target.
Source note: the visible `2 <= h` domain excludes the archival denominator-zero
case, so this theorem is not claimed as the literal archival endpoint.
-/
def theorem7_1_weighted_pairingSpec : Prop := by
  classical
  exact ∀ {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {h total : ℝ}
    (_htotal : total = totalValue values)
    (_hh_ge_two : 2 ≤ h)
    (_hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (_hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (_hhighest : ∃ i : Agent, values i = h)
    (_hlarge : 4 * h ≤ total),
    total ≤ 576 * Real.logb 2 h * weightedPairingRevenue values

theorem theorem7_1_weighted_pairing : theorem7_1_weighted_pairingSpec := by
  classical
  intro Agent _ values h total htotal hh_ge_two hvalue_ge_one hvalue_le_h
    hhighest hlarge
  letI : LinearOrder Agent :=
    LinearOrder.lift' (Fintype.equivFin Agent) (Fintype.equivFin Agent).injective
  letI : DecidableEq Agent := Classical.decEq Agent
  have _hsource_attained : ∃ i : Agent, values i = h := hhighest
  obtain ⟨source, hrounded⟩ :=
    theorem7_1_weighted_pairing_rounded_log_support values htotal
      (by linarith : 1 ≤ h) hvalue_ge_one hvalue_le_h hlarge
  rw [GHW01DigitalGoods.weightedPairingRevenue_source_definition values source] at hrounded
  have hh_pos : 0 < h := by linarith
  have hlog_ge_one : 1 ≤ Real.logb 2 h := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hh_pos]
    norm_num
    exact hh_ge_two
  have hrevenue_nonneg : 0 ≤ weightedPairingRevenue values := by
    simp only [weightedPairingRevenue]
    exact weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (source.positive_other_bid_mass i))
  have hcoefficient :
      192 * (Real.logb 2 h + 2) ≤ 576 * Real.logb 2 h := by
    nlinarith
  exact hrounded.trans (mul_le_mul_of_nonneg_right hcoefficient hrevenue_nonneg)

/--
Technical parameterized certificate for Theorem 7.2.  The paper-facing
square-root logarithmic endpoint below chooses its scale explicitly.
-/
theorem theorem7_2_weighted_pairing_benchmark_parameterized_support
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {h total s : ℝ}
    (htotal : total = totalValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hF_ge_two_h : 2 * h ≤ fixedPriceBenchmark values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : Real.logb 2 h + 2 ≤ s ^ 2) :
    ∃ source : WeightedPairingSourceProfile values,
      fixedPriceBenchmark values ≤ 576 * s *
        weightedPairingSourceOperationalExpectedRevenue values source := by
  change 2 * h ≤ finiteCandidateFixedPriceBenchmark values 1 at hF_ge_two_h
  have hF_ge_two_h_public : 2 * h ≤ fixedPriceBenchmark values := by
    simpa [fixedPriceBenchmark] using hF_ge_two_h
  have hvalue_nonneg : ∀ i : Agent, 0 ≤ values i :=
    fun i => le_trans zero_le_one (hvalue_ge_one i)
  have hfixed_eq :
      singlePriceRevenue values (optimalThreshold values) =
        fixedPriceBenchmark values :=
    (optimalThreshold_attains_fixedPriceBenchmark values hvalue_ge_one).2
  have hfixed_le_total_value : fixedPriceBenchmark values ≤ totalValue values := by
    rw [← hfixed_eq]
    simpa [totalValue, totalBidValue] using
      singlePriceRevenue_le_totalBidValue_of_nonneg values
        (optimalThreshold values) hvalue_nonneg
  have htotal_bid : total = totalBidValue values := by
    simpa [totalValue, totalBidValue] using htotal
  have hfixed_le_total : fixedPriceBenchmark values ≤ total := by
    rw [htotal]
    exact hfixed_le_total_value
  have hh_lt_total : h < total := by
    nlinarith [hF_ge_two_h_public, hfixed_le_total, hh_ge_one]
  let source : WeightedPairingSourceProfile values :=
    weightedPairingSourceProfile_of_nonnegative_and_denominator_pos values
      hvalue_nonneg
      (paper_weighted_pairing_den_pos_of_high_value_bound
        values htotal_bid hvalue_le_h hh_lt_total)
  have hbenchmark_eq :
      fixedPriceBenchmark values = twoWinnerBenchmark values := by
    simpa [fixedPriceBenchmark, twoWinnerBenchmark] using
      finiteCandidateFixedPriceBenchmark_one_eq_twoWinner
        values h hh_ge_one hvalue_le_h hF_ge_two_h
  have htwo_winner_large : 2 * h ≤ twoWinnerBenchmark values := by
    rw [← hbenchmark_eq]
    exact hF_ge_two_h
  have htwo_winner_bound :
      twoWinnerBenchmark values ≤ 576 * s * weightedPairingRevenue values := by
    simpa [totalValue, twoWinnerBenchmark, weightedPairingRevenue] using
    paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h htwo_winner_large
      hs_ge_two hlog_le_s_sq
  refine ⟨source, ?_⟩
  rw [GHW01DigitalGoods.weightedPairingRevenue_source_definition values source]
  rw [hbenchmark_eq]
  exact htwo_winner_bound

/--
The selected-scale finite certificate behind Theorem 7.2.  It is kept
separate because `log_2 h + 2` is meaningful even at the degenerate boundary
`h = 1`; the following endpoint recovers the source's `sqrt(log h)` form.
-/
theorem theorem7_2_weighted_pairing_benchmark_sqrt_log_plus_two
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {h total : ℝ}
    (htotal : total = totalValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hF_ge_two_h : 2 * h ≤ fixedPriceBenchmark values) :
    ∃ source : WeightedPairingSourceProfile values,
      fixedPriceBenchmark values ≤
        1152 * Real.sqrt (Real.logb 2 h + 2) *
          weightedPairingSourceOperationalExpectedRevenue values source := by
  let r : ℝ := Real.sqrt (Real.logb 2 h + 2)
  have hlog_nonneg : 0 ≤ Real.logb 2 h :=
    Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2) hh_ge_one
  have hradicand_nonneg : 0 ≤ Real.logb 2 h + 2 := by
    linarith
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = Real.logb 2 h + 2 := by
    dsimp [r]
    exact Real.sq_sqrt hradicand_nonneg
  have hr_ge_one : 1 ≤ r := by
    nlinarith
  have hs_ge_two : 2 ≤ r + 1 := by
    linarith
  have hlog_le_s_sq : Real.logb 2 h + 2 ≤ (r + 1) ^ 2 := by
    nlinarith
  obtain ⟨source, hparameterized⟩ :=
    theorem7_2_weighted_pairing_benchmark_parameterized_support values htotal
      hh_ge_one hvalue_ge_one hvalue_le_h hF_ge_two_h hs_ge_two hlog_le_s_sq
  have hoperational_nonneg :
      0 ≤ weightedPairingSourceOperationalExpectedRevenue values source := by
    rw [GHW01DigitalGoods.weightedPairingRevenue_source_definition values source]
    exact weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (source.positive_other_bid_mass i))
  have hr_plus_one_le : r + 1 ≤ 2 * r := by
    linarith
  have hcoefficient : 576 * (r + 1) ≤ 1152 * r := by
    nlinarith
  refine ⟨source, ?_⟩
  calc
    fixedPriceBenchmark values ≤
        576 * (r + 1) *
          weightedPairingSourceOperationalExpectedRevenue values source :=
      hparameterized
    _ ≤ 1152 * r *
          weightedPairingSourceOperationalExpectedRevenue values source :=
      mul_le_mul_of_nonneg_right hcoefficient hoperational_nonneg
    _ = 1152 * Real.sqrt (Real.logb 2 h + 2) *
          weightedPairingSourceOperationalExpectedRevenue values source := by
      simp [r]

/--
Theorem 7.2: if `F >= 2h`, weighted pairing has the source's square-root
logarithmic guarantee.  The explicit `2 <= h` premise is required because
the archival asymptotic denominator `sqrt(log_2 h)` vanishes at `h = 1`.
The source `h` is explicitly required to occur as a highest bid.

Source status: approved corrected source target.
Source note: the visible `2 <= h` domain excludes the archival denominator-zero
case, so this theorem is not claimed as the literal archival endpoint.
-/
def theorem7_2_weighted_pairing_benchmarkSpec : Prop := by
  classical
  exact ∀ {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {h total : ℝ}
    (_htotal : total = totalValue values)
    (_hh_ge_two : 2 ≤ h)
    (_hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (_hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (_hhighest : ∃ i : Agent, values i = h),
    let _ : Nonempty Agent := ⟨Classical.choose _hhighest⟩
    ∀ (_hF_ge_two_h : 2 * h ≤ fixedPriceBenchmark values),
    fixedPriceBenchmark values ≤
      2304 * Real.sqrt (Real.logb 2 h) * weightedPairingRevenue values

theorem theorem7_2_weighted_pairing_benchmark :
    theorem7_2_weighted_pairing_benchmarkSpec := by
  intro Agent _ values h total htotal hh_ge_two hvalue_ge_one hvalue_le_h
    hhighest
  classical
  letI : Nonempty Agent := ⟨Classical.choose hhighest⟩
  dsimp only
  intro hF_ge_two_h
  letI : LinearOrder Agent :=
    LinearOrder.lift' (Fintype.equivFin Agent) (Fintype.equivFin Agent).injective
  letI : DecidableEq Agent := Classical.decEq Agent
  have _hsource_attained : ∃ i : Agent, values i = h := hhighest
  obtain ⟨source, hplus_two⟩ :=
    theorem7_2_weighted_pairing_benchmark_sqrt_log_plus_two values htotal
      (by linarith : 1 ≤ h) hvalue_ge_one hvalue_le_h hF_ge_two_h
  rw [GHW01DigitalGoods.weightedPairingRevenue_source_definition values source] at hplus_two
  have hh_pos : 0 < h := by linarith
  have hlog_ge_one : 1 ≤ Real.logb 2 h := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hh_pos]
    norm_num
    exact hh_ge_two
  have hlog_nonneg : 0 ≤ Real.logb 2 h := by
    linarith
  have hradicand_bound :
      Real.logb 2 h + 2 ≤ 4 * Real.logb 2 h := by
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.logb 2 h) :=
    Real.sqrt_nonneg _
  have hsqrt_plus_nonneg :
      0 ≤ Real.sqrt (Real.logb 2 h + 2) :=
    Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (Real.logb 2 h)) ^ 2 = Real.logb 2 h :=
    Real.sq_sqrt hlog_nonneg
  have hsqrt_plus_sq :
      (Real.sqrt (Real.logb 2 h + 2)) ^ 2 = Real.logb 2 h + 2 :=
    Real.sq_sqrt (by linarith)
  have hsqrt_bound :
      Real.sqrt (Real.logb 2 h + 2) ≤
        2 * Real.sqrt (Real.logb 2 h) := by
    nlinarith
  have hrevenue_nonneg : 0 ≤ weightedPairingRevenue values := by
    simp only [weightedPairingRevenue]
    exact weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (source.positive_other_bid_mass i))
  have hcoefficient :
      1152 * Real.sqrt (Real.logb 2 h + 2) ≤
        2304 * Real.sqrt (Real.logb 2 h) := by
    nlinarith
  exact hplus_two.trans (mul_le_mul_of_nonneg_right hcoefficient hrevenue_nonneg)

/-- Every bid in the Theorem 7.2 tightness family is strictly positive. -/
theorem ghwTightValue_positive
    (k s : ℕ) (i : GhwTightAgent k s) :
    0 < ghwTightValue k s i := by
  rcases i with a | t
  · change 0 < (2 : ℝ) ^ (a.1.val + 1)
    positivity
  · change 0 < (2 : ℝ) ^ k
    positivity

/-- The repeated-bid tightness family satisfies the source weighted-pairing
probability domain.  Two top bidders provide a distinct positive-mass offer
for every bidder. -/
theorem ghwTightSourceProfile
    (k s : ℕ) (hs_two : 2 ≤ s) :
    WeightedPairingSourceProfile (ghwTightValue k s) := by
  apply weightedPairingSourceProfile_of_positive_and_distinct
  · exact ghwTightValue_positive k s
  · intro i
    by_cases hi : i = Sum.inr ⟨0, by omega⟩
    · subst i
      refine ⟨Sum.inr ⟨1, by omega⟩, ?_⟩
      simp
    · exact ⟨Sum.inr ⟨0, by omega⟩, Ne.symm hi⟩

/--
Theorem 7.2 tightness: the paper's repeated-bid family makes weighted pairing
earn at most `3 / s` times the fixed-price benchmark `F`.

The family has `s` top bids of value `2^k`; each lower level `r < k` has
`2^(k-r)` copies of value `2^r`.  Taking `s^2 + 2 ≤ k` gives the asymptotic
`O(1 / sqrt(log h))` upper-bound construction from the source proof.

This parameterized inequality is support for the source-facing selected-scale
tightness construction below.
-/
theorem theorem7_2_weighted_pairing_tightness_parameterized_support
    (k s : ℕ) (hs_two : 2 ≤ s) (hk_large : s * s + 2 ≤ k) :
    weightedPairingRevenue (ghwTightValue k s) ≤
      (3 / (s : ℝ)) * ghwTightFixedPriceBenchmarkValue k s hs_two := by
  have hs_pos : 0 < s := by omega
  letI : Nonempty (GhwTightAgent k s) := ⟨Sum.inr ⟨0, hs_pos⟩⟩
  have hratio :
      weightedPairingRevenue (ghwTightValue k s) ≤
        (3 / (s : ℝ)) * ghwTightTwoWinnerBenchmarkValue k s hs_two := by
    simpa [weightedPairingRevenue] using
    paper_theorem7_2_tightness_ratio_for_repeated_bid_family
      k s hs_two hk_large
  have htwo_le_one :
      ghwTightTwoWinnerBenchmarkValue k s hs_two ≤
        ghwTightFixedPriceBenchmarkValue k s hs_two := by
    unfold ghwTightTwoWinnerBenchmarkValue ghwTightFixedPriceBenchmarkValue
    change finiteCandidateFixedPriceBenchmark (ghwTightValue k s) 2 ≤
      finiteCandidateFixedPriceBenchmark (ghwTightValue k s) 1
    exact finiteCandidateFixedPriceBenchmark_two_le_one (ghwTightValue k s)
  have hfactor_nonneg : 0 ≤ 3 / (s : ℝ) := by positivity
  exact hratio.trans (mul_le_mul_of_nonneg_left htwo_le_one hfactor_nonneg)

/-- The repeated-bid construction in Theorem 7.2 has the source's operational
weighted-pairing revenue and its explicit `3 / s` ratio certificate. -/
theorem theorem7_2_weighted_pairing_tightness
    (k s : ℕ) (hs_two : 2 ≤ s) (hk_large : s * s + 2 ≤ k) :
    ∃ source : WeightedPairingSourceProfile (ghwTightValue k s),
      weightedPairingSourceOperationalExpectedRevenue (ghwTightValue k s) source ≤
        (3 / (s : ℝ)) * ghwTightFixedPriceBenchmarkValue k s hs_two := by
  let source : WeightedPairingSourceProfile (ghwTightValue k s) :=
    ghwTightSourceProfile k s hs_two
  refine ⟨source, ?_⟩
  rw [GHW01DigitalGoods.weightedPairingRevenue_source_definition
    (ghwTightValue k s) source]
  exact theorem7_2_weighted_pairing_tightness_parameterized_support
    k s hs_two hk_large

/-- For the selected hard family `k = s^2 + 2`, the explicit `3 / s`
certificate is at most `6 / sqrt(log_2(2^k))`. -/
theorem tightness_selected_scale_coefficient
    (s : ℕ) (hs_two : 2 ≤ s) :
    3 / (s : ℝ) ≤
      6 / Real.sqrt (Real.logb 2 ((2 : ℝ) ^ (s * s + 2))) := by
  have hs_pos : 0 < s := by omega
  have hsR_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos
  have hsR_ge_two : 2 ≤ (s : ℝ) := by exact_mod_cast hs_two
  have hkNat_pos : 0 < s * s + 2 := by omega
  have hkR_pos : 0 < ((s * s + 2 : ℕ) : ℝ) := by
    exact_mod_cast hkNat_pos
  have hkR_nonneg : 0 ≤ ((s * s + 2 : ℕ) : ℝ) := le_of_lt hkR_pos
  have hlog : Real.logb 2 ((2 : ℝ) ^ (s * s + 2)) =
      ((s * s + 2 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.logb_rpow (by norm_num) (by norm_num)
  rw [hlog]
  have hroot_nonneg : 0 ≤ Real.sqrt ((s * s + 2 : ℕ) : ℝ) :=
    Real.sqrt_nonneg _
  have hroot_sq : (Real.sqrt ((s * s + 2 : ℕ) : ℝ)) ^ 2 =
      ((s * s + 2 : ℕ) : ℝ) :=
    Real.sq_sqrt hkR_nonneg
  have hk_bound : ((s * s + 2 : ℕ) : ℝ) ≤ (2 * (s : ℝ)) ^ 2 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith [sq_nonneg (s : ℝ)]
  have hroot_le : Real.sqrt ((s * s + 2 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
    nlinarith
  have hroot_pos : 0 < Real.sqrt ((s * s + 2 : ℕ) : ℝ) := by
    nlinarith
  apply (div_le_div_iff₀ hsR_pos hroot_pos).mpr
  nlinarith

/-- A concrete unbounded source-faithful tightness family for Theorem 7.2.
For `k = s^2 + 2` it proves the source's
`O(F / sqrt(log h))` upper-ratio claim with an explicit constant.

Source status: direct source theorem endpoint.
-/
def theorem7_2_weighted_pairing_tightness_selected_sqrt_logSpec : Prop :=
  ∀ (s : ℕ) (hs_two : 2 ≤ s),
    weightedPairingRevenue (ghwTightValue (s * s + 2) s) ≤
      (6 / Real.sqrt
        (Real.logb 2 ((2 : ℝ) ^ (s * s + 2)))) *
        ghwTightFixedPriceBenchmarkValue (s * s + 2) s hs_two

theorem theorem7_2_weighted_pairing_tightness_selected_sqrt_log :
    theorem7_2_weighted_pairing_tightness_selected_sqrt_logSpec := by
  intro s hs_two
  have hbase :
      weightedPairingRevenue (ghwTightValue (s * s + 2) s) ≤
        (3 / (s : ℝ)) *
          ghwTightFixedPriceBenchmarkValue (s * s + 2) s hs_two := by
    exact theorem7_2_weighted_pairing_tightness_parameterized_support
      (s * s + 2) s hs_two (by omega)
  have hcoefficient := tightness_selected_scale_coefficient s hs_two
  have hbenchmark_nonneg :
      0 ≤ ghwTightFixedPriceBenchmarkValue (s * s + 2) s hs_two := by
    have hs_pos : 0 < s := by omega
    letI : Nonempty (GhwTightAgent (s * s + 2) s) :=
      ⟨Sum.inr ⟨0, hs_pos⟩⟩
    unfold ghwTightFixedPriceBenchmarkValue fixedPriceBenchmark
    exact finiteCandidateFixedPriceBenchmark_nonneg _ 1
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoefficient hbenchmark_nonneg)

/-- Valid support theorem: truthfulness implies monotone own-bid allocation
when the other reports are fixed. This is not the paper's cross-bidder
Lemma 8.1, whose SODA proof identifies two different report profiles. -/
theorem lemma8_1_own_bid_monotone_support
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hM : truthful M)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := by
  simpa [truthful, paper_digital_goods_truthful] using
    paper_lemma8_1_allocation_mono_own_bid_of_truthful M hM bids i hlt

/--
Corrected Lemma 8.1 endpoint. The SODA statement claims cross-bidder
monotonicity from truthfulness alone, but its proof substitutes one bidder's
outcome at the original profile for another bidder's outcome after a unilateral
report change. Ordinary set-of-bids anonymity does not justify that step.

The later journal formulation makes the required monotonicity condition
explicit: at every cutoff below the lower value, the lower bidder's offer CDF
is bounded by the higher bidder's offer CDF. Evaluating it at the lower value
and enlarging the higher bidder's acceptance event proves the advertised
cross-bidder probability comparison.

Source status: approved source-version correction, using the same pinned
journal monotone-offer condition as Theorem 8.2.
-/
def lemma8_1_truthful_monotoneSpec : Prop := by
  classical
  exact ∀ {Agent Price : Type*} [Fintype Price]
    (values : Agent → ℝ) (price : Price → ℝ) (offerLaw : Agent → PMF Price)
    (_hcdf_monotone :
      ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
        AppliedModelingLib.pmfProb (offerLaw i) (fun p => price p ≤ t) ≤
          AppliedModelingLib.pmfProb (offerLaw j) (fun p => price p ≤ t))
    (i j : Agent) (_hij : values i < values j),
    AppliedModelingLib.pmfProb (offerLaw i) (fun p => price p ≤ values i) ≤
      AppliedModelingLib.pmfProb (offerLaw j) (fun p => price p ≤ values j)

theorem lemma8_1_truthful_monotone : lemma8_1_truthful_monotoneSpec := by
  classical
  intro Agent Price _ values price offerLaw hcdf_monotone i j hij
  have hsame_cutoff :=
    hcdf_monotone i j (le_of_lt hij) (values i) le_rfl
  exact hsame_cutoff.trans
    (AppliedModelingLib.pmfProb_le_of_imp
      (offerLaw j)
      (fun p => price p ≤ values i)
      (fun p => price p ≤ values j)
      (fun _p hp => hp.trans (le_of_lt hij)))

/--
Theorem 8.2 source-version endpoint.

For Section 8.2, the paper-facing formalization follows the journal version's
refined monotone truthful randomized offer-auction wording. Every such auction
has expected revenue at most the fixed-price benchmark `F`.

This is the Theorem 8.2 endpoint used for the SODA paper. The preliminary
unrestricted wording is tracked separately as source-version audit material,
not as a paper-facing theorem.

Source status: approved corrected source target.
Source note: Formalized against the separately pinned later journal monotone
randomized-offer wording; it does not claim the preliminary SODA statement.
-/
def theorem8_2_truthful_revenue_upper_boundSpec : Prop := by
  classical
  exact
  ∀ {Agent Price : Type*} [Fintype Agent] [Nonempty Agent]
    [Fintype Price]
    (values : Agent → ℝ) (price : Price → ℝ) (offerLaw : Agent → PMF Price)
    (_hvalue_nonneg : ∀ i, 0 ≤ values i)
    (_hprice_nonneg : ∀ p, 0 ≤ price p)
    (_hcdf_monotone :
      ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
        AppliedModelingLib.pmfProb (offerLaw i) (fun p => price p ≤ t) ≤
          AppliedModelingLib.pmfProb (offerLaw j) (fun p => price p ≤ t)),
    paper_theorem8_2_raw_cdf_expected_revenue
        values price offerLaw ≤
      fixedPriceBenchmark values

theorem theorem8_2_truthful_revenue_upper_bound :
    theorem8_2_truthful_revenue_upper_boundSpec := by
  classical
  intro Agent Price _ _ _ values price offerLaw hvalue_nonneg hprice_nonneg
    hcdf_monotone
  letI : LinearOrder Agent :=
    LinearOrder.lift' (Fintype.equivFin Agent) (Fintype.equivFin Agent).injective
  letI : DecidableEq Agent := Classical.decEq Agent
  let model : PaperTheorem82JournalRawCDFMonotoneOfferSourceModel Agent Price :=
    { values := values
      price := price
      offerLaw := offerLaw
      value_nonneg := hvalue_nonneg
      price_nonneg := hprice_nonneg
      cdf_monotone := hcdf_monotone }
  change
    paper_theorem8_2_raw_cdf_expected_revenue
        model.values model.price model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_offer_source_model
      model

/--
Theorem 9.1: bid-independent auctions have an attained lower-bound witness.

For every positive source constant `alpha`, the binary witness contains at
least one bidder of value `highValue`.  Its benchmark is therefore compared by
the source's ordinary positive-denominator ratio `R / F <= 1 / highValue`.

Source status: source theorem endpoint.
Source note: the Section 5.1 source model permits the price rule to choose
`>=` or `>` separately for each erased bid multiset.  `rule` exposes that choice;
the proof reduces it pointwise to the weak comparison only on the binary
adversarial profiles, where an equality-only sale has nonnegative payment.
-/
def theorem9_1_bid_independent_lower_boundSpec : Prop :=
  ∀ (rule : PaperBidIndependentBoundaryRule) {highValue : ℕ} {alpha : ℝ}
    (_hhigh_ge_two : 2 ≤ highValue) (_halpha_pos : 0 < alpha),
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      twoValueBidIndependentBoundaryRevenue rule
          highValue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * alpha ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount

theorem theorem9_1_bid_independent_lower_bound :
    theorem9_1_bid_independent_lower_boundSpec := by
  intro rule highValue alpha hhigh_ge_two halpha_pos
  exact
    paper_theorem9_1_bid_independent_boundary_multiset_rule_real_alpha_ratio_witness_attained
      rule hhigh_ge_two halpha_pos

/--
Lemma 9.2: every deterministic truthful auction has a bid-independent
fixed-other-bids offer slice.

For each fixed profile of the other bids, either every report is rejected, or
all winning reports pay one critical price, reports below it lose, and reports
above it win.  The critical report itself may win or lose, matching the
source's open/closed boundary alternatives.

Source status: source lemma endpoint.
Source note: this is the full finite offer-slice form of the paper's
``truthful deterministic auctions are bid-independent'' conclusion.  The
global set-of-bids representation used in Theorem 9.3 is audited separately
as a source-model bridge.
-/
def lemma9_2_bid_independenceSpec : Prop := by
  classical
  exact ∀ {Agent : Type*}
    (M : DigitalGoodsAuction Agent)
    (_htruth : truthful M)
    (_hIR : M.IndividuallyRational)
    (_hNPT : M.NoPositiveTransfers)
    (_hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent),
    DeterministicOfferBidIndependent (deterministicAuctionOffer M bids i)

theorem lemma9_2_bid_independence : lemma9_2_bid_independenceSpec := by
  classical
  intro Agent M htruth hIR hNPT hbinary bids i
  simpa [truthful, paper_digital_goods_truthful] using
    AppliedModelingLib.Auction.paper_lemma9_2_deterministic_truthful_auction_bid_independent_slices
      M htruth hIR hNPT hbinary bids i

/--
Derived support for Lemma 9.2: the full bid-independent slice has a
nonnegative threshold that dominates every realized winning payment.

This is intentionally auxiliary rather than the source lemma endpoint: it
forgets the source conclusion that all reports above the critical price win.
-/
theorem lemma9_2_threshold_domination
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : truthful M)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    ∃ threshold,
      0 ≤ threshold ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer M bids i) threshold := by
  simpa [truthful, paper_digital_goods_truthful] using
    paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
      M htruth hIR hNPT hbinary bids i

/--
Theorem 9.3: deterministic truthful auctions have an attained lower-bound
witness for every positive source constant `alpha`.

The input is the paper's deterministic set-of-bids source model.  Its focused
outcome field is the Section 9.3 slice `g(x) = A_i(B_i^x)`.  The model carries
the set-of-bids-to-erased-multiset representation as an explicit source-model
premise; the theorem derives the internal erased-list relabeling needed by the
two-value lower-bound construction.

Source status: source theorem under documented source-model conventions.
Source note: the checked target makes the source's sale-price convention,
set-of-bids-to-erased-multiset representation bridge, and integer high-value
domain explicit.  It proves the displayed `1 / H` witness on that target; it
also records that `H` occurs in the binary input, and does not claim the
unrestricted archival quantification verbatim.
-/
def theorem9_3_deterministic_truthful_lower_boundSpec : Prop :=
  ∀ {highValue : ℕ} {alpha : ℝ}
    (model : assumption_theorem9_3_primitive_set_of_bids_deterministic_source_model highValue)
    (_hhigh_ge_two : 2 ≤ highValue) (_halpha_pos : 0 < alpha),
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      revenue (model.auctionFamily highCount lowCount)
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * alpha ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount

theorem theorem9_3_deterministic_truthful_lower_bound :
    theorem9_3_deterministic_truthful_lower_boundSpec := by
  intro highValue alpha model hhigh_ge_two halpha_pos
  have hsource_revenue :
      ∀ highCount lowCount,
        revenue (model.auctionFamily highCount lowCount)
            (twoValueBidProfile highValue highCount lowCount) =
          (model.auctionFamily highCount lowCount).revenue
            (twoValueBidProfile highValue highCount lowCount) := by
    intro highCount lowCount
    exact revenue_eq_totalPayments_of_losersPayZero _
      (model.binary highCount lowCount) _
      (DigitalGoodsAuction.losersPayZero_of_individuallyRational_noPositiveTransfers
        _ (model.individuallyRational highCount lowCount)
        (model.noPositiveTransfers highCount lowCount))
  let alphaNat : ℕ := Nat.ceil alpha
  have halphaNat_pos : 0 < alphaNat := by
    simpa [alphaNat] using (Nat.ceil_pos.mpr halpha_pos)
  obtain ⟨highCount, lowCount, hattained, hratio, hscale⟩ :=
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_set_of_bids_source_model_attained
      model hhigh_ge_two halphaNat_pos
  refine ⟨highCount, lowCount, hattained, ?_, ?_⟩
  · rw [hsource_revenue highCount lowCount]
    exact hratio
  have halpha_le : alpha ≤ (alphaNat : ℝ) := by
    simpa [alphaNat] using Nat.le_ceil alpha
  exact le_trans
    (mul_le_mul_of_nonneg_left halpha_le (by positivity)) hscale

/-! ## Section 11 Deep-Audit Support -/

/--
Bounded-supply Theorem 4.1: `F_k` controls the top-`k` multi-price value.

Source status: deep-audit support only. This unnumbered source prose is not a
normal named-theory result. The Lean theorem records the exact corrected-domain
component without claiming the literal prose endpoint.
-/
theorem section11_bounded_fixed_price_lower_bound
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) {h : ℝ}
    (hh_ge_two : 2 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    boundedTopKValue values capacity ≤
      (2 * Real.logb 2 h) * boundedBenchmark values capacity := by
  exact boundedSupplyFixedPriceBenchmark_ge_topK_exact_logb_of_two_le
    values capacity hh_ge_two hvalue_ge_one hvalue_le_h

/-- The bounded single-price mechanism uses `opt_{m k/(n-m)}` on the sample
and a fixed-priority cap of `k` on the market side. -/
def section11_singlePriceSamplingAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) : DigitalGoodsAuction Agent :=
  boundedSinglePriceSamplingAuction side sampleSide
    sampleSize marketSize capacity

theorem section11_singlePriceSampling_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) :
    truthful (section11_singlePriceSamplingAuction side sampleSide
      sampleSize marketSize capacity) := by
  exact boundedSinglePriceSamplingAuction_truthful side sampleSide
    sampleSize marketSize capacity

theorem section11_singlePriceSampling_supply_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) (values : Agent → ℝ) :
    boundedCappedAllocationCount side (!sampleSide)
        (boundedSamplingPriceRule side sampleSide
          (scaledSampleCapacity sampleSize marketSize capacity)) capacity values ≤
      capacity := by
  exact boundedSinglePriceSamplingAuction_supply_feasible side sampleSide
    sampleSize marketSize capacity values

/-- Exact high-probability estimate used to show that priority capping rejects
only a small number of buyers on balanced fixed-size samples. -/
theorem section11_small_rejection_probability
    {Agent : Type*} [DecidableEq Agent]
    {all eligible : Finset Agent} (heligible : eligible ⊆ all)
    {sampleSize : ℕ} (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < all.card)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    fixedSizeSampleProbability all sampleSize
        (fun sample =>
          (fixedSizeHitCount eligible sample : ℝ) <
            (1 - delta) * (eligible.card : ℝ) *
              (sampleSize : ℝ) / (all.card : ℝ)) <
      Real.exp (-((eligible.card : ℝ) * (sampleSize : ℝ) * delta ^ 2 /
        (2 * (all.card : ℝ)))) := by
  exact boundedSampling_underrepresentation_probability heligible
    hsample_pos hsample_lt hdelta_pos hdelta_le_one

/--
Combined probability form of Section 11's qualitative small-rejection claim.
The source leaves the success probability unspecified, so the theorem accepts
an explicit lower bound for the market-count slack event and transfers it to
the actual number of bidders rejected by the capacity cap under the uniform
fixed-size sampling law.

Source status: deep-audit transfer lemma only. It does not derive the source
claim's success event or probability from the advertised bounded-supply regime.
-/
theorem section11_small_rejection_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize capacity slack : ℕ) (values : Agent → ℝ)
    (hsample_lt : sampleSize < Fintype.card Agent)
    {successProbability : ℝ}
    (hsuccess : 0 < successProbability)
    (hsuccess_le_one : successProbability ≤ 1)
    (hcount_probability :
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
        (fun sample =>
          sideSaleCount (sampledSideAssignment sample.1) false values
              (boundedSamplingPriceRule
                (sampledSideAssignment sample.1) true
                (scaledSampleCapacity sampleSize
                  (Fintype.card Agent - sampleSize) capacity) values) ≤
            capacity + slack)) :
    successProbability ≤ pmfEventProbability
      (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
      (fun sample =>
        boundedRejectionCount
            (sideSaleCount (sampledSideAssignment sample.1) false values
              (boundedSamplingPriceRule
                (sampledSideAssignment sample.1) true
                (scaledSampleCapacity sampleSize
                  (Fintype.card Agent - sampleSize) capacity) values))
            capacity ≤ slack) := by
  exact boundedSinglePriceSampling_small_rejection_combined_guarantee
    sampleSize capacity slack values hsample_lt hsuccess hsuccess_le_one
    hcount_probability

/-- On the simultaneous benchmark-capture and count-balance event, the
bounded single-price sampler is multiplicatively competitive with `F_k`. -/
theorem section11_singlePriceSampling_competitive
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) (values : Agent → ℝ)
    {beta gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hsample :
      beta * boundedBenchmark values capacity ≤
        (min (scaledSampleCapacity sampleSize marketSize capacity)
          (sideSaleCount side sampleSide values
            (boundedSamplingPriceRule side sampleSide
              (scaledSampleCapacity sampleSize marketSize capacity) values)) : ℝ) *
          boundedSamplingPriceRule side sampleSide
            (scaledSampleCapacity sampleSize marketSize capacity) values)
    (hbalance :
      gamma *
          (min (scaledSampleCapacity sampleSize marketSize capacity)
            (sideSaleCount side sampleSide values
              (boundedSamplingPriceRule side sampleSide
                (scaledSampleCapacity sampleSize marketSize capacity) values)) : ℝ) ≤
        (min capacity
          (sideSaleCount side (!sampleSide) values
            (boundedSamplingPriceRule side sampleSide
              (scaledSampleCapacity sampleSize marketSize capacity) values)) : ℝ)) :
    gamma * beta * boundedBenchmark values capacity ≤
      boundedSinglePriceSamplingRevenue side sampleSide
        sampleSize marketSize capacity values := by
  exact boundedSinglePriceSampling_competitive_on_balanced_sample
    side sampleSide sampleSize marketSize capacity values hgamma hsample hbalance

/--
Section 11's combined qualitative single-price guarantee.  Because the source
does not specify a numerical competitive constant or success probability,
`beta`, `gamma`, and `successProbability` are quantified explicitly under the
uniform fixed-`sampleSize` law.  Any proved probability lower bound for the
displayed benchmark-capture/balance event transfers to the competitive-revenue
event, and every realized auction is truthful and respects the `capacity` cap.

Source status: deep-audit transfer lemma only. It does not derive the source
claim's good-event probability or competitive constants from the advertised
bounded-supply regime.
-/
theorem section11_singlePriceSampling_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize capacity : ℕ) (values : Agent → ℝ)
    (hsample_lt : sampleSize < Fintype.card Agent)
    {beta gamma successProbability : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsuccess : 0 < successProbability)
    (hsuccess_le_one : successProbability ≤ 1)
    (hgood_probability :
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
        (fun sample => boundedSinglePriceSamplingGoodEvent sample.1
          sampleSize (Fintype.card Agent - sampleSize) capacity
          values beta gamma)) :
    (∀ sample : FixedSizeSampleSpace Agent sampleSize,
        truthful
          (section11_singlePriceSamplingAuction
            (sampledSideAssignment sample.1) true sampleSize
            (Fintype.card Agent - sampleSize) capacity)) ∧
      (∀ sample : FixedSizeSampleSpace Agent sampleSize,
        boundedCappedAllocationCount
            (sampledSideAssignment sample.1) false
            (boundedSamplingPriceRule (sampledSideAssignment sample.1) true
              (scaledSampleCapacity sampleSize
                (Fintype.card Agent - sampleSize) capacity))
            capacity values ≤ capacity) ∧
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
        (fun sample => boundedSinglePriceSamplingCompetitiveEvent sample.1
          sampleSize (Fintype.card Agent - sampleSize) capacity
          values beta gamma) := by
  simpa [truthful, section11_singlePriceSamplingAuction] using
    boundedSinglePriceSampling_fixedSize_combined_guarantee
      sampleSize capacity values hsample_lt hbeta hgamma hsuccess
      hsuccess_le_one hgood_probability

/-- With half-sampling, each side uses the other side's `opt_{k/2}` and is
independently capped at `k/2`. -/
def section11_dualPriceSamplingAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) : DigitalGoodsAuction Agent :=
  boundedDualPriceSamplingAuction side capacity

theorem section11_dualPriceSampling_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) :
    truthful (section11_dualPriceSamplingAuction side capacity) := by
  exact boundedDualPriceSamplingAuction_truthful side capacity

theorem section11_dualPriceSampling_supply_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) (values : Agent → ℝ) :
    boundedDualAllocationCount side capacity values ≤ capacity := by
  exact boundedDualPriceSamplingAuction_supply_feasible side capacity values

theorem section11_dualPriceSampling_competitive
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (capacity : ℕ) (values : Agent → ℝ)
    {target gamma sampleRevenueFalse sampleRevenueTrue : ℝ}
    (hgamma : 0 ≤ gamma)
    (htarget : target ≤ sampleRevenueFalse + sampleRevenueTrue)
    (hfalse : gamma * sampleRevenueFalse ≤
      boundedSidePriceRevenue side false values (capacity / 2)
        (boundedSamplingPriceRule side true (capacity / 2) values))
    (htrue : gamma * sampleRevenueTrue ≤
      boundedSidePriceRevenue side true values (capacity / 2)
        (boundedSamplingPriceRule side false (capacity / 2) values)) :
    gamma * target ≤ boundedDualPriceSamplingRevenue side capacity values := by
  exact boundedDualPriceSampling_competitive_on_balanced_halves
    side capacity values hgamma htarget hfalse htrue

/--
Section 11's combined qualitative dual-price guarantee.  The omitted source
constant and success probability remain explicit parameters under the uniform
half-sample law: a probability lower bound for the displayed two-sided
capture/balance event transfers to the competitive-revenue event, while
truthfulness and total supply feasibility hold for every realized split.

Source status: deep-audit transfer lemma only. It does not derive the source
claim's good-event probability or competitive constants from the advertised
bounded-supply regime.
-/
theorem section11_dualPriceSampling_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (capacity : ℕ) (values : Agent → ℝ)
    {beta gamma successProbability : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsuccess : 0 < successProbability)
    (hsuccess_le_one : successProbability ≤ 1)
    (hgood_probability :
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw (Fintype.card Agent / 2)
          (Nat.div_le_self _ _))
        (fun sample => boundedDualPriceSamplingGoodEvent sample.1
          capacity values beta gamma)) :
    (∀ sample : FixedSizeSampleSpace Agent (Fintype.card Agent / 2),
        truthful
          (section11_dualPriceSamplingAuction
            (sampledSideAssignment sample.1) capacity)) ∧
      (∀ sample : FixedSizeSampleSpace Agent (Fintype.card Agent / 2),
        boundedDualAllocationCount
            (sampledSideAssignment sample.1) capacity values ≤ capacity) ∧
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw (Fintype.card Agent / 2)
          (Nat.div_le_self _ _))
        (fun sample => boundedDualPriceSamplingCompetitiveEvent sample.1
          capacity values beta gamma) := by
  simpa [truthful, section11_dualPriceSamplingAuction] using
    boundedDualPriceSampling_fixedHalf_combined_guarantee
      capacity values hbeta hgamma hsuccess hsuccess_le_one
      hgood_probability

/-- The deterministic optimal-threshold mechanism extends by replacing `opt`
with `opt_k` on each own-erased profile and rejecting exact threshold ties. -/
def section11_deterministicOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) : DigitalGoodsAuction Agent :=
  boundedDeterministicOptimalThresholdAuction capacity

theorem section11_deterministicOptimalThreshold_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) :
    truthful (section11_deterministicOptimalThresholdAuction
      (Agent := Agent) capacity) := by
  exact boundedDeterministicOptimalThresholdAuction_truthful capacity

theorem section11_deterministicOptimalThreshold_supply_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) (values : Agent → ℝ) :
    boundedDeterministicOptimalThresholdAllocationCount capacity values ≤
      capacity := by
  exact boundedDeterministicOptimalThresholdAuction_supply_feasible
    capacity values

/--
Unlimited supply is the `k=n` slice, so every unlimited-supply upper bound is
also a bounded-supply upper bound.

Source status: deep-audit support only; this is unnumbered source prose rather
than a normal named-theory endpoint.
-/
theorem section11_unlimited_upper_bounds_transport
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {bound : ℝ}
    (hunlimited : M.revenue values ≤ bound * fixedPriceBenchmark values) :
    M.revenue values ≤
      bound * boundedBenchmark values (Fintype.card Agent) := by
  exact unlimitedUpperBound_transports_to_boundedSupply M values hunlimited

end

end GHW01DigitalGoods.ProofBridge
