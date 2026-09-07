import AppliedModelingLib.MechanismDesign.Auctions.DigitalGoods
import Mathlib.Data.Multiset.Sort
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Source Definitions for GHW01 Digital-Goods Auctions

This module records the paper's core source vocabulary independently of the
proof-oriented auction encodings.  The archival line references are to
`GHW01DigitalGoods.txt`.  In particular, an outcome here is literally a finite
set of winners with associated sale prices, and a randomized auction is
literally a probability distribution over such outcomes.
-/

namespace GHW01DigitalGoods
namespace SourceDefinitions

open AppliedModelingLib.Auction
open scoped BigOperators ENNReal

noncomputable section

/-! ## Bidders, bids, and outcomes -/

/-- A bidder's utility values, indexed by the bidders.

Source: lines 195-196.
-/
abbrev BidValues (Agent : Type*) := Agent → ℝ

/-- A sealed-bid report profile.

Source: lines 108 and 195-196.
-/
abbrev BidProfile (Agent : Type*) := Agent → ℝ

/-- The source distinguishes true utility values from submitted bids.

Source: lines 195-196.
-/
structure AuctionInput (Agent : Type*) where
  values : BidValues Agent
  bids : BidProfile Agent

/-- The source convention used when analyzing truthful auctions: `b_i = u_i`.

Source: lines 215-227.
-/
def TruthfulReports {Agent : Type*} (input : AuctionInput Agent) : Prop :=
  input.bids = input.values

/-- The paper's ascending-index presentation of ordered bids.  This is a
presentation convention rather than a restriction on unordered profiles.

Source: lines 195-199.
-/
def SortedBids {n : ℕ} (bids : BidProfile (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → bids i ≤ bids j

/-- An auction outcome is a finite set of satisfied bids and one sale price
for each bidder.  Prices of losing bidders are semantically irrelevant.

Source: lines 200-203.
-/
structure AuctionOutcome (Agent : Type*) where
  winners : Finset Agent
  salePrice : Agent → ℝ

namespace AuctionOutcome

/-- Every winning bid is filled at or below its submitted value.

Source: lines 200-203.
-/
def FillsAtOrBelow {Agent : Type*} (outcome : AuctionOutcome Agent)
    (bids : BidProfile Agent) : Prop :=
  ∀ i, i ∈ outcome.winners → outcome.salePrice i ≤ bids i

/-- A bidder's profit is value minus price upon winning and zero upon losing.

Source: lines 215-220.
-/
def profit {Agent : Type*} [DecidableEq Agent]
    (outcome : AuctionOutcome Agent) (values : BidValues Agent)
    (i : Agent) : ℝ :=
  if i ∈ outcome.winners then values i - outcome.salePrice i else 0

/-- Auction revenue is the sum of all winning sale prices.

Source: lines 210-214.
-/
def revenue {Agent : Type*} (outcome : AuctionOutcome Agent) : ℝ :=
  ∑ i ∈ outcome.winners, outcome.salePrice i

/-- A single-price outcome charges one common price to every winner.

Source: lines 67-69.
-/
def IsSinglePrice {Agent : Type*} (outcome : AuctionOutcome Agent) : Prop :=
  ∃ p : ℝ, ∀ i, i ∈ outcome.winners → outcome.salePrice i = p

/-- A genuinely different-price outcome has two winners charged unequal
prices.  General `AuctionOutcome`s permit this but do not require it.

Source: lines 67-69.
-/
def UsesDifferentPrices {Agent : Type*} (outcome : AuctionOutcome Agent) : Prop :=
  ∃ i, i ∈ outcome.winners ∧
    ∃ j, j ∈ outcome.winners ∧ outcome.salePrice i ≠ outcome.salePrice j

end AuctionOutcome

/-! ## Deterministic and randomized auction mechanisms -/

/-- A deterministic mechanism maps every bid profile to an auction outcome.

Source: lines 203-204.
-/
abbrev DeterministicAuction (Agent : Type*) :=
  BidProfile Agent → AuctionOutcome Agent

/-- A randomized mechanism maps every bid profile to a probability
distribution on auction outcomes.

Source: lines 203-210.
-/
abbrev RandomizedAuction (Agent : Type*) :=
  BidProfile Agent → PMF (AuctionOutcome Agent)

/-- `R` for a deterministic mechanism and bid profile.

Source: lines 210-214.
-/
def deterministicRevenue {Agent : Type*}
    (auction : DeterministicAuction Agent) (bids : BidProfile Agent) : ℝ :=
  (auction bids).revenue

/-- For a randomized auction, `R` is the random variable obtained by mapping
the outcome distribution through outcome revenue.

Source: lines 210-214.
-/
def randomizedRevenueLaw {Agent : Type*}
    (auction : RandomizedAuction Agent) (bids : BidProfile Agent) : PMF ℝ :=
  PMF.map AuctionOutcome.revenue (auction bids)

/-- A deterministic auction is single-price when every realized outcome is
single-price.

Source: lines 67-69.
-/
def DeterministicIsSinglePrice {Agent : Type*}
    (auction : DeterministicAuction Agent) : Prop :=
  ∀ bids, (auction bids).IsSinglePrice

/-- A randomized auction is single-price when every positive-probability
realized outcome is single-price.

Source: lines 67-70.
-/
def RandomizedIsSinglePrice {Agent : Type*}
    (auction : RandomizedAuction Agent) : Prop :=
  ∀ bids outcome, auction bids outcome ≠ 0 → outcome.IsSinglePrice

/-- A deterministic multi-price auction actually realizes unequal prices on
at least one bid profile.  General deterministic auctions permit such prices;
single-price auctions are the restricted subclass above.

Source: lines 67-69.
-/
def DeterministicUsesMultiplePrices {Agent : Type*}
    (auction : DeterministicAuction Agent) : Prop :=
  ∃ bids, (auction bids).UsesDifferentPrices

/-- A randomized multi-price auction realizes an unequal-price outcome with
positive probability on at least one bid profile.

Source: lines 67-70.
-/
def RandomizedUsesMultiplePrices {Agent : Type*}
    (auction : RandomizedAuction Agent) : Prop :=
  ∃ bids outcome, auction bids outcome ≠ 0 ∧ outcome.UsesDifferentPrices

/-- The expected profit induced by a distribution over outcomes.  The source's
randomized algorithms have finite random support; `tsum` also states the
distribution-on-outcomes definition without choosing a seed representation.

Source: lines 203-220.
-/
def randomizedExpectedProfit {Agent : Type*} [DecidableEq Agent]
    (auction : RandomizedAuction Agent) (values : BidValues Agent)
    (i : Agent) (bids : BidProfile Agent) : ℝ :=
  ∑' outcome : AuctionOutcome Agent,
    (auction bids outcome).toReal * outcome.profit values i

/-- Existence of all expected profits compared by randomized truthfulness.
This makes the finiteness presupposed by the source phrase "expected profit"
explicit instead of relying on Lean's totalized value for a nonsummable
series.

Source: lines 219-221.
-/
def HasFiniteExpectedProfits {Agent : Type*} [DecidableEq Agent]
    (auction : RandomizedAuction Agent) : Prop :=
  ∀ (values : BidValues Agent) (i : Agent) (bids : BidProfile Agent),
    Summable fun outcome : AuctionOutcome Agent =>
      (auction bids outcome).toReal * outcome.profit values i

/-- Truthful bidding weakly maximizes deterministic profit, holding all other
bids fixed.

Source: lines 215-226.
-/
def DeterministicTruthful {Agent : Type*} [DecidableEq Agent]
    (auction : DeterministicAuction Agent) : Prop :=
  ∀ (values : BidValues Agent) (i : Agent) (report : ℝ),
    (auction (Function.update values i report)).profit values i ≤
      (auction values).profit values i

/-- Truthful bidding weakly maximizes expected profit in a randomized auction,
holding all other bids fixed.

Source: lines 215-226.
-/
def RandomizedTruthful {Agent : Type*} [DecidableEq Agent]
    (auction : RandomizedAuction Agent) : Prop :=
  HasFiniteExpectedProfits auction ∧
    ∀ (values : BidValues Agent) (i : Agent) (report : ℝ),
      randomizedExpectedProfit auction values i
          (Function.update values i report) ≤
        randomizedExpectedProfit auction values i values

/-- Source correctness for deterministic auctions: truthfulness together with
filling each winning bid at or below its report.

Source: lines 79-83 and 200-226.
-/
def DeterministicCorrect {Agent : Type*} [DecidableEq Agent]
    (auction : DeterministicAuction Agent) : Prop :=
  DeterministicTruthful auction ∧
    ∀ bids, (auction bids).FillsAtOrBelow bids

/-- Source correctness for randomized auctions: expected-profit truthfulness
and feasibility of every positive-probability outcome.

Source: lines 79-83 and 200-226.
-/
def RandomizedCorrect {Agent : Type*} [DecidableEq Agent]
    (auction : RandomizedAuction Agent) : Prop :=
  RandomizedTruthful auction ∧
    ∀ bids outcome, auction bids outcome ≠ 0 →
      outcome.FillsAtOrBelow bids

/-- In the unlimited-supply model there is no cardinality constraint on the
winner set: every bidder can receive one identical item.

Source: lines 89-96.
-/
abbrev UnlimitedSupplyDeterministicAuction (Agent : Type*) :=
  DeterministicAuction Agent

/-- Randomized version of the unlimited-supply mechanism model.

Source: lines 89-96.
-/
abbrev UnlimitedSupplyRandomizedAuction (Agent : Type*) :=
  RandomizedAuction Agent

/-! ## Fixed prices and the paper's analysis quantities -/

/-- Fixed pricing satisfies exactly the bids weakly above `p` and charges
every satisfied bid `p`.

Source: lines 97-102.
-/
def fixedPriceOutcome {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) (p : ℝ) : AuctionOutcome Agent where
  winners := (Finset.univ : Finset Agent).filter fun i => p ≤ bids i
  salePrice := fun _ => p

/-- The fixed-pricing mechanism at a price chosen before seeing the bids.

Source: lines 97-102.
-/
def fixedPriceAuction {Agent : Type*} [Fintype Agent]
    (p : ℝ) : DeterministicAuction Agent :=
  fun bids => fixedPriceOutcome bids p

/-- A fixed-price outcome is source-feasible at its submitted profile.

Source: lines 97-102.
-/
theorem fixedPriceOutcome_fillsAtOrBelow {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) (p : ℝ) :
    (fixedPriceOutcome bids p).FillsAtOrBelow bids := by
  classical
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- A fixed-price outcome is single-price by construction.

Source: lines 67-69 and 97-102.
-/
theorem fixedPriceOutcome_isSinglePrice {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) (p : ℝ) :
    (fixedPriceOutcome bids p).IsSinglePrice := by
  exact ⟨p, by simp [fixedPriceOutcome]⟩

/-- Fixed-price revenue, reusing the library's exact sum over accepting bids.

Source: lines 97-102 and 228-234.
-/
abbrev fixedPriceRevenue {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) (p : ℝ) : ℝ :=
  AppliedModelingLib.Auction.singlePriceRevenue bids p

/-- Outcome revenue agrees with the reusable fixed-price revenue definition.

Source: lines 97-102 and 210-214.
-/
theorem fixedPriceOutcome_revenue {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) (p : ℝ) :
    (fixedPriceOutcome bids p).revenue = fixedPriceRevenue bids p := by
  classical
  change (fixedPriceOutcome bids p).revenue =
    AppliedModelingLib.Auction.singlePriceRevenue bids p
  rw [AppliedModelingLib.Auction.singlePriceRevenue_eq_saleCount_mul]
  simp [AuctionOutcome.revenue, fixedPriceOutcome,
    AppliedModelingLib.Auction.saleCount]

/-- `F`: the maximum fixed-price revenue over prices equal to an input bid.
The source's normalized nonempty bid domain makes this finite candidate set
exactly sufficient.

Source: lines 128-148, 228-234, and 317-337.
-/
def optimalFixedPriceRevenue {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    (fun i => fixedPriceRevenue bids (bids i))

/-- `p` is an optimal threshold exactly when it is an input bid attaining `F`.
This relational form leaves the source's unspecified tie-breaking visible.

Source: lines 317-337.
-/
def IsOptimalThreshold {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) (p : ℝ) : Prop :=
  (∃ i, p = bids i) ∧
    fixedPriceRevenue bids p = optimalFixedPriceRevenue bids

private theorem exists_optimalThreshold
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : ∃ p, IsOptimalThreshold bids p := by
  classical
  let H : (Finset.univ : Finset Agent).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
    exact ⟨i, by simp⟩
  obtain ⟨i, _hi, hmax⟩ :=
    (Finset.univ : Finset Agent).exists_mem_eq_sup'
      (f := fun i => fixedPriceRevenue bids (bids i)) H
  exact ⟨bids i, ⟨⟨i, rfl⟩, hmax.symm⟩⟩

/-- The input-bid prices attaining `F`.  This value-level candidate set makes
the tie rule independent of bidder names and of any presentation ordering.

Source: lines 317-337.
-/
def optimalThresholdCandidates
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : Finset ℝ := by
  classical
  exact ((Finset.univ : Finset Agent).image bids).filter fun p =>
    fixedPriceRevenue bids p = optimalFixedPriceRevenue bids

private theorem optimalThresholdCandidates_nonempty
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : (optimalThresholdCandidates bids).Nonempty := by
  classical
  obtain ⟨p, ⟨⟨i, hpi⟩, hrevenue⟩⟩ := exists_optimalThreshold bids
  refine ⟨p, Finset.mem_filter.mpr ⟨?_, hrevenue⟩⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hpi.symm⟩

/-- The source threshold `opt(B)`, with ties resolved by the largest
revenue-maximizing bid value.  The source leaves ties open; choosing on values
rather than bidder indices makes this a canonical function of the bid multiset.

Source: lines 317-337.
-/
def optimalThreshold {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : ℝ :=
  (optimalThresholdCandidates bids).max'
    (optimalThresholdCandidates_nonempty bids)

/-- The selected `opt(B)` is an input bid and attains `F`.

Source: lines 317-337.
-/
theorem optimalThreshold_spec {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : IsOptimalThreshold bids (optimalThreshold bids) := by
  classical
  have hmem : optimalThreshold bids ∈ optimalThresholdCandidates bids := by
    exact Finset.max'_mem _ (optimalThresholdCandidates_nonempty bids)
  rw [optimalThresholdCandidates, Finset.mem_filter] at hmem
  rcases hmem with ⟨hprice, hrevenue⟩
  rcases Finset.mem_image.mp hprice with ⟨i, _hi, hvalue⟩
  exact ⟨⟨i, hvalue.symm⟩, hrevenue⟩

/-- The optimal single-price auction satisfies all bids at least `opt(B)` at
that price and rejects all other bids.

Source: lines 317-322.
-/
def optimalSinglePriceOutcome {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : AuctionOutcome Agent :=
  fixedPriceOutcome bids (optimalThreshold bids)

/-- The source's optimal single-price (untruthful) mechanism.

Source: lines 313-322.
-/
def optimalSinglePriceAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] :
    DeterministicAuction Agent :=
  optimalSinglePriceOutcome

/-- `n`, the number of bidders.

Source: lines 128-130 and 195-196.
-/
abbrev bidderCount (Agent : Type*) [Fintype Agent] : ℕ :=
  Fintype.card Agent

/-- `T`, the sum of all bids, equivalently optimal multi-price revenue under
truthful reports.

Source: lines 128-134 and 228-232.
-/
def totalBidValue {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) : ℝ :=
  ∑ i : Agent, bids i

/-- The untruthful multi-price outcome that satisfies every bid at its own
reported value.

Source: lines 228-232.
-/
def fullValueOutcome {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) : AuctionOutcome Agent where
  winners := Finset.univ
  salePrice := bids

/-- `T` is exactly the revenue of the full-value multi-price outcome.

Source: lines 228-232.
-/
theorem fullValueOutcome_revenue {Agent : Type*} [Fintype Agent]
    (bids : BidProfile Agent) :
    (fullValueOutcome bids).revenue = totalBidValue bids := by
  simp [AuctionOutcome.revenue, fullValueOutcome, totalBidValue]

/-- Under the source's truthful-report convention, the sum of utility values,
the bid-defined total value `T`, and the revenue of the full-value multi-price
outcome are the same quantity.  The truthful-report premise is used only to
identify utilities with bids; the outcome-revenue identity itself holds for
every bid profile.

Source: lines 215-232.
-/
theorem truthfulReports_utilitySum_eq_totalBidValue_and_fullValueRevenue
    {Agent : Type*} [Fintype Agent] (input : AuctionInput Agent)
    (htruth : TruthfulReports input) :
    (∑ i : Agent, input.values i) = totalBidValue input.bids ∧
      totalBidValue input.bids = (fullValueOutcome input.bids).revenue := by
  change input.bids = input.values at htruth
  constructor
  · rw [← htruth]
    rfl
  · exact (fullValueOutcome_revenue input.bids).symm

/-- `ℓ`, the smallest bid in a nonempty finite profile.

Source: lines 228-237.
-/
def lowestBid {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : ℝ :=
  (Finset.univ : Finset Agent).inf'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    bids

/-- `h`, the highest bid in a nonempty finite profile.

Source: lines 128-132 and 228-237.
-/
def highestBid {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    bids

/-- The source's scale normalization `ℓ = 1`.

Source: lines 128-132 and 235-238.
-/
def NormalizedBidScale {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : BidProfile Agent) : Prop :=
  lowestBid bids = 1

/-! ## Competitive-analysis conventions -/

/-- The displayed auction-performance ratio `R / B`, instantiated in the
paper with `B = T` or `B = F`.

Source: lines 239-245.
-/
def performanceRatio (revenue benchmark : ℝ) : ℝ :=
  revenue / benchmark

/-- A uniform positive constant-factor lower bound, the paper's use of
`R = Ω(B)` for a maximization problem.

Source: lines 239-245.
-/
def RevenueBigOmega {Instance : Type*}
    (revenue benchmark : Instance → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x, c * benchmark x ≤ revenue x

/-- A uniform constant-factor upper bound, the paper's use of `R = O(B)` for
an impossibility result.

Source: lines 239-245.
-/
def RevenueBigO {Instance : Type*}
    (revenue benchmark : Instance → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, revenue x ≤ C * benchmark x

/-- The paper's large-market assumption `α h ≤ F`.

Source: lines 256-263.
-/
def fixedPriceScaleCondition (alpha highest fixedPrice : ℝ) : Prop :=
  alpha * highest ≤ fixedPrice

/-- The weaker large-market assumption `α h ≤ T` used in some proofs.

Source: lines 263-265.
-/
def totalValueScaleCondition (alpha highest total : ℝ) : Prop :=
  alpha * highest ≤ total

/-- The positive-scale convention implicit when `α` counts a guaranteed
number of sales or tends to infinity.  It is separate from either displayed
inequality rather than hidden inside it.

Source: lines 256-265.
-/
def PositiveAlpha (alpha : ℝ) : Prop :=
  0 < alpha

/-- An auction is competitive on an assumption class when one positive
constant works uniformly for all admissible inputs.

Source: lines 266-267.
-/
def CompetitiveOn {Instance : Type*} (admissible : Instance → Prop)
    (revenue benchmark : Instance → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x, admissible x → c * benchmark x ≤ revenue x

/-- On an admissible class with a positive benchmark, competitiveness is
equivalent to a uniform positive lower bound on the displayed performance
ratio.  This is the paper's passage between `R = Ω(B)` and
`R / B = Ω(1)`; benchmark positivity is stated explicitly because it is
exactly what licenses division without changing the inequality.

Source: lines 239-245 and 266-267.
-/
theorem competitiveOn_iff_uniformPositivePerformanceRatio
    {Instance : Type*} (admissible : Instance → Prop)
    (revenue benchmark : Instance → ℝ)
    (hbenchmark_pos : ∀ x, admissible x → 0 < benchmark x) :
    CompetitiveOn admissible revenue benchmark ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x, admissible x →
        c ≤ performanceRatio (revenue x) (benchmark x) := by
  constructor
  · rintro ⟨c, hc_pos, hc⟩
    refine ⟨c, hc_pos, ?_⟩
    intro x hx
    exact (le_div_iff₀ (hbenchmark_pos x hx)).2 (hc x hx)
  · rintro ⟨c, hc_pos, hc⟩
    refine ⟨c, hc_pos, ?_⟩
    intro x hx
    exact (le_div_iff₀ (hbenchmark_pos x hx)).1 (hc x hx)

/-! ## Vickrey and bid-independent auction families -/

/-- Relational definition of a `k`-item Vickrey outcome: exactly `k` top bids
win, every winner pays the highest losing (the `(k+1)`st-highest) bid, and
ties may be resolved by the source's arbitrary fixed order.

Source: lines 284-287.
-/
def IsKItemVickreyOutcome {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : BidProfile Agent) (k : ℕ) (outcome : AuctionOutcome Agent) : Prop :=
  outcome.winners.card = k ∧
    (∀ i, i ∈ outcome.winners →
      ∀ j, j ∉ outcome.winners → bids j ≤ bids i) ∧
    ∃ critical : Agent,
      critical ∉ outcome.winners ∧
      (∀ j, j ∉ outcome.winners → bids j ≤ bids critical) ∧
      ∀ i, i ∈ outcome.winners → outcome.salePrice i = bids critical

/-- A deterministic mechanism implements the `k`-item Vickrey rule on every
bid profile.

Source: lines 284-287.
-/
def IsKItemVickreyAuction {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (auction : DeterministicAuction Agent) (k : ℕ) : Prop :=
  ∀ bids, IsKItemVickreyOutcome bids k (auction bids)

/-- The source's unlimited-supply Vickrey family chooses `k = f(n)` with
`1 ≤ f(n) < n`.  The condition is stated on the meaningful domain `2 ≤ n`.

Source: lines 289-291.
-/
def AdmissibleVickreySupplyRule (f : ℕ → ℕ) : Prop :=
  ∀ n, 2 ≤ n → 1 ≤ f n ∧ f n < n

/-- Whether equality at an offered price wins.  The source allows both the
weak (`b_i ≥ p`) and strict (`b_i > p`) boundary conventions.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
inductive ThresholdBoundary where
  | weak
  | strict
  deriving DecidableEq

/-- A bid-independent offer consists of its price and boundary convention.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
structure ThresholdOffer where
  price : ℝ
  boundary : ThresholdBoundary

/-- Acceptance under the source's weak or strict comparison convention.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
def accepts (offer : ThresholdOffer) (bid : ℝ) : Prop :=
  match offer.boundary with
  | .weak => offer.price ≤ bid
  | .strict => offer.price < bid

/-- `B_i`, the multiset of bids with bidder `i` removed.  A multiset retains
duplicate bid values, which are distinct bids in the source auction input.

Source: lines 351-354.
-/
def otherBids {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : BidProfile Agent) (i : Agent) : Multiset ℝ :=
  ((Finset.univ : Finset Agent).erase i).val.map bids

/-- The predetermined function `f` from other-bid multisets to an offered
price and its open/closed boundary convention.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
abbrev BidIndependentRule := Multiset ℝ → ThresholdOffer

/-- The outcome generated by the paper's bid-independent rule: bidder `i`
receives the offer computed from `B_i`, wins exactly when its bid passes the
returned comparison, and pays the returned price.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
def bidIndependentOutcome {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (rule : BidIndependentRule) (bids : BidProfile Agent) :
    AuctionOutcome Agent := by
  classical
  exact
    { winners := (Finset.univ : Finset Agent).filter fun i =>
        accepts (rule (otherBids bids i)) (bids i)
      salePrice := fun i => (rule (otherBids bids i)).price }

/-- A bid-independent outcome always fills winning bids at or below their
reports, for either permitted boundary convention.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
theorem bidIndependentOutcome_fillsAtOrBelow
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (rule : BidIndependentRule) (bids : BidProfile Agent) :
    (bidIndependentOutcome rule bids).FillsAtOrBelow bids := by
  classical
  intro i hi
  have haccept : accepts (rule (otherBids bids i)) (bids i) :=
    (Finset.mem_filter.mp hi).2
  cases hboundary : (rule (otherBids bids i)).boundary with
  | weak =>
      simpa [accepts, hboundary, bidIndependentOutcome] using haccept
  | strict =>
      exact le_of_lt (by
        simpa [accepts, hboundary, bidIndependentOutcome] using haccept)

/-- The deterministic bid-independent auction induced by `f`.

Source: lines 351-357 and footnote 2 at lines 372-374.
-/
def bidIndependentAuction {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (rule : BidIndependentRule) : DeterministicAuction Agent :=
  bidIndependentOutcome rule

end

end SourceDefinitions
end GHW01DigitalGoods
