import GHW01DigitalGoods.MainTheorems

/-!
# Paper Assumptions: GHW01 Digital Goods

This file records source theorem conditions used by the compact paper-facing
interface: normalized bid ranges, benchmark prerequisites, truthfulness
conditions, and lower-bound parameter conditions.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib.Auction
open scoped BigOperators

/-- Corollary 4.2 fixes `h` as a maximum bid. -/
-- audit-premise: hmax : ∃ i : Agent, values i = h
abbrev assumption_high_value_attained {Agent : Type*}
    (values : Agent → ℝ) (h : ℝ) : Prop :=
  ∃ i : Agent, values i = h

/-- Weighted-pairing statements expose the paper's total-value notation. -/
-- audit-premise: htotal : total = totalValue values
abbrev assumption_total_value_notation {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (total : ℝ) : Prop :=
  total = ∑ i : Agent, values i

/-- Theorem 7.1 assumes the high-bid value is small relative to total value. -/
-- audit-premise: hlarge : 4 * h ≤ total
abbrev assumption_weighted_pairing_large_market (h total : ℝ) : Prop :=
  4 * h ≤ total

/-- Theorem 7.2 assumes the paper fixed-price benchmark is at least twice `h`. -/
-- audit-premise: hF_ge_two_h : 2 * h ≤ finiteCandidateFixedPriceBenchmark values 1
abbrev assumption_fixed_price_benchmark_large_enough
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (h : ℝ) : Prop :=
  2 * h ≤ finiteCandidateFixedPriceBenchmark values 1

/-- Lemma 9.2 is stated for truthful auctions. The corrected Lemma 8.1 uses
the separately reviewed journal monotone-offer condition instead. -/
-- audit-premise: hM : truthful M
-- audit-premise: htruth : truthful M
abbrev assumption_truthful_auction_condition
    {Agent : Type*}
    (M : DigitalGoodsAuction Agent) : Prop := by
  classical
  exact paper_digital_goods_truthful M

/-- Lemma 8.1 compares a lower bid with a higher bid. -/
-- audit-premise: hlt : low < high
abbrev assumption_low_bid_below_high_bid (low high : ℝ) : Prop :=
  low < high

/--
Lemma 8.1 and Theorem 8.2 are checked against the later journal version's
monotone randomized-offer formulation rather than the broader preliminary
SODA wording. The approved formal target additionally uses finite bidder and
price carriers and PMF-valued, hence finite/countably-supported, marginal offer
laws; those are explicit formalization-domain restrictions, not conditions
attributed to the journal statement. Within that domain, the mathematical
antecedent consists of nonnegative values, nonnegative offered prices, and
monotonicity of the marginal offer CDFs; it is not an opaque source-model
record.
-/
-- audit-premise: hvalue_nonneg : ∀ i, 0 ≤ values i
-- audit-premise: hprice_nonneg : ∀ p, 0 ≤ price p
-- audit-premise: hcdf_monotone : ∀ i j, values i ≤ values j → ∀ t, t ≤ values i → AppliedModelingLib.pmfProb (offerLaw i) (fun p => price p ≤ t) ≤ AppliedModelingLib.pmfProb (offerLaw j) (fun p => price p ≤ t)
abbrev assumption_theorem8_2_journal_raw_cdf_monotone_offer_source_model
    {Agent Price : Type*} [Fintype Agent] [Nonempty Agent]
    [Fintype Price]
    (values : Agent → ℝ) (price : Price → ℝ) (offerLaw : Agent → PMF Price) :
    Prop := by
  classical
  exact
    (∀ i, 0 ≤ values i) ∧
      (∀ p, 0 ≤ price p) ∧
        ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
          AppliedModelingLib.pmfProb (offerLaw i) (fun p => price p ≤ t) ≤
            AppliedModelingLib.pmfProb (offerLaw j) (fun p => price p ≤ t)

/--
Theorem 9.3's source-model carrier.  This makes explicit the paper's
deterministic truthful-auction model, including its binary outcome and
sale-price conventions, together with the focused bidder slice as a function
of the multiset of other bids.  The erased-list implementation bridge is
derived from this source-facing carrier inside the proof.
-/
-- audit-premise: model : assumption_theorem9_3_primitive_set_of_bids_deterministic_source_model highValue
abbrev assumption_theorem9_3_primitive_set_of_bids_deterministic_source_model
    (highValue : ℕ) :=
  PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue

end GHW01DigitalGoods
