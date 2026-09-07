import GHW01DigitalGoods.AuctionMainTheorems

/-!
# GHW Bid-Independent Boundary Convention

Section 5.1 of the source permits a bid-independent rule to choose, for each
erased multiset of bids, whether equality with its posted price is accepted.  The
existing deterministic lower-bound construction uses the revenue-maximizing
weak (`>=`) convention.  This file makes the wider source convention explicit
and proves that it is pointwise dominated on the binary adversarial inputs.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib.Auction

/-!
The `acceptsEquality` bit is the source footnote's per-erased-multiset choice:
`true` means a bidder with bid equal to the posted price wins (`bid >= price`),
and `false` means she must strictly exceed it (`bid > price`).
-/
structure PaperBidIndependentBoundaryRule where
  price : Multiset ℝ → ℝ
  acceptsEquality : Multiset ℝ → Bool

/-- Whether the source rule accepts one bid at the price selected from its
erased bid multiset. -/
def PaperBidIndependentBoundaryRule.accepts
    (rule : PaperBidIndependentBoundaryRule) (others : Multiset ℝ) (bid : ℝ) : Prop :=
  if rule.acceptsEquality others then rule.price others ≤ bid else rule.price others < bid

/-- Payment obtained from one bidder under the source's strict-or-weak
threshold convention. -/
noncomputable def paperBidIndependentBoundaryPayment
    (rule : PaperBidIndependentBoundaryRule) (others : Multiset ℝ) (bid : ℝ) : ℝ :=
  if rule.acceptsEquality others then
    if rule.price others ≤ bid then rule.price others else 0
  else if rule.price others < bid then rule.price others else 0

/--
On a nonnegative bid, allowing equality can only increase the corresponding
payment.  This is the only place where the `>=` convention is used to reduce
the Section 5.1 source model to the existing weak-threshold construction.
-/
theorem paperBidIndependentBoundaryPayment_le_weak
    (rule : PaperBidIndependentBoundaryRule) (others : Multiset ℝ) (bid : ℝ)
    (hbid_nonneg : 0 ≤ bid) :
    paperBidIndependentBoundaryPayment rule others bid ≤
      if rule.price others ≤ bid then rule.price others else 0 := by
  by_cases hweak : rule.price others ≤ bid
  · by_cases hequality : rule.acceptsEquality others
    · simp [paperBidIndependentBoundaryPayment,
        hequality, hweak]
    · by_cases hstrict : rule.price others < bid
      · simp [paperBidIndependentBoundaryPayment,
          hequality, hstrict, hweak]
      · have hprice_eq_bid : rule.price others = bid :=
          le_antisymm hweak (le_of_not_gt hstrict)
        simp [paperBidIndependentBoundaryPayment,
          hequality,
          hprice_eq_bid, hbid_nonneg]
  · have hstrict : ¬ rule.price others < bid := fun hlt => hweak (le_of_lt hlt)
    simp [paperBidIndependentBoundaryPayment,
      hweak, hstrict]

/--
Revenue of a Section 5.1 source bid-independent rule on the binary input used
in Theorem 9.1.  Each bidder's price and equality convention are computed from
that bidder's erased bid multiset, so the `>=`/`>` choice can vary with the
other bids while remaining invariant to their presentation order.
-/
noncomputable def twoValueBidIndependentBoundaryRevenue
    (rule : PaperBidIndependentBoundaryRule)
    (highValue highCount lowCount : ℕ) : ℝ :=
  (highCount : ℝ) *
      paperBidIndependentBoundaryPayment rule
        (Multiset.ofList
          (twoValueErasedBidList highValue (highCount - 1) lowCount))
        (highValue : ℝ) +
    (lowCount : ℝ) *
      paperBidIndependentBoundaryPayment rule
        (Multiset.ofList
          (twoValueErasedBidList highValue highCount (lowCount - 1))) 1

/--
The source's arbitrary per-multiset strict-or-weak rule has no more revenue on a
binary input than its same-price weak (`>=`) counterpart.  The comparison is
valid even for an arbitrary real-valued price rule: the only extra weak wins
are equality wins, which pay the nonnegative bid value.
-/
theorem twoValueBidIndependentBoundaryRevenue_le_weak
    (rule : PaperBidIndependentBoundaryRule)
    (highValue highCount lowCount : ℕ) :
    twoValueBidIndependentBoundaryRevenue rule highValue highCount lowCount ≤
      twoValueBidIndependentPriceRevenue
        (twoValueListBidIndependentThresholdPrice
          (fun others => rule.price (Multiset.ofList others)) highValue)
        highValue highCount lowCount := by
  have hhigh_payment :=
    paperBidIndependentBoundaryPayment_le_weak rule
      (Multiset.ofList
        (twoValueErasedBidList highValue (highCount - 1) lowCount))
      (highValue : ℝ) (by exact_mod_cast Nat.zero_le highValue)
  have hlow_payment :=
    paperBidIndependentBoundaryPayment_le_weak rule
      (Multiset.ofList
        (twoValueErasedBidList highValue highCount (lowCount - 1)))
      1 (by norm_num)
  have hhigh_count_nonneg : 0 ≤ (highCount : ℝ) := by
    exact_mod_cast Nat.zero_le highCount
  have hlow_count_nonneg : 0 ≤ (lowCount : ℝ) := by
    exact_mod_cast Nat.zero_le lowCount
  simpa [twoValueBidIndependentBoundaryRevenue,
    twoValueBidIndependentPriceRevenue,
    twoValueListBidIndependentThresholdPrice] using
    add_le_add
      (mul_le_mul_of_nonneg_left hhigh_payment hhigh_count_nonneg)
      (mul_le_mul_of_nonneg_left hlow_payment hlow_count_nonneg)

/--
Source-faithful GHW Theorem 9.1 binary witness.  The rule may choose `>=` or
`>` separately for every erased bid multiset, exactly as allowed in the Section
5.1 footnote.  The existing weak-threshold witness applies because the source
revenue is pointwise no larger than weak-threshold revenue at the same price.
-/
theorem paper_theorem9_1_bid_independent_boundary_multiset_rule_scaled_lower_bound_fixed_price_benchmark
    (rule : PaperBidIndependentBoundaryRule) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentBoundaryRevenue
            rule highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hweak_revenue, hscale⟩ :=
    paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark
      (fun others => rule.price (Multiset.ofList others)) hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, ?_, hscale⟩
  have hsource_le_weak :=
    twoValueBidIndependentBoundaryRevenue_le_weak
      rule highValue highCount lowCount
  have hhigh_nonneg : 0 ≤ (highValue : ℝ) := by
    exact_mod_cast Nat.zero_le highValue
  exact le_trans
    (mul_le_mul_of_nonneg_left hsource_le_weak hhigh_nonneg)
    hweak_revenue

/--
Attained form of the source-faithful GHW Theorem 9.1 binary witness.  In
addition to the benchmark inequalities, `0 < highCount` certifies that the
high value occurs in the constructed input.
-/
theorem paper_theorem9_1_bid_independent_boundary_multiset_rule_scaled_lower_bound_fixed_price_benchmark_attained
    (rule : PaperBidIndependentBoundaryRule) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (highValue : ℝ) *
          twoValueBidIndependentBoundaryRevenue
            rule highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hattained, hweak_revenue, hscale⟩ :=
    paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark_attained
      (fun others => rule.price (Multiset.ofList others)) hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, hattained, ?_, hscale⟩
  have hsource_le_weak :=
    twoValueBidIndependentBoundaryRevenue_le_weak
      rule highValue highCount lowCount
  have hhigh_nonneg : 0 ≤ (highValue : ℝ) := by
    exact_mod_cast Nat.zero_le highValue
  exact le_trans
    (mul_le_mul_of_nonneg_left hsource_le_weak hhigh_nonneg)
    hweak_revenue

/--
Real-parameter form of the source-faithful Theorem 9.1 witness.  The finite
construction uses the positive natural ceiling of the source constant `alpha`,
and the final inequality is weakened back to that original real constant.
-/
theorem paper_theorem9_1_bid_independent_boundary_multiset_rule_real_alpha_scaled_lower_bound_fixed_price_benchmark
    (rule : PaperBidIndependentBoundaryRule) {highValue : ℕ} {alpha : ℝ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentBoundaryRevenue
            rule highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * alpha ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  let alphaNat : ℕ := ⌈alpha⌉₊
  have halphaNat_pos : 0 < alphaNat := by
    simpa [alphaNat] using (Nat.ceil_pos.mpr halpha_pos)
  obtain ⟨highCount, lowCount, hboundary_revenue, hscale⟩ :=
    paper_theorem9_1_bid_independent_boundary_multiset_rule_scaled_lower_bound_fixed_price_benchmark
      rule hhigh_ge_two halphaNat_pos
  refine ⟨highCount, lowCount, hboundary_revenue, ?_⟩
  have halpha_le : alpha ≤ (alphaNat : ℝ) := by
    simpa [alphaNat] using (Nat.le_ceil alpha)
  have hhigh_nonneg : 0 ≤ (highValue : ℝ) := by
    exact_mod_cast Nat.zero_le highValue
  exact le_trans
    (mul_le_mul_of_nonneg_left halpha_le hhigh_nonneg)
    hscale

/--
Attained real-parameter form of the source-faithful Theorem 9.1 witness.
-/
theorem paper_theorem9_1_bid_independent_boundary_multiset_rule_real_alpha_scaled_lower_bound_fixed_price_benchmark_attained
    (rule : PaperBidIndependentBoundaryRule) {highValue : ℕ} {alpha : ℝ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (highValue : ℝ) *
          twoValueBidIndependentBoundaryRevenue
            rule highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * alpha ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  let alphaNat : ℕ := ⌈alpha⌉₊
  have halphaNat_pos : 0 < alphaNat := by
    simpa [alphaNat] using (Nat.ceil_pos.mpr halpha_pos)
  obtain ⟨highCount, lowCount, hattained, hboundary_revenue, hscale⟩ :=
    paper_theorem9_1_bid_independent_boundary_multiset_rule_scaled_lower_bound_fixed_price_benchmark_attained
      rule hhigh_ge_two halphaNat_pos
  refine ⟨highCount, lowCount, hattained, hboundary_revenue, ?_⟩
  have halpha_le : alpha ≤ (alphaNat : ℝ) := by
    simpa [alphaNat] using (Nat.le_ceil alpha)
  have hhigh_nonneg : 0 ≤ (highValue : ℝ) := by
    exact_mod_cast Nat.zero_le highValue
  exact le_trans
    (mul_le_mul_of_nonneg_left halpha_le hhigh_nonneg)
    hscale

/--
Ratio form of the attained real-parameter Theorem 9.1 witness.  Positivity of
`alpha` makes the benchmark denominator strictly positive, so the displayed
ratio is the ordinary source ratio rather than a vacuous division-by-zero
statement.
-/
theorem paper_theorem9_1_bid_independent_boundary_multiset_rule_real_alpha_ratio_witness_attained
    (rule : PaperBidIndependentBoundaryRule) {highValue : ℕ} {alpha : ℝ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      twoValueBidIndependentBoundaryRevenue rule
          highValue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * alpha ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hattained, hrevenue, hscale⟩ :=
    paper_theorem9_1_bid_independent_boundary_multiset_rule_real_alpha_scaled_lower_bound_fixed_price_benchmark_attained
      rule hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, hattained, ?_, hscale⟩
  have hhigh_pos : 0 < (highValue : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hhigh_ge_two)
  have hbenchmark_pos :
      0 < twoValueFixedPriceBenchmark highValue highCount lowCount := by
    exact lt_of_lt_of_le (mul_pos hhigh_pos halpha_pos) hscale
  exact
    paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark
      hhigh_pos hbenchmark_pos hrevenue

end GHW01DigitalGoods
