import GHW01DigitalGoods.MainTheorems

/-!
# Post-paper audit: Competitive Auctions and Digital Goods

This file is the Lean-side endpoint ledger for the Goldberg-Hartline-Wright
digital-goods paper. For the compact human-facing statement surface, read
`PaperInterface.lean`; each theorem below is an importable source-numbered
endpoint delegated to the paper-facing theorem exported by
`GHW01DigitalGoods.MainTheorems`.

Cached source text inventory checked by this audit:

- Theorem 4.1, line 359: `F >= T / (2 log h)`.
- Corollary 4.2, line 301: `F >= T / (4 log n)`.
- Lemma 6.1, line 428: random subset split lower-tail estimate.
- Theorem 6.2, line 479: random sampling auction revenue guarantee.
- Theorem 7.1, line 563: weighted pairing gets `Omega(T / log h)` when `4h <= T`.
- Theorem 7.2, line 626: weighted pairing gets `Omega(F / log h)` when `F >= 2h`.
- Lemma 8.1, line 747: truthfulness implies monotone win probabilities.
- Theorem 8.2, line 833: Section 8.2 is checked against the later journal
  monotone-auction formulation; the preliminary unrestricted wording is
  recorded only as a source-version audit note.
- Theorem 9.1, line 979: bid-independent lower-bound witness.
- Lemma 9.2, line 1105: truthful deterministic auctions are bid-independent.
- Theorem 9.3, line 1100: deterministic truthful lower-bound witness.
- Section 11, lines 1637--1712: `F_k`, `T_k`, `opt_k`, the bounded Theorem 4.1,
  capped single- and dual-price sampling auctions, truthfulness, concentration
  and balanced-sample competitiveness, the truthful and capacity-feasible
  deterministic `opt_k` extension, and transport of unlimited-supply upper
  bounds through the `k=n` slice.

The corresponding README rows and DAG nodes are checked in
`FINAL_VALIDATION_REPORT.md`.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib.Auction
open scoped BigOperators

/-- Audit endpoint for the repaired exact GHW Theorem 4.1 domain. -/
theorem audit_theorem4_1_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_two : 2 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (2 * Real.logb 2 h) *
        finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
      values hh_ge_two hvalue_ge_one hvalue_le_h

/--
Audit endpoint for the corrected exact GHW Corollary 4.2 domain.  The source
omits the visible nondegenerate cardinality premise `2 <= n`.
-/
theorem audit_corollary4_2_fixed_price_lower_bound
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
  exact
    paper_corollary4_2_fixed_price_lower_bound_exact_logb_of_card_two_le
      values hvalues_nonneg hh_pos hmax hvalue_le_h hcard_ge_two

/-- Audit endpoint for the source's exact fixed-cardinality Lemma 6.1. -/
theorem audit_lemma6_1_fixed_size
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
  exact lemma6_1_fixed_size_lower_tail heligible hsample_pos hsample_lt
    hdelta_pos hdelta_le_one

/-- Independent fair-coin lower-tail support for the fixed-size Lemma 6.1 proof. -/
theorem audit_lemma6_1_fair_coin_support
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (AppliedModelingLib.FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp (-(s.card : ℝ) / 36) := by
  exact paper_aux_theorem6_2_fair_coin_lower_tail_relaxed s keep

/--
Audit endpoint for GHW Theorem 6.2: the original directional auction under a
uniform exact half-sample.  The positive half-size makes the technical
`NeZero (m + m)` instance redundant as a mathematical premise.
-/
theorem audit_theorem6_2_random_sampling
    (m : ℕ) [NeZero (m + m)] (hm_pos : 0 < m)
    (values : Fin (m + m) → ℝ) {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
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
                (sampledSideAssignment sample.1) true 1).revenue values) := by
  exact
    theorem6_2_directional_fixed_half_revenue_bound_of_finite_candidate_benchmark_all_alpha
      values m hm_pos (by simp) hhigh_pos hvalue_bound halpha_highValue

/--
Independent fair-coin counterpart retained as support only.  It is not the
exact-half source endpoint above and receives no source-theorem credit.
-/
theorem audit_theorem6_2_random_sampling_fair_coin_support
    {n : ℕ} [NeZero n]
    (values : Fin n → ℝ) (keep : Bool) {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (AppliedModelingLib.FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  exact
    theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
      values keep hhigh_pos hvalue_bound halpha_highValue

/-- Audit endpoint for GHW Theorem 7.1 under the paper condition `4h <= T`. -/
theorem audit_theorem7_1_weighted_pairing
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
  exact
    paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hlarge

/-- Audit endpoint for GHW Theorem 7.2 under the paper condition `F^(2) >= 2h`. -/
theorem audit_theorem7_2_weighted_pairing_benchmark
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
  exact
    paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hF_ge_two_h
      hs_ge_two hlog_le_s_sq

/-- Audit endpoint for the explicit Theorem 7.2 repeated-bid tightness family. -/
theorem audit_theorem7_2_weighted_pairing_tightness
    (k s : ℕ) (hs_two : 2 ≤ s) (hk_large : s * s + 2 ≤ k) :
    weightedPairingExpectedRevenue (ghwTightValue k s) ≤
      (3 / (s : ℝ)) * ghwTightTwoWinnerBenchmarkValue k s hs_two := by
  exact paper_theorem7_2_tightness_ratio_for_repeated_bid_family
    k s hs_two hk_large

/-- Audit endpoint for GHW Lemma 8.1: own-bid monotonicity from truthfulness. -/
theorem audit_lemma8_1_truthful_monotone
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hM : paper_digital_goods_truthful M)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := by
  exact paper_lemma8_1_allocation_mono_own_bid_of_truthful M hM bids i hlt

/--
Audit endpoint for GHW Theorem 8.2, using the later journal version's monotone
truthful randomized-auction statement. The source model records the journal
CDF monotonicity condition on raw marginal offer laws; the adjacent surplus
recursion is derived internally from those CDF inequalities.
-/
theorem audit_theorem8_2_truthful_revenue_upper_bound
    {Agent Price : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [Fintype Price] [DecidableEq Price]
    [LinearOrder Agent]
    (model :
      PaperTheorem82JournalRawCDFMonotoneOfferSourceModel Agent Price) :
    paper_theorem8_2_raw_cdf_expected_revenue
        model.values model.price model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_offer_source_model
      model

/--
Source-version audit endpoint for Section 8.2.

This declaration is not part of the paper-facing theorem inventory. It records
why the public Section 8.2 endpoint is checked against the later journal
monotone-auction formulation rather than against the preliminary unrestricted
wording. -/
theorem audit_theorem8_2_weak_truthful_counterexample :
    finiteCandidateFixedPriceBenchmark paper_theorem8_2_counterexample_values 1 <
      paper_theorem8_2_counterexample_auction.revenue
        paper_theorem8_2_counterexample_values := by
  exact paper_theorem8_2_counterexample_revenue_gt_benchmark

/--
Audit endpoint for GHW Theorem 9.1 in the paper anonymous erased-bid-list
model for deterministic bid-independent auctions.
-/
theorem audit_theorem9_1_bid_independent_lower_bound
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
  exact
    paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark
      priceRule hhigh_ge_two halpha_pos

/--
Audit endpoint for GHW Lemma 9.2: truthful deterministic IR/NPT binary auction
slices admit nonnegative critical-price thresholds.
-/
theorem audit_lemma9_2_threshold_domination
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
  exact
    paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
      M htruth hIR hNPT hbinary bids i

/--
Audit endpoint for GHW Theorem 9.3. From deterministic truthfulness, IR/NPT,
binary allocation, and the paper's set-of-bids focused-outcome convention,
the erased-list relabeling bridge and Lemma 9.2 list-price representation are
constructed internally.
-/
theorem audit_theorem9_3_deterministic_truthful_lower_bound
    {highValue alpha : ℕ}
    (model :
      PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (model.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_set_of_bids_source_model
      model hhigh_ge_two halpha_pos

/-! ## Section 11 bounded-supply endpoints -/

theorem audit_section11_bounded_fixed_price_lower_bound
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) {h : ℝ}
    (hh_ge_two : 2 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    boundedSupplyTopKTotal values capacity ≤
      (2 * Real.logb 2 h) *
        boundedSupplyFixedPriceBenchmark values capacity := by
  exact boundedSupplyFixedPriceBenchmark_ge_topK_exact_logb_of_two_le
    values capacity hh_ge_two hvalue_ge_one hvalue_le_h

theorem audit_section11_single_price_truthful_and_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) (values : Agent → ℝ) :
    (boundedSinglePriceSamplingAuction side sampleSide
        sampleSize marketSize capacity).TruthfulDominantStrategy ∧
      boundedCappedAllocationCount side (!sampleSide)
          (boundedSamplingPriceRule side sampleSide
            (scaledSampleCapacity sampleSize marketSize capacity)) capacity values ≤
        capacity := by
  exact ⟨boundedSinglePriceSamplingAuction_truthful side sampleSide
      sampleSize marketSize capacity,
    boundedSinglePriceSamplingAuction_supply_feasible side sampleSide
      sampleSize marketSize capacity values⟩

theorem audit_section11_single_price_combined_guarantee
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
        (boundedSinglePriceSamplingAuction
          (sampledSideAssignment sample.1) true sampleSize
          (Fintype.card Agent - sampleSize) capacity).TruthfulDominantStrategy) ∧
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
  exact boundedSinglePriceSampling_fixedSize_combined_guarantee
    sampleSize capacity values hsample_lt hbeta hgamma hsuccess
    hsuccess_le_one hgood_probability

theorem audit_section11_small_rejection_combined_guarantee
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

theorem audit_section11_dual_price_truthful_and_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) (values : Agent → ℝ) :
    (boundedDualPriceSamplingAuction side capacity).TruthfulDominantStrategy ∧
      boundedDualAllocationCount side capacity values ≤ capacity := by
  exact ⟨boundedDualPriceSamplingAuction_truthful side capacity,
    boundedDualPriceSamplingAuction_supply_feasible side capacity values⟩

theorem audit_section11_dual_price_combined_guarantee
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
        (boundedDualPriceSamplingAuction
          (sampledSideAssignment sample.1) capacity).TruthfulDominantStrategy) ∧
      (∀ sample : FixedSizeSampleSpace Agent (Fintype.card Agent / 2),
        boundedDualAllocationCount
            (sampledSideAssignment sample.1) capacity values ≤ capacity) ∧
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw (Fintype.card Agent / 2)
          (Nat.div_le_self _ _))
        (fun sample => boundedDualPriceSamplingCompetitiveEvent sample.1
          capacity values beta gamma) := by
  exact boundedDualPriceSampling_fixedHalf_combined_guarantee
    capacity values hbeta hgamma hsuccess hsuccess_le_one
    hgood_probability

theorem audit_section11_deterministic_optimal_threshold_truthful_and_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) (values : Agent → ℝ) :
    (boundedDeterministicOptimalThresholdAuction
        (Agent := Agent) capacity).TruthfulDominantStrategy ∧
      boundedDeterministicOptimalThresholdAllocationCount capacity values ≤
        capacity := by
  exact ⟨boundedDeterministicOptimalThresholdAuction_truthful capacity,
    boundedDeterministicOptimalThresholdAuction_supply_feasible capacity values⟩

theorem audit_section11_unlimited_upper_bounds_transport
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {bound : ℝ}
    (hunlimited : M.revenue values ≤
      bound * finiteCandidateFixedPriceBenchmark values 1) :
    M.revenue values ≤
      bound * boundedSupplyFixedPriceBenchmark values (Fintype.card Agent) := by
  exact unlimitedUpperBound_transports_to_boundedSupply M values hunlimited

end GHW01DigitalGoods
