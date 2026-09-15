import GHW01DigitalGoods.ProofBridge

namespace GHW01DigitalGoods

namespace PaperInterface

open AppliedModelingLib.Auction
open MeasureTheory
open scoped BigOperators
open GHW01DigitalGoods.ProofBridge
noncomputable section

/-- Source-facing semantic target for the bundled definition `definition_revenue`. -/
def definition_revenueSpec : Prop :=
  (∀ {Agent : Type*}
    (outcome : source_auctionOutcome Agent), GHW01DigitalGoods.ProofBridge.source_outcomeRevenue (Agent := Agent) (outcome := outcome) = SourceDefinitions.AuctionOutcome.revenue outcome) ∧
    (∀ {Agent : Type*}
    (auction : source_deterministicAuction Agent)
    (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_deterministicRevenue (Agent := Agent) (auction := auction) (bids := bids) = SourceDefinitions.deterministicRevenue auction bids) ∧
    (∀ {Agent : Type*}
    (auction : source_randomizedAuction Agent)
    (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_randomizedRevenueLaw (Agent := Agent) (auction := auction) (bids := bids) = SourceDefinitions.randomizedRevenueLaw auction bids)

/-- Source-facing semantic target for the bundled definition `definition_truthfulness`. -/
def definition_truthfulnessSpec : Prop :=
  (∀ {Agent : Type*}
    (auction : source_deterministicAuction Agent), GHW01DigitalGoods.ProofBridge.source_deterministicTruthful (Agent := Agent) (auction := auction) =
      by
        classical
        exact SourceDefinitions.DeterministicTruthful auction) ∧
    (∀ {Agent : Type*}
    (auction : source_randomizedAuction Agent), GHW01DigitalGoods.ProofBridge.source_randomizedTruthful (Agent := Agent) (auction := auction) =
      by
        classical
        exact SourceDefinitions.RandomizedTruthful auction)

/-- Source-facing semantic target for the bundled definition `definition_fixed_price_benchmark`. -/
def definition_fixed_price_benchmarkSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_optimalFixedPriceRevenue (Agent := Agent) (bids := bids) = SourceDefinitions.optimalFixedPriceRevenue bids)

/-- Source-facing semantic target for the bundled definition `definition_total_value`. -/
def definition_total_valueSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent] (values : Agent → ℝ), GHW01DigitalGoods.ProofBridge.totalValue (Agent := Agent) (values := values) = ∑ i : Agent, values i) ∧
    (∀ {Agent : Type*} [Fintype Agent] (input : source_auctionInput Agent)
    (htruth : SourceDefinitions.TruthfulReports input), totalValue input.values = SourceDefinitions.totalBidValue input.bids ∧   SourceDefinitions.totalBidValue input.bids =     (SourceDefinitions.fullValueOutcome input.bids).revenue)

/-- Source-facing semantic target for the bundled definition `definition_weighted_pairing_revenue`. -/
def definition_weighted_pairing_revenueSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i), GHW01DigitalGoods.ProofBridge.source_weightedPairingW (Agent := Agent) (bids := bids) (hbid_ge_one := hbid_ge_one) (hdistinct := hdistinct) =
      by
        classical
        exact SourceDefinitions.weightedPairingW bids
          (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
            bids hbid_ge_one hdistinct)) ∧
    (∀ {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i), GHW01DigitalGoods.ProofBridge.source_weightedPairingOutcomeExpectedRevenue (Agent := Agent) (bids := bids) (hbid_ge_one := hbid_ge_one) (hdistinct := hdistinct) =
      by
        classical
        exact SourceDefinitions.weightedPairingOutcomeExpectedRevenue bids
          (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
            bids hbid_ge_one hdistinct)) ∧
    (∀ {Agent : Type*} [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i), source_weightedPairingOutcomeExpectedRevenue bids hbid_ge_one hdistinct =   source_weightedPairingW bids hbid_ge_one hdistinct)

/-- Source-facing semantic target migrated from `theorem4_1_high_valueSpec`. -/
def result_theorem4_1Spec : Prop :=
  ∀ {Agent : Type*} [Fintype Agent]
      (values : Agent → ℝ) {h : ℝ}
      (_hh_ge_two : 2 ≤ h)
      (_hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
      (_hvalue_le_h : ∀ i : Agent, values i ≤ h)
      (_hhighest : ∃ i : Agent, values i = h),
      let _ : Nonempty Agent := ⟨Classical.choose _hhighest⟩
      totalValue values ≤
        (2 * Real.logb 2 h) * fixedPriceBenchmark values

/-- Source-facing semantic target migrated from `corollary4_2_fixed_price_lower_boundSpec`. -/
def result_corollary4_2Spec : Prop :=
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

/-- Source-facing semantic target migrated from `lemma6_1_fixed_sizeSpec`. -/
def result_lemma6_1_fixed_size_lower_tailSpec : Prop :=
  by
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

/-- Source-facing semantic target migrated from `theorem6_2_random_samplingSpec`. -/
def result_theorem6_2_random_samplingSpec : Prop :=
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

/-- Supporting extension of Theorem 6.2 with the source's real scale
parameter.  The source-facing row above remains the archival natural-count
contract; this extension keeps `0 ≤ alpha` explicit and uses the same finite
candidate benchmark and fair-coin event. -/
def extension_theorem6_2_real_alphaSpec : Prop :=
  ∀ {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha highValue : ℝ}
    (_halpha_nonneg : 0 ≤ alpha)
    (_hhigh_pos : 0 < highValue)
    (_hvalue_bound : ∀ i, values i ≤ highValue)
    (_halpha_highValue : alpha * highValue ≤ finiteCandidateFixedPriceBenchmark values 1),
    1 - Real.exp (-alpha / 36) - 40 * Real.exp (-alpha / 72) ≤
      (AppliedModelingLib.FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 * (randomSamplingOptimalThresholdAuction side keep 1).revenue values}

/-- Source-facing semantic target migrated from `theorem7_1_weighted_pairingSpec`. -/
def result_theorem7_1_weighted_pairingSpec : Prop :=
  by
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

/-- Source-facing semantic target migrated from `theorem7_2_weighted_pairing_benchmarkSpec`. -/
def result_theorem7_2_lower_boundSpec : Prop :=
  by
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

/-- Source-facing semantic target migrated from `theorem7_2_weighted_pairing_tightness_selected_sqrt_logSpec`. -/
def result_theorem7_2_tightnessSpec : Prop :=
  ∀ (s : ℕ) (hs_two : 2 ≤ s),
      weightedPairingRevenue (ghwTightValue (s * s + 2) s) ≤
        (6 / Real.sqrt
          (Real.logb 2 ((2 : ℝ) ^ (s * s + 2)))) *
          ghwTightFixedPriceBenchmarkValue (s * s + 2) s hs_two

/-- Source-facing semantic target migrated from `lemma8_1_truthful_monotoneSpec`. -/
def result_lemma8_1_monotone_allocationSpec : Prop :=
  by
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

/-- Source-facing semantic target migrated from `theorem8_2_truthful_revenue_upper_boundSpec`. -/
def result_theorem8_2_journal_revenue_upper_boundSpec : Prop :=
  by
    classical
    exact
    ∀ {Agent : Type*} [Fintype Agent] [Nonempty Agent]
      (values : Agent → ℝ) (offerLaw : Agent → Measure ℝ)
      (_hofferLaw_isProbability : ∀ i, IsProbabilityMeasure (offerLaw i))
      (_hvalue_nonneg : ∀ i, 0 ≤ values i)
      (_hoffer_nonneg : ∀ i, offerLaw i (Set.Iio 0) = 0)
      (_hcdf_monotone :
        ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
          ProbabilityTheory.cdf (offerLaw i) t ≤
            ProbabilityTheory.cdf (offerLaw j) t),
      paper_theorem8_2_continuous_marginal_expected_revenue
          values offerLaw ≤ fixedPriceBenchmark values

/-! A reusable extension of the journal Theorem 8.2 bridge.  The source says
"probability distributions" without restricting the offer seed to finite or
countable support.  This supporting target therefore uses an arbitrary
probability measure and exposes the sole analytic obligation—integrability of
the realized revenue—rather than silently treating a continuous law as a PMF.
It is not counted as a new numbered source claim. -/
def extension_theorem8_2_continuous_measure_revenueSpec : Prop :=
  ∀ {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [MeasurableSpace Outcome]
    (μ : Measure Outcome) [IsProbabilityMeasure μ]
    (values : Agent → ℝ) (offerPrice : Outcome → Agent → ℝ)
    (_hoff_integrable : Integrable
      (fun outcome => paper_theorem8_2_journal_monotone_offer_revenue
        values (offerPrice outcome)) μ)
    (_hoff_nonneg : ∀ᵐ outcome ∂μ, ∀ i, 0 ≤ offerPrice outcome i)
    (_hoff_accept_monotone : ∀ᵐ outcome ∂μ, ∀ i j, values i ≤ values j →
      offerPrice outcome i ≤ values i → offerPrice outcome j ≤ offerPrice outcome i),
    paper_theorem8_2_journal_monotone_measure_expected_revenue
        μ values offerPrice ≤
      finiteCandidateFixedPriceBenchmark values 1

/-- Source-facing semantic target migrated from `theorem9_1_bid_independent_lower_boundSpec`. -/
def result_theorem9_1_bid_independent_lower_boundSpec : Prop :=
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

/-- Source-facing semantic target migrated from `lemma9_2_bid_independenceSpec`. -/
def result_lemma9_2_bid_independenceSpec : Prop :=
  by
    classical
    exact ∀ {Agent : Type*}
      (M : DigitalGoodsAuction Agent)
      (_htruth : truthful M)
      (_hIR : M.IndividuallyRational)
      (_hNPT : M.NoPositiveTransfers)
      (_hbinary : M.BinaryAllocation)
      (bids : Agent → ℝ) (i : Agent),
      DeterministicOfferBidIndependent (deterministicAuctionOffer M bids i)

/-- Source-facing semantic target migrated from `theorem9_3_deterministic_truthful_lower_boundSpec`. -/
def result_theorem9_3_deterministic_lower_boundSpec : Prop :=
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

/-- Source-facing semantic target for the bundled definition `definition_bounded_supply_fixed_price_benchmark`. -/
def definition_bounded_supply_fixed_price_benchmarkSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ), GHW01DigitalGoods.ProofBridge.source_boundedSupplyFk (Agent := Agent) (bids := bids) (capacity := capacity) = SourceDefinitions.boundedSupplyFk bids capacity)

/-- Source-facing semantic target for the bundled definition `definition_bounded_supply_top_k_total`. -/
def definition_bounded_supply_top_k_totalSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ) (capacity : ℕ)
    (hcapacity : capacity ≤ Fintype.card Agent), GHW01DigitalGoods.ProofBridge.source_boundedSupplyTk (Agent := Agent) (bids := bids) (capacity := capacity) (hcapacity := hcapacity) =
      by
        classical
        exact SourceDefinitions.boundedSupplyTk bids capacity hcapacity)

/-- Source-facing semantic target for the bundled definition `definition_bounded_supply_optimal_threshold`. -/
def definition_bounded_supply_optimal_thresholdSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ), GHW01DigitalGoods.ProofBridge.source_boundedSupplyOptK (Agent := Agent) (bids := bids) (capacity := capacity) = SourceDefinitions.boundedSupplyOptK bids capacity)

/-- Source-facing semantic target for the bundled definition `model_bounded_single_price_sampling_auction`. -/
def model_bounded_single_price_sampling_auctionSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < Fintype.card Agent) (capacity : ℕ), GHW01DigitalGoods.ProofBridge.source_boundedSinglePriceSampling (Agent := Agent) (sampleSize := sampleSize) (hsample_pos := hsample_pos) (hsample_lt := hsample_lt) (capacity := capacity) =
      by
        letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
        exact SourceDefinitions.boundedSinglePriceFixedSizeOutcomeLaw
          sampleSize hsample_pos hsample_lt capacity)

/-- Source-facing semantic target for the bundled definition `model_bounded_dual_price_sampling_auction`. -/
def model_bounded_dual_price_sampling_auctionSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (halfCapacity : ℕ), GHW01DigitalGoods.ProofBridge.source_boundedDualPriceSampling (Agent := Agent) (sampleSize := sampleSize) (hsample_pos := hsample_pos) (hhalf := hhalf) (halfCapacity := halfCapacity) =
      by
        letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
        exact SourceDefinitions.boundedDualExactHalfOutcomeLaw
          sampleSize hsample_pos hhalf halfCapacity)

/-- Source-facing semantic target for the bundled definition `definition_price_classes`. -/
def definition_price_classesSpec : Prop :=
  (∀ {Agent : Type*}
    (outcome : source_auctionOutcome Agent), GHW01DigitalGoods.ProofBridge.source_singlePriceOutcome (Agent := Agent) (outcome := outcome) = SourceDefinitions.AuctionOutcome.IsSinglePrice outcome) ∧
    (∀ {Agent : Type*}
    (auction : SourceDefinitions.DeterministicAuction Agent), GHW01DigitalGoods.ProofBridge.source_deterministicIsSinglePrice (Agent := Agent) (auction := auction) = SourceDefinitions.DeterministicIsSinglePrice auction) ∧
    (∀ {Agent : Type*}
    (auction : SourceDefinitions.RandomizedAuction Agent), GHW01DigitalGoods.ProofBridge.source_randomizedIsSinglePrice (Agent := Agent) (auction := auction) = SourceDefinitions.RandomizedIsSinglePrice auction) ∧
    (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_deterministicMultiPriceAuction (Agent := Agent) = SourceDefinitions.DeterministicAuction Agent) ∧
    (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_randomizedMultiPriceAuction (Agent := Agent) = SourceDefinitions.RandomizedAuction Agent)

/-- Source-facing semantic target for the bundled definition `definition_auction_correctness`. -/
def definition_auction_correctnessSpec : Prop :=
  (∀ {Agent : Type*}
    (auction : source_deterministicAuction Agent), GHW01DigitalGoods.ProofBridge.source_deterministicCorrect (Agent := Agent) (auction := auction) =
      by
        classical
        exact SourceDefinitions.DeterministicCorrect auction) ∧
    (∀ {Agent : Type*}
    (auction : source_randomizedAuction Agent), GHW01DigitalGoods.ProofBridge.source_randomizedCorrect (Agent := Agent) (auction := auction) =
      by
        classical
        exact SourceDefinitions.RandomizedCorrect auction)

/-- Source-facing semantic target for the bundled definition `model_unlimited_supply`. -/
def model_unlimited_supplySpec : Prop :=
  (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_unlimitedSupplyDeterministicAuction (Agent := Agent) = SourceDefinitions.UnlimitedSupplyDeterministicAuction Agent) ∧
    (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_unlimitedSupplyRandomizedAuction (Agent := Agent) = SourceDefinitions.UnlimitedSupplyRandomizedAuction Agent)

/-- Source-facing semantic target for the bundled definition `definition_fixed_pricing`. -/
def definition_fixed_pricingSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent]
    (bids : source_bidProfile Agent) (p : ℝ), GHW01DigitalGoods.ProofBridge.source_fixedPriceOutcome (Agent := Agent) (bids := bids) (p := p) = SourceDefinitions.fixedPriceOutcome bids p) ∧
    (∀ {Agent : Type*} [Fintype Agent]
    (p : ℝ), GHW01DigitalGoods.ProofBridge.source_fixedPriceAuction (Agent := Agent) (p := p) = SourceDefinitions.fixedPriceAuction p) ∧
    (∀ {Agent : Type*} [Fintype Agent]
    (bids : source_bidProfile Agent) (p : ℝ), GHW01DigitalGoods.ProofBridge.source_fixedPriceRevenue (Agent := Agent) (bids := bids) (p := p) = SourceDefinitions.fixedPriceRevenue bids p) ∧
    (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_optimalFixedPriceRevenue (Agent := Agent) (bids := bids) = SourceDefinitions.optimalFixedPriceRevenue bids) ∧
    (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_optimalThresholdDefinition (Agent := Agent) (bids := bids) = SourceDefinitions.optimalThreshold bids)

/-- Source-facing semantic target for the bundled definition `definition_bidder_count`. -/
def definition_bidder_countSpec : Prop :=
  (∀ (Agent : Type*) [Fintype Agent], GHW01DigitalGoods.ProofBridge.source_bidderCount (Agent := Agent) = SourceDefinitions.bidderCount Agent)

/-- Source-facing semantic target for the bundled definition `definition_bid_extrema`. -/
def definition_bid_extremaSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_lowestBid (Agent := Agent) (bids := bids) = SourceDefinitions.lowestBid bids) ∧
    (∀ {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_highestBid (Agent := Agent) (bids := bids) = SourceDefinitions.highestBid bids) ∧
    (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_normalizedBidScale (Agent := Agent) (bids := bids) = SourceDefinitions.NormalizedBidScale bids)

/-- Source-facing semantic target for the bundled definition `model_bidder_values_and_bids`. -/
def model_bidder_values_and_bidsSpec : Prop :=
  (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_bidValues (Agent := Agent) = SourceDefinitions.BidValues Agent) ∧
    (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_bidProfile (Agent := Agent) = SourceDefinitions.BidProfile Agent) ∧
    (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_auctionInput (Agent := Agent) = SourceDefinitions.AuctionInput Agent)

/-- Source-facing semantic target for the bundled definition `model_sorted_bid_convention`. -/
def model_sorted_bid_conventionSpec : Prop :=
  (∀ {n : ℕ}
    (bids : source_bidProfile (Fin n)), GHW01DigitalGoods.ProofBridge.source_sortedBidConvention (n := n) (bids := bids) = SourceDefinitions.SortedBids bids)

/-- Source-facing semantic target for the bundled definition `definition_auction_outcome`. -/
def definition_auction_outcomeSpec : Prop :=
  (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_auctionOutcome (Agent := Agent) = SourceDefinitions.AuctionOutcome Agent) ∧
    (∀ {Agent : Type*}
    (outcome : source_auctionOutcome Agent) (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_outcomeFillsAtOrBelow (Agent := Agent) (outcome := outcome) (bids := bids) = SourceDefinitions.AuctionOutcome.FillsAtOrBelow outcome bids)

/-- Source-facing semantic target for the bundled definition `definition_auction_mechanisms`. -/
def definition_auction_mechanismsSpec : Prop :=
  (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_deterministicAuction (Agent := Agent) = SourceDefinitions.DeterministicAuction Agent) ∧
    (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_randomizedAuction (Agent := Agent) = SourceDefinitions.RandomizedAuction Agent)

/-- Source-facing semantic target for the bundled definition `definition_bidder_profit`. -/
def definition_bidder_profitSpec : Prop :=
  (∀ {Agent : Type*}
    (outcome : source_auctionOutcome Agent) (values : source_bidValues Agent)
    (i : Agent), GHW01DigitalGoods.ProofBridge.source_profitDefinition (Agent := Agent) (outcome := outcome) (values := values) (i := i) =
      by
        classical
        exact SourceDefinitions.AuctionOutcome.profit outcome values i)

/-- Source-facing semantic target for the bundled definition `definition_performance_convention`. -/
def definition_performance_conventionSpec : Prop :=
  (∀ (auctionRevenue benchmark : ℝ), GHW01DigitalGoods.ProofBridge.source_performanceRatio (auctionRevenue := auctionRevenue) (benchmark := benchmark) = SourceDefinitions.performanceRatio auctionRevenue benchmark) ∧
    (∀ {Instance : Type*}
    (auctionRevenue benchmark : Instance → ℝ), GHW01DigitalGoods.ProofBridge.source_revenueBigOmega (Instance := Instance) (auctionRevenue := auctionRevenue) (benchmark := benchmark) = SourceDefinitions.RevenueBigOmega auctionRevenue benchmark) ∧
    (∀ {Instance : Type*}
    (auctionRevenue benchmark : Instance → ℝ), GHW01DigitalGoods.ProofBridge.source_revenueBigO (Instance := Instance) (auctionRevenue := auctionRevenue) (benchmark := benchmark) = SourceDefinitions.RevenueBigO auctionRevenue benchmark)

/-- Source-facing semantic target for the bundled definition `definition_scale_conditions`. -/
def definition_scale_conditionsSpec : Prop :=
  (∀ (alpha highest fixedPrice : ℝ), GHW01DigitalGoods.ProofBridge.source_fixedPriceScaleCondition (alpha := alpha) (highest := highest) (fixedPrice := fixedPrice) = SourceDefinitions.fixedPriceScaleCondition alpha highest fixedPrice) ∧
    (∀ (alpha highest total : ℝ), GHW01DigitalGoods.ProofBridge.source_totalValueScaleCondition (alpha := alpha) (highest := highest) (total := total) = SourceDefinitions.totalValueScaleCondition alpha highest total) ∧
    (∀ (alpha : ℝ), GHW01DigitalGoods.ProofBridge.source_positiveAlpha (alpha := alpha) = SourceDefinitions.PositiveAlpha alpha)

/-- Source-facing semantic target for the bundled definition `definition_competitive_auction`. -/
def definition_competitive_auctionSpec : Prop :=
  (∀ {Instance : Type*}
    (admissible : Instance → Prop) (auctionRevenue benchmark : Instance → ℝ), GHW01DigitalGoods.ProofBridge.source_competitiveDefinition (Instance := Instance) (admissible := admissible) (auctionRevenue := auctionRevenue) (benchmark := benchmark) = SourceDefinitions.CompetitiveOn admissible auctionRevenue benchmark) ∧
    (∀ {Instance : Type*} (admissible : Instance → Prop)
    (auctionRevenue benchmark : Instance → ℝ)
    (hbenchmark_pos : ∀ x, admissible x → 0 < benchmark x), source_competitiveDefinition admissible auctionRevenue benchmark ↔   ∃ c : ℝ, 0 < c ∧ ∀ x, admissible x →     c ≤ source_performanceRatio (auctionRevenue x) (benchmark x))

/-- Source-facing semantic target for the bundled definition `definition_k_item_vickrey`. -/
def definition_k_item_vickreySpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent]
    (auction : source_deterministicAuction Agent) (k : ℕ), GHW01DigitalGoods.ProofBridge.source_kItemVickreyAuction (Agent := Agent) (auction := auction) (k := k) =
      by
        classical
        exact SourceDefinitions.IsKItemVickreyAuction auction k)

/-- Source-facing semantic target for the bundled definition `definition_unlimited_vickrey_family`. -/
def definition_unlimited_vickrey_familySpec : Prop :=
  (∀ (f : ℕ → ℕ), GHW01DigitalGoods.ProofBridge.source_admissibleVickreySupplyRule (f := f) = SourceDefinitions.AdmissibleVickreySupplyRule f)

/-- Source-facing semantic target for the bundled definition `definition_optimal_threshold`. -/
def definition_optimal_thresholdSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent) (p : ℝ), GHW01DigitalGoods.ProofBridge.source_isOptimalThreshold (Agent := Agent) (bids := bids) (p := p) = SourceDefinitions.IsOptimalThreshold bids p) ∧
    (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_optimalThresholdDefinition (Agent := Agent) (bids := bids) = SourceDefinitions.optimalThreshold bids) ∧
    (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_optimalSinglePriceOutcome (Agent := Agent) (bids := bids) = SourceDefinitions.optimalSinglePriceOutcome bids) ∧
    (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent], GHW01DigitalGoods.ProofBridge.source_optimalSinglePriceAuction (Agent := Agent) = SourceDefinitions.optimalSinglePriceAuction)

/-- Source-facing semantic target for the bundled definition `definition_bid_independent_auction`. -/
def definition_bid_independent_auctionSpec : Prop :=
  (GHW01DigitalGoods.ProofBridge.source_thresholdOffer = SourceDefinitions.ThresholdOffer) ∧
    (∀ (offer : source_thresholdOffer) (bid : ℝ), GHW01DigitalGoods.ProofBridge.source_acceptsThreshold (offer := offer) (bid := bid) = SourceDefinitions.accepts offer bid) ∧
    (∀ {Agent : Type*} [Fintype Agent]
    (bids : source_bidProfile Agent) (i : Agent), GHW01DigitalGoods.ProofBridge.source_otherBids (Agent := Agent) (bids := bids) (i := i) =
      by
        classical
        exact SourceDefinitions.otherBids bids i) ∧
    (GHW01DigitalGoods.ProofBridge.source_bidIndependentRule = SourceDefinitions.BidIndependentRule) ∧
    (∀ {Agent : Type*}
    [Fintype Agent]
    (rule : source_bidIndependentRule) (bids : source_bidProfile Agent), GHW01DigitalGoods.ProofBridge.source_bidIndependentOutcome (Agent := Agent) (rule := rule) (bids := bids) =
      by
        classical
        exact SourceDefinitions.bidIndependentOutcome rule bids) ∧
    (∀ {Agent : Type*}
    [Fintype Agent]
    (rule : source_bidIndependentRule), GHW01DigitalGoods.ProofBridge.source_bidIndependentAuction (Agent := Agent) (rule := rule) =
      by
        classical
        exact SourceDefinitions.bidIndependentAuction rule)

/-- Source-facing semantic target for the bundled definition `definition_threshold_boundary_convention`. -/
def definition_threshold_boundary_conventionSpec : Prop :=
  (GHW01DigitalGoods.ProofBridge.source_thresholdBoundaryConvention = SourceDefinitions.ThresholdBoundary)

/-- Source-facing semantic target for the bundled definition `definition_random_sampling_auction`. -/
def definition_random_sampling_auctionSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent]
    (plan : source_randomSamplingPlan Agent), GHW01DigitalGoods.ProofBridge.source_randomSamplingAuction (Agent := Agent) (plan := plan) =
      by
        classical
        exact plan.directionalOutcomeLaw)

/-- Source-facing semantic target for the bundled definition `definition_dual_price_sampling_auction`. -/
def definition_dual_price_sampling_auctionSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent]
    (plan : source_randomSamplingPlan Agent), GHW01DigitalGoods.ProofBridge.source_dualPriceRandomSamplingAuction (Agent := Agent) (plan := plan) =
      by
        classical
        exact plan.dualPriceOutcomeLaw)

/-- Source-facing semantic target for the bundled definition `definition_exact_half_optimal_threshold`. -/
def definition_exact_half_optimal_thresholdSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (boundary : source_thresholdBoundaryConvention), GHW01DigitalGoods.ProofBridge.source_exactHalfOptimalThresholdAuction (Agent := Agent) (sampleSize := sampleSize) (hsample_pos := hsample_pos) (hhalf := hhalf) (boundary := boundary) =
      by
        classical
        letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
        exact SourceDefinitions.exactHalfOptimalThresholdOutcomeLaw
          sampleSize hsample_pos hhalf boundary)

/-- Source-facing semantic target for the bundled definition `definition_independent_half_analysis_model`. -/
def definition_independent_half_analysis_modelSpec : Prop :=
  (∀ (Agent : Type*), GHW01DigitalGoods.ProofBridge.source_independentHalfSamplingAnalysisLaw (Agent := Agent) = SourceDefinitions.independentHalfSamplingAnalysisLaw Agent)

/-- Source-facing semantic target for the bundled definition `definition_weighted_pairing_auction`. -/
def definition_weighted_pairing_auctionSpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i), GHW01DigitalGoods.ProofBridge.source_weightedPairingAuction (Agent := Agent) (bids := bids) (hbid_ge_one := hbid_ge_one) (hdistinct := hdistinct) =
      by
        classical
        exact SourceDefinitions.weightedPairingOutcomeLaw bids
          (weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
            bids hbid_ge_one hdistinct))

/-- Source-facing semantic target for the bundled definition `definition_deterministic_optimal_threshold_auction`. -/
def definition_deterministic_optimal_threshold_auctionSpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent]
    (hcard : 2 ≤ Fintype.card Agent), GHW01DigitalGoods.ProofBridge.source_deterministicOptimalThresholdAuction (Agent := Agent) (hcard := hcard) =
      by
        classical
        letI : Nonempty Agent := Fintype.card_pos_iff.mp (by omega)
        exact SourceDefinitions.deterministicOptimalThresholdAuction hcard)

/-- Source-facing semantic target for the bundled definition `model_bounded_supply_capacity`. -/
def model_bounded_supply_capacitySpec : Prop :=
  (∀ {Agent : Type*} [Fintype Agent]
    (auction : DigitalGoodsAuction Agent) (capacity : ℕ), GHW01DigitalGoods.ProofBridge.source_boundedSupplyModel (Agent := Agent) (auction := auction) (capacity := capacity) = SourceDefinitions.IsKItemBoundedSupplyAuction auction capacity)

/-- Source-facing semantic target for the bundled definition `definition_scarce_supply`. -/
def definition_scarce_supplySpec : Prop :=
  (∀ {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ), GHW01DigitalGoods.ProofBridge.source_scarceSupply (Agent := Agent) (bids := bids) (capacity := capacity) = SourceDefinitions.scarceSupply bids capacity)

end

end PaperInterface
end GHW01DigitalGoods
