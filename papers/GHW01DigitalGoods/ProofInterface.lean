import GHW01DigitalGoods.PaperInterface

import GHW01DigitalGoods.ProofBridge



namespace GHW01DigitalGoods

namespace PaperInterface

open AppliedModelingLib.Auction
open scoped BigOperators
open GHW01DigitalGoods.ProofBridge
noncomputable section

theorem definition_revenue_realizes_spec : definition_revenueSpec := by
  unfold definition_revenueSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩

theorem definition_truthfulness_realizes_spec : definition_truthfulnessSpec := by
  unfold definition_truthfulnessSpec
  exact ⟨by intros; rfl, by intros; rfl⟩

theorem definition_fixed_price_benchmark_realizes_spec : definition_fixed_price_benchmarkSpec := by
  unfold definition_fixed_price_benchmarkSpec
  exact by intros; rfl

theorem definition_total_value_realizes_spec : definition_total_valueSpec := by
  unfold definition_total_valueSpec
  exact ⟨by intros; rfl, by intro Agent _ input htruth; exact GHW01DigitalGoods.ProofBridge.source_truthfulReports_totalValue_bridge (Agent := Agent) (input := input) (htruth := htruth)⟩

theorem definition_weighted_pairing_revenue_realizes_spec : definition_weighted_pairing_revenueSpec := by
  unfold definition_weighted_pairing_revenueSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, by intro Agent _ bids hbid_ge_one hdistinct; exact GHW01DigitalGoods.ProofBridge.source_weightedPairingOutcomeExpectedRevenue_eq_W (Agent := Agent) (bids := bids) (hbid_ge_one := hbid_ge_one) (hdistinct := hdistinct)⟩⟩

theorem result_theorem4_1 : result_theorem4_1Spec := by
  exact GHW01DigitalGoods.ProofBridge.theorem4_1_high_value

theorem result_corollary4_2 : result_corollary4_2Spec := by
  exact GHW01DigitalGoods.ProofBridge.corollary4_2_fixed_price_lower_bound

theorem result_lemma6_1_fixed_size_lower_tail : result_lemma6_1_fixed_size_lower_tailSpec := by
  exact GHW01DigitalGoods.ProofBridge.lemma6_1_fixed_size

theorem result_theorem6_2_random_sampling : result_theorem6_2_random_samplingSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem6_2_random_sampling

theorem result_theorem7_1_weighted_pairing : result_theorem7_1_weighted_pairingSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem7_1_weighted_pairing

theorem result_theorem7_2_lower_bound : result_theorem7_2_lower_boundSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem7_2_weighted_pairing_benchmark

theorem result_theorem7_2_tightness : result_theorem7_2_tightnessSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem7_2_weighted_pairing_tightness_selected_sqrt_log

theorem result_lemma8_1_monotone_allocation : result_lemma8_1_monotone_allocationSpec := by
  exact GHW01DigitalGoods.ProofBridge.lemma8_1_truthful_monotone

theorem result_theorem8_2_journal_revenue_upper_bound : result_theorem8_2_journal_revenue_upper_boundSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem8_2_truthful_revenue_upper_bound

theorem result_theorem9_1_bid_independent_lower_bound : result_theorem9_1_bid_independent_lower_boundSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem9_1_bid_independent_lower_bound

theorem result_lemma9_2_bid_independence : result_lemma9_2_bid_independenceSpec := by
  exact GHW01DigitalGoods.ProofBridge.lemma9_2_bid_independence

theorem result_theorem9_3_deterministic_lower_bound : result_theorem9_3_deterministic_lower_boundSpec := by
  exact GHW01DigitalGoods.ProofBridge.theorem9_3_deterministic_truthful_lower_bound

theorem definition_bounded_supply_fixed_price_benchmark_realizes_spec : definition_bounded_supply_fixed_price_benchmarkSpec := by
  unfold definition_bounded_supply_fixed_price_benchmarkSpec
  exact by intros; rfl

theorem definition_bounded_supply_top_k_total_realizes_spec : definition_bounded_supply_top_k_totalSpec := by
  unfold definition_bounded_supply_top_k_totalSpec
  exact by intros; rfl

theorem definition_bounded_supply_optimal_threshold_realizes_spec : definition_bounded_supply_optimal_thresholdSpec := by
  unfold definition_bounded_supply_optimal_thresholdSpec
  exact by intros; rfl

theorem model_bounded_single_price_sampling_auction_realizes_spec : model_bounded_single_price_sampling_auctionSpec := by
  unfold model_bounded_single_price_sampling_auctionSpec
  exact by intros; rfl

theorem model_bounded_dual_price_sampling_auction_realizes_spec : model_bounded_dual_price_sampling_auctionSpec := by
  unfold model_bounded_dual_price_sampling_auctionSpec
  exact by intros; rfl

theorem definition_price_classes_realizes_spec : definition_price_classesSpec := by
  unfold definition_price_classesSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩⟩⟩

theorem definition_auction_correctness_realizes_spec : definition_auction_correctnessSpec := by
  unfold definition_auction_correctnessSpec
  exact ⟨by intros; rfl, by intros; rfl⟩

theorem model_unlimited_supply_realizes_spec : model_unlimited_supplySpec := by
  unfold model_unlimited_supplySpec
  exact ⟨by intros; rfl, by intros; rfl⟩

theorem definition_fixed_pricing_realizes_spec : definition_fixed_pricingSpec := by
  unfold definition_fixed_pricingSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩⟩⟩

theorem definition_bidder_count_realizes_spec : definition_bidder_countSpec := by
  unfold definition_bidder_countSpec
  exact by intros; rfl

theorem definition_bid_extrema_realizes_spec : definition_bid_extremaSpec := by
  unfold definition_bid_extremaSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩

theorem model_bidder_values_and_bids_realizes_spec : model_bidder_values_and_bidsSpec := by
  unfold model_bidder_values_and_bidsSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩

theorem model_sorted_bid_convention_realizes_spec : model_sorted_bid_conventionSpec := by
  unfold model_sorted_bid_conventionSpec
  exact by intros; rfl

theorem definition_auction_outcome_realizes_spec : definition_auction_outcomeSpec := by
  unfold definition_auction_outcomeSpec
  exact ⟨by intros; rfl, by intros; rfl⟩

theorem definition_auction_mechanisms_realizes_spec : definition_auction_mechanismsSpec := by
  unfold definition_auction_mechanismsSpec
  exact ⟨by intros; rfl, by intros; rfl⟩

theorem definition_bidder_profit_realizes_spec : definition_bidder_profitSpec := by
  unfold definition_bidder_profitSpec
  exact by intros; rfl

theorem definition_performance_convention_realizes_spec : definition_performance_conventionSpec := by
  unfold definition_performance_conventionSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩

theorem definition_scale_conditions_realizes_spec : definition_scale_conditionsSpec := by
  unfold definition_scale_conditionsSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩

theorem definition_competitive_auction_realizes_spec : definition_competitive_auctionSpec := by
  unfold definition_competitive_auctionSpec
  exact ⟨by intros; rfl, by intro Instance admissible auctionRevenue benchmark hbenchmark_pos; exact GHW01DigitalGoods.ProofBridge.source_competitive_iff_uniformPositiveRevenueBenchmarkRatio (Instance := Instance) (admissible := admissible) (auctionRevenue := auctionRevenue) (benchmark := benchmark) (hbenchmark_pos := hbenchmark_pos)⟩

theorem definition_k_item_vickrey_realizes_spec : definition_k_item_vickreySpec := by
  unfold definition_k_item_vickreySpec
  exact by intros; rfl

theorem definition_unlimited_vickrey_family_realizes_spec : definition_unlimited_vickrey_familySpec := by
  unfold definition_unlimited_vickrey_familySpec
  exact by intros; rfl

theorem definition_optimal_threshold_realizes_spec : definition_optimal_thresholdSpec := by
  unfold definition_optimal_thresholdSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩⟩

theorem definition_bid_independent_auction_realizes_spec : definition_bid_independent_auctionSpec := by
  unfold definition_bid_independent_auctionSpec
  exact ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, ⟨by intros; rfl, by intros; rfl⟩⟩⟩⟩⟩

theorem definition_threshold_boundary_convention_realizes_spec : definition_threshold_boundary_conventionSpec := by
  unfold definition_threshold_boundary_conventionSpec
  exact by intros; rfl

theorem definition_random_sampling_auction_realizes_spec : definition_random_sampling_auctionSpec := by
  unfold definition_random_sampling_auctionSpec
  exact by intros; rfl

theorem definition_dual_price_sampling_auction_realizes_spec : definition_dual_price_sampling_auctionSpec := by
  unfold definition_dual_price_sampling_auctionSpec
  exact by intros; rfl

theorem definition_exact_half_optimal_threshold_realizes_spec : definition_exact_half_optimal_thresholdSpec := by
  unfold definition_exact_half_optimal_thresholdSpec
  exact by intros; rfl

theorem definition_independent_half_analysis_model_realizes_spec : definition_independent_half_analysis_modelSpec := by
  unfold definition_independent_half_analysis_modelSpec
  exact by intros; rfl

theorem definition_weighted_pairing_auction_realizes_spec : definition_weighted_pairing_auctionSpec := by
  unfold definition_weighted_pairing_auctionSpec
  exact by intros; rfl

theorem definition_deterministic_optimal_threshold_auction_realizes_spec : definition_deterministic_optimal_threshold_auctionSpec := by
  unfold definition_deterministic_optimal_threshold_auctionSpec
  exact by intros; rfl

theorem model_bounded_supply_capacity_realizes_spec : model_bounded_supply_capacitySpec := by
  unfold model_bounded_supply_capacitySpec
  exact by intros; rfl

theorem definition_scarce_supply_realizes_spec : definition_scarce_supplySpec := by
  unfold definition_scarce_supplySpec
  exact by intros; rfl

end

end PaperInterface
end GHW01DigitalGoods
