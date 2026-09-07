import GHW01DigitalGoods.AuctionMainTheorems
import GHW01DigitalGoods.FixedSizeSampling
import AppliedModelingLib.Foundations.Probability.OrderStatistics

/-!
# Bounded-supply digital-goods auctions

This file formalizes Section 11 of Goldberg--Hartline--Wright.  It keeps the
bounded benchmark and the capped sampling constructions separate from the
unlimited-supply core.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib
open AppliedModelingLib.Auction
open scoped BigOperators

noncomputable section

/-! ## Bounded benchmarks -/

/-- Revenue from price `p` when at most `capacity` units may be sold. -/
def boundedSupplySinglePriceRevenue {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (capacity : ℕ) (p : ℝ) : ℝ :=
  (min capacity (saleCount values p) : ℝ) * p

/-- Candidate bounded-supply revenue at bidder `i`'s value. -/
def candidateBoundedSupplyRevenue {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (capacity : ℕ) (i : Agent) : ℝ :=
  if 0 ≤ values i then
    boundedSupplySinglePriceRevenue values capacity (values i)
  else
    0

/-- Section 11's `F_k`: optimal fixed-price revenue selling at most `k` units. -/
def boundedSupplyFixedPriceBenchmark {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    (candidateBoundedSupplyRevenue values capacity)

theorem boundedSupplySinglePriceRevenue_nonneg
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (capacity : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ boundedSupplySinglePriceRevenue values capacity p := by
  exact mul_nonneg (by positivity) hp

theorem candidateBoundedSupplyRevenue_nonneg
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (capacity : ℕ) (i : Agent) :
    0 ≤ candidateBoundedSupplyRevenue values capacity i := by
  by_cases hi : 0 ≤ values i
  · simp [candidateBoundedSupplyRevenue, hi,
      boundedSupplySinglePriceRevenue_nonneg values capacity hi]
  · simp [candidateBoundedSupplyRevenue, hi]

theorem candidateBoundedSupplyRevenue_le_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) (i : Agent) :
    candidateBoundedSupplyRevenue values capacity i ≤
      boundedSupplyFixedPriceBenchmark values capacity := by
  unfold boundedSupplyFixedPriceBenchmark
  exact Finset.le_sup'
    (s := (Finset.univ : Finset Agent))
    (f := candidateBoundedSupplyRevenue values capacity)
    (b := i) (by simp)

theorem boundedSupplyFixedPriceBenchmark_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    0 ≤ boundedSupplyFixedPriceBenchmark values capacity := by
  obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
  exact (candidateBoundedSupplyRevenue_nonneg values capacity i).trans
    (candidateBoundedSupplyRevenue_le_benchmark values capacity i)

/-- Every nonnegative posted price is dominated by the finite candidate-price
benchmark.  Choosing the least bid that accepts `p` preserves the buyer count
and can only raise the per-unit price. -/
theorem boundedSupplySinglePriceRevenue_le_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    boundedSupplySinglePriceRevenue values capacity p ≤
      boundedSupplyFixedPriceBenchmark values capacity := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  by_cases hwinners : winners.Nonempty
  · obtain ⟨i, hi, hmin⟩ :=
      Finset.exists_min_image winners values hwinners
    have hpi : p ≤ values i := (Finset.mem_filter.mp hi).2
    have hsame : saleCount values (values i) = saleCount values p := by
      unfold saleCount
      apply congrArg Finset.card
      ext j
      constructor
      · intro hj
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hj).1, hpi.trans (Finset.mem_filter.mp hj).2⟩
      · intro hj
        have hjw : j ∈ winners := by
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hj).1, hmin j hjw⟩
    calc
      boundedSupplySinglePriceRevenue values capacity p ≤
          boundedSupplySinglePriceRevenue values capacity (values i) := by
        unfold boundedSupplySinglePriceRevenue
        rw [hsame]
        exact mul_le_mul_of_nonneg_left hpi (by positivity)
      _ = candidateBoundedSupplyRevenue values capacity i := by
        have hi_nonneg : 0 ≤ values i := hp.trans hpi
        simp [candidateBoundedSupplyRevenue, hi_nonneg]
      _ ≤ boundedSupplyFixedPriceBenchmark values capacity :=
        candidateBoundedSupplyRevenue_le_benchmark values capacity i
  · have hcount : saleCount values p = 0 := by
      unfold saleCount
      change winners.card = 0
      simp [Finset.not_nonempty_iff_eq_empty.mp hwinners]
    simp [boundedSupplySinglePriceRevenue, hcount,
      boundedSupplyFixedPriceBenchmark_nonneg values capacity]

theorem exists_boundedSupplyBenchmarkBidder
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    ∃ i : Agent,
      boundedSupplyFixedPriceBenchmark values capacity =
        candidateBoundedSupplyRevenue values capacity i := by
  classical
  let H : (Finset.univ : Finset Agent).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
    exact ⟨i, by simp⟩
  obtain ⟨i, hi, hmax⟩ :=
    (Finset.univ : Finset Agent).exists_mem_eq_sup'
      (f := candidateBoundedSupplyRevenue values capacity) H
  exact ⟨i, hmax⟩

/-- A bidder attaining `F_k`. -/
def boundedSupplyBenchmarkBidder {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) : Agent :=
  Classical.choose (exists_boundedSupplyBenchmarkBidder values capacity)

/-- Section 11's `opt_k`: a benchmark-attaining nonnegative threshold. -/
def boundedSupplyOptimalThreshold {Agent : Type*}
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) : ℝ :=
  let i := boundedSupplyBenchmarkBidder values capacity
  if 0 ≤ values i then values i else 0

theorem boundedSupplyOptimalThreshold_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    0 ≤ boundedSupplyOptimalThreshold values capacity := by
  classical
  let i := boundedSupplyBenchmarkBidder values capacity
  by_cases hi : 0 ≤ values i
  · simp [boundedSupplyOptimalThreshold, i, hi]
  · simp [boundedSupplyOptimalThreshold, i, hi]

theorem boundedSupplyOptimalThreshold_revenue_eq_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (capacity : ℕ) :
    boundedSupplySinglePriceRevenue values capacity
        (boundedSupplyOptimalThreshold values capacity) =
      boundedSupplyFixedPriceBenchmark values capacity := by
  classical
  let i := boundedSupplyBenchmarkBidder values capacity
  have hselected :
      boundedSupplyFixedPriceBenchmark values capacity =
        candidateBoundedSupplyRevenue values capacity i :=
    Classical.choose_spec
      (exists_boundedSupplyBenchmarkBidder values capacity)
  by_cases hi : 0 ≤ values i
  · rw [hselected]
    simp [boundedSupplyOptimalThreshold, candidateBoundedSupplyRevenue, i, hi]
  · have hbench_zero : boundedSupplyFixedPriceBenchmark values capacity = 0 := by
      rw [hselected]
      simp [candidateBoundedSupplyRevenue, hi]
    rw [hbench_zero]
    simp [boundedSupplyOptimalThreshold, i, hi,
      boundedSupplySinglePriceRevenue]

/-- Internal finite representation of the sum of the highest at most `k`
bids.  The paper-facing `T_k` endpoint below identifies this with the exact
`k`-bid sum on the source domain of nonnegative bids and `k ≤ n`. -/
def boundedSupplyTopKTotal {Agent : Type*}
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) : ℝ :=
  AppliedModelingLib.Probability.topKSumOn capacity values

/-- On the source domain for Section 11, the library's convenient
at-most-`k` representation is exactly the paper's sum of the highest `k`
bids.  Any smaller candidate set extends to a `k`-set, and nonnegative added
bids cannot decrease its sum. -/
theorem boundedSupplyTopKTotal_eq_exact_cardinality_of_nonneg
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ)
    (hcapacity : capacity ≤ Fintype.card Agent)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i) :
    boundedSupplyTopKTotal values capacity =
      ((Finset.univ : Finset Agent).powerset.filter fun s =>
        s.card = capacity).sup'
        (by
          obtain ⟨s, hs_sub, hs_card⟩ :=
            Finset.exists_subset_card_eq
              (s := (Finset.univ : Finset Agent)) hcapacity
          exact ⟨s, Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr hs_sub, hs_card⟩⟩)
        (fun s => ∑ i ∈ s, values i) := by
  classical
  let atMost : Finset (Finset Agent) :=
    (Finset.univ : Finset Agent).powerset.filter fun s => s.card ≤ capacity
  let exact : Finset (Finset Agent) :=
    (Finset.univ : Finset Agent).powerset.filter fun s => s.card = capacity
  have hatMost_nonempty : atMost.Nonempty := by
    exact AppliedModelingLib.Probability.topKCandidateSets_nonempty Agent capacity
  have hexact_nonempty : exact.Nonempty := by
    obtain ⟨s, hs_sub, hs_card⟩ :=
      Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset Agent)) hcapacity
    exact ⟨s, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hs_sub, hs_card⟩⟩
  change atMost.sup' hatMost_nonempty (fun s => ∑ i ∈ s, values i) =
    exact.sup' hexact_nonempty (fun s => ∑ i ∈ s, values i)
  apply le_antisymm
  · refine Finset.sup'_le hatMost_nonempty _ ?_
    intro s hs
    have hs_card : s.card ≤ capacity := by
      simpa [atMost] using (Finset.mem_filter.mp hs).2
    obtain ⟨t, hst, ht_univ, ht_card⟩ :=
      Finset.exists_subsuperset_card_eq (s := s)
        (t := (Finset.univ : Finset Agent)) (by simp) hs_card hcapacity
    have hsum : (∑ i ∈ s, values i) ≤ ∑ i ∈ t, values i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hst ?_
      intro i _ _
      exact hvalues_nonneg i
    exact hsum.trans (Finset.le_sup' (fun t => ∑ i ∈ t, values i)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ht_univ, ht_card⟩))
  · refine Finset.sup'_le hexact_nonempty _ ?_
    intro s hs
    have hs_card : s.card ≤ capacity := by
      exact (Finset.mem_filter.mp hs).2.le
    exact Finset.le_sup' (fun s => ∑ i ∈ s, values i)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (by simp), hs_card⟩)

theorem saleCount_on_finset_le_saleCount
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (s : Finset Agent) (p : ℝ) :
    saleCount (fun i : ↑s => values i) p ≤ saleCount values p := by
  classical
  let source : Finset ↑s :=
    (Finset.univ : Finset ↑s).filter fun i => p ≤ values i
  let target : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  let embedded : Finset Agent := source.map (Function.Embedding.subtype _)
  have hsubset : embedded ⊆ target := by
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hj).2⟩
  have hcard := Finset.card_le_card hsubset
  simpa [saleCount, source, target, embedded] using hcard

theorem singlePriceRevenue_on_finset_le_boundedSupply
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) (s : Finset Agent)
    (hs : s.card ≤ capacity) {p : ℝ} (hp : 0 ≤ p) :
    singlePriceRevenue (fun i : ↑s => values i) p ≤
      boundedSupplySinglePriceRevenue values capacity p := by
  rw [singlePriceRevenue_eq_saleCount_mul]
  unfold boundedSupplySinglePriceRevenue
  have hsub_card : saleCount (fun i : ↑s => values i) p ≤ s.card := by
    simpa using saleCount_le_card (fun i : ↑s => values i) p
  have hsub_capacity : saleCount (fun i : ↑s => values i) p ≤ capacity :=
    hsub_card.trans hs
  have hsub_total := saleCount_on_finset_le_saleCount values s p
  have hcount :
      saleCount (fun i : ↑s => values i) p ≤
        min capacity (saleCount values p) :=
    le_min hsub_capacity hsub_total
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hp

theorem finiteCandidateBenchmark_on_finset_le_boundedSupplyBenchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) (s : Finset Agent) [Nonempty ↑s]
    (hs_nonempty : s.Nonempty) (hs : s.card ≤ capacity) :
    finiteCandidateFixedPriceBenchmark (fun i : ↑s => values i) 1 ≤
      boundedSupplyFixedPriceBenchmark values capacity := by
  classical
  obtain ⟨i, hi⟩ :=
    exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
      (fun i : ↑s => values i) 1
  rw [hi]
  by_cases hfeasible :
      0 ≤ values i ∧ 1 ≤ saleCount (fun j : ↑s => values j) (values i)
  · rw [candidateFixedPriceRevenue]
    simp only [hfeasible]
    apply (singlePriceRevenue_on_finset_le_boundedSupply
      values capacity s hs hfeasible.1).trans
    simpa [candidateBoundedSupplyRevenue, hfeasible.1] using
      (candidateBoundedSupplyRevenue_le_benchmark values capacity (i : Agent))
  · rw [candidateFixedPriceRevenue]
    simp only [hfeasible, if_false]
    exact boundedSupplyFixedPriceBenchmark_nonneg values capacity

/-- Rounded dyadic bounded-supply auxiliary bound, retained separately from
the corrected exact Section 11 endpoint below. -/
theorem boundedSupplyFixedPriceBenchmark_ge_topK
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) {h : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    boundedSupplyTopKTotal values capacity ≤
      (2 * (Real.logb 2 h + 2)) *
        boundedSupplyFixedPriceBenchmark values capacity := by
  classical
  let candidates := AppliedModelingLib.Probability.topKCandidateSets Agent capacity
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    candidates.exists_mem_eq_sup'
      (AppliedModelingLib.Probability.topKCandidateSets_nonempty Agent capacity)
      (fun s => ∑ i ∈ s, values i)
  have hs_card : s.card ≤ capacity := by
    simpa [candidates, AppliedModelingLib.Probability.topKCandidateSets] using hs_mem
  rw [boundedSupplyTopKTotal, AppliedModelingLib.Probability.topKSumOn]
  change candidates.sup' _ (fun s => ∑ i ∈ s, values i) ≤ _
  rw [hs_eq]
  by_cases hs_nonempty : s.Nonempty
  · letI : Nonempty ↑s := Finset.nonempty_coe_sort.mpr hs_nonempty
    have hpaper :=
      paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value
        (fun i : ↑s => values i) hh_ge_one
        (fun i => hvalue_ge_one i) (fun i => hvalue_le_h i)
    have hsum :
        (∑ i ∈ s, values i) =
          totalBidValue (fun i : ↑s => values i) := by
      simpa [totalBidValue] using (Finset.sum_attach s values).symm
    rw [hsum]
    exact hpaper.trans (mul_le_mul_of_nonneg_left
      (finiteCandidateBenchmark_on_finset_le_boundedSupplyBenchmark
        values capacity s hs_nonempty hs_card)
      (by
        have hlog : 0 ≤ Real.logb 2 h :=
          Real.logb_nonneg (b := 2) (by norm_num) hh_ge_one
        positivity))
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_nonempty
    subst s
    simp only [Finset.sum_empty]
    exact mul_nonneg
      (by
        have hlog : 0 ≤ Real.logb 2 h :=
          Real.logb_nonneg (b := 2) (by norm_num) hh_ge_one
        positivity)
      (boundedSupplyFixedPriceBenchmark_nonneg values capacity)

/--
Corrected exact Section 11 extension of Theorem 4.1.  The real-log factor is
valid on the same repaired domain `2 <= h` as the one-winner result.
-/
theorem boundedSupplyFixedPriceBenchmark_ge_topK_exact_logb_of_two_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (capacity : ℕ) {h : ℝ}
    (hh_ge_two : 2 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    boundedSupplyTopKTotal values capacity ≤
      (2 * Real.logb 2 h) *
        boundedSupplyFixedPriceBenchmark values capacity := by
  classical
  let candidates := AppliedModelingLib.Probability.topKCandidateSets Agent capacity
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    candidates.exists_mem_eq_sup'
      (AppliedModelingLib.Probability.topKCandidateSets_nonempty Agent capacity)
      (fun s => ∑ i ∈ s, values i)
  have hs_card : s.card ≤ capacity := by
    simpa [candidates, AppliedModelingLib.Probability.topKCandidateSets] using hs_mem
  rw [boundedSupplyTopKTotal, AppliedModelingLib.Probability.topKSumOn]
  change candidates.sup' _ (fun s => ∑ i ∈ s, values i) ≤ _
  rw [hs_eq]
  by_cases hs_nonempty : s.Nonempty
  · letI : Nonempty ↑s := Finset.nonempty_coe_sort.mpr hs_nonempty
    have hpaper :=
      paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
        (fun i : ↑s => values i) hh_ge_two
        (fun i => hvalue_ge_one i) (fun i => hvalue_le_h i)
    have hsum :
        (∑ i ∈ s, values i) =
          totalBidValue (fun i : ↑s => values i) := by
      simpa [totalBidValue] using (Finset.sum_attach s values).symm
    rw [hsum]
    exact hpaper.trans (mul_le_mul_of_nonneg_left
      (finiteCandidateBenchmark_on_finset_le_boundedSupplyBenchmark
        values capacity s hs_nonempty hs_card)
      (by
        have hlog : 0 ≤ Real.logb 2 h :=
          Real.logb_nonneg (b := 2) (by norm_num) (by linarith)
        positivity))
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_nonempty
    subst s
    simp only [Finset.sum_empty]
    exact mul_nonneg
      (by
        have hlog : 0 ≤ Real.logb 2 h :=
          Real.logb_nonneg (b := 2) (by norm_num) (by linarith)
        positivity)
      (boundedSupplyFixedPriceBenchmark_nonneg values capacity)

/-! ## Priority capping and bounded-supply threshold auctions -/

/-- Bidders on `marketSide` whose reports accept `price`. -/
def boundedEligible
    {Agent : Type*} (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (price : ℝ) (i : Agent) : Prop :=
  side i = marketSide ∧ price ≤ bids i

/-- Number of eligible bidders preceding `i` in a fixed priority order. -/
noncomputable def earlierBoundedEligibleCount
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (price : ℝ) (i : Agent) : ℕ := by
  classical
  exact ((Finset.univ : Finset Agent).filter fun j =>
    boundedEligible side marketSide bids price j ∧ j < i).card

/-- Fixed-priority capping: accept an eligible bidder exactly when fewer than
`capacity` earlier eligible bidders exist. -/
def boundedCappedWinner
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (price : ℝ) (capacity : ℕ) (i : Agent) : Prop :=
  boundedEligible side marketSide bids price i ∧
    earlierBoundedEligibleCount side marketSide bids price i < capacity

/-- A capped posted-threshold auction.  The price rule may inspect the whole
profile; truthfulness below requires own-report independence on the market
side. -/
noncomputable def boundedCappedThresholdAuction
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (priceRule : (Agent → ℝ) → ℝ) (capacity : ℕ) :
    DigitalGoodsAuction Agent := by
  classical
  exact
    { allocation := fun bids i =>
        if boundedCappedWinner side marketSide bids (priceRule bids) capacity i
        then 1 else 0
      payment := fun bids i =>
        if boundedCappedWinner side marketSide bids (priceRule bids) capacity i
        then priceRule bids else 0 }

noncomputable def boundedCappedWinnerSet
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (price : ℝ) (capacity : ℕ) : Finset Agent := by
  classical
  exact (Finset.univ : Finset Agent).filter fun i =>
    boundedCappedWinner side marketSide bids price capacity i

noncomputable def boundedCappedAllocationCount
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (priceRule : (Agent → ℝ) → ℝ) (capacity : ℕ)
    (bids : Agent → ℝ) : ℕ :=
  (boundedCappedWinnerSet side marketSide bids (priceRule bids) capacity).card

theorem earlierBoundedEligibleCount_update_self
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (i : Agent) (report price : ℝ) :
    earlierBoundedEligibleCount side marketSide
        (Function.update bids i report) price i =
      earlierBoundedEligibleCount side marketSide bids price i := by
  classical
  unfold earlierBoundedEligibleCount
  apply congrArg Finset.card
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [boundedEligible, Function.update, hji]

theorem boundedCappedWinner_update_self_iff
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (i : Agent) (report price : ℝ)
    (capacity : ℕ) :
    boundedCappedWinner side marketSide (Function.update bids i report)
        price capacity i ↔
      side i = marketSide ∧ price ≤ report ∧
        earlierBoundedEligibleCount side marketSide bids price i < capacity := by
  simp [boundedCappedWinner, boundedEligible, and_assoc,
    earlierBoundedEligibleCount_update_self]

theorem boundedCappedThresholdAuction_truthful
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (priceRule : (Agent → ℝ) → ℝ) (capacity : ℕ)
    (hprice : ∀ (bids : Agent → ℝ) (i : Agent) (report : ℝ),
      side i = marketSide →
        priceRule (Function.update bids i report) = priceRule bids) :
    DigitalGoodsAuction.TruthfulDominantStrategy
      (boundedCappedThresholdAuction side marketSide priceRule capacity) := by
  classical
  intro values i report
  let M := boundedCappedThresholdAuction side marketSide priceRule capacity
  have hutility_truth :
      M.utility values i values =
        if boundedCappedWinner side marketSide values (priceRule values)
            capacity i then values i - priceRule values else 0 := by
    by_cases hw :
        boundedCappedWinner side marketSide values (priceRule values) capacity i
    · simp [M, DigitalGoodsAuction.utility, boundedCappedThresholdAuction, hw]
    · simp [M, DigitalGoodsAuction.utility, boundedCappedThresholdAuction, hw]
  have hutility_report :
      M.utility values i (Function.update values i report) =
        if boundedCappedWinner side marketSide
            (Function.update values i report)
            (priceRule (Function.update values i report)) capacity i
        then values i - priceRule (Function.update values i report) else 0 := by
    by_cases hw : boundedCappedWinner side marketSide
        (Function.update values i report)
        (priceRule (Function.update values i report)) capacity i
    · simp [M, DigitalGoodsAuction.utility, boundedCappedThresholdAuction, hw]
    · simp [M, DigitalGoodsAuction.utility, boundedCappedThresholdAuction, hw]
  rw [hutility_truth, hutility_report]
  by_cases hmarket : side i = marketSide
  · have hp := hprice values i report hmarket
    have htruth :
        boundedCappedWinner side marketSide values (priceRule values) capacity i ↔
          priceRule values ≤ values i ∧
            earlierBoundedEligibleCount side marketSide values
              (priceRule values) i < capacity := by
      simp [boundedCappedWinner, boundedEligible, hmarket]
    have hreport :
        boundedCappedWinner side marketSide (Function.update values i report)
            (priceRule (Function.update values i report)) capacity i ↔
          priceRule values ≤ report ∧
            earlierBoundedEligibleCount side marketSide values
              (priceRule values) i < capacity := by
      rw [hp]
      simpa [hmarket] using
        (boundedCappedWinner_update_self_iff side marketSide values i report
          (priceRule values) capacity)
    rw [hp] at hreport
    rw [hp]
    by_cases hcap :
        earlierBoundedEligibleCount side marketSide values
          (priceRule values) i < capacity
    · by_cases hv : priceRule values ≤ values i
      · by_cases hr : priceRule values ≤ report
        · rw [if_pos (hreport.mpr ⟨hr, hcap⟩),
            if_pos (htruth.mpr ⟨hv, hcap⟩)]
        · rw [if_neg (hreport.not.mpr (by simp [hr])),
            if_pos (htruth.mpr ⟨hv, hcap⟩)]
          exact sub_nonneg.mpr hv
      · have hvlt : values i < priceRule values := lt_of_not_ge hv
        by_cases hr : priceRule values ≤ report
        · rw [if_pos (hreport.mpr ⟨hr, hcap⟩),
            if_neg (htruth.not.mpr (by simp [hv]))]
          exact sub_nonpos.mpr (le_of_lt hvlt)
        · rw [if_neg (hreport.not.mpr (by simp [hr])),
            if_neg (htruth.not.mpr (by simp [hv]))]
    · have ht_not :
          ¬ boundedCappedWinner side marketSide values
            (priceRule values) capacity i :=
        htruth.not.mpr (by simp [hcap])
      have hr_not :
          ¬ boundedCappedWinner side marketSide
            (Function.update values i report)
            (priceRule values) capacity i :=
        hreport.not.mpr (by simp [hcap])
      rw [if_neg hr_not, if_neg ht_not]
  · have ht_not :
        ¬ boundedCappedWinner side marketSide values
          (priceRule values) capacity i := by
      simp [boundedCappedWinner, boundedEligible, hmarket]
    have hr_not :
        ¬ boundedCappedWinner side marketSide
          (Function.update values i report)
          (priceRule (Function.update values i report)) capacity i := by
      simp [boundedCappedWinner, boundedEligible, hmarket]
    rw [if_neg hr_not, if_neg ht_not]

theorem boundedCappedWinner_card_le_capacity
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (bids : Agent → ℝ) (price : ℝ) (capacity : ℕ) :
    (boundedCappedWinnerSet side marketSide bids price capacity).card ≤
      capacity := by
  classical
  let winners : Finset Agent :=
    boundedCappedWinnerSet side marketSide bids price capacity
  have winner_spec (i : ↑winners) :
      boundedCappedWinner side marketSide bids price capacity i := by
    have hi : (i : Agent) ∈
        (Finset.univ : Finset Agent).filter fun a =>
          boundedCappedWinner side marketSide bids price capacity a := by
      simpa [winners, boundedCappedWinnerSet] using i.2
    exact (Finset.mem_filter.mp hi).2
  let rank : ↑winners → Fin capacity := fun i =>
    ⟨earlierBoundedEligibleCount side marketSide bids price i,
      (winner_spec i).2⟩
  have hrank_injective : Function.Injective rank := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij_lt | hji_lt
    · have hi_eligible : boundedEligible side marketSide bids price i :=
        (winner_spec i).1
      let beforeI : Finset Agent :=
        (Finset.univ : Finset Agent).filter fun a =>
          boundedEligible side marketSide bids price a ∧ a < i
      let beforeJ : Finset Agent :=
        (Finset.univ : Finset Agent).filter fun a =>
          boundedEligible side marketSide bids price a ∧ a < j
      have hproper : beforeI ⊂ beforeJ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro a ha
          rcases Finset.mem_filter.mp ha with ⟨haU, haE, hai⟩
          exact Finset.mem_filter.mpr ⟨haU, haE, hai.trans hij_lt⟩
        · intro heq
          have hi_mem_j : (i : Agent) ∈ beforeJ :=
            Finset.mem_filter.mpr ⟨by simp, hi_eligible, hij_lt⟩
          have hi_not_mem_i : (i : Agent) ∉ beforeI := by simp [beforeI]
          exact hi_not_mem_i (heq ▸ hi_mem_j)
      have hcard := Finset.card_lt_card hproper
      have hrank_lt : earlierBoundedEligibleCount side marketSide bids price i <
          earlierBoundedEligibleCount side marketSide bids price j := by
        change beforeI.card < beforeJ.card
        exact hcard
      exact (Nat.ne_of_lt hrank_lt) (congrArg Fin.val hij)
    · have hj_eligible : boundedEligible side marketSide bids price j :=
        (winner_spec j).1
      let beforeJ : Finset Agent :=
        (Finset.univ : Finset Agent).filter fun a =>
          boundedEligible side marketSide bids price a ∧ a < j
      let beforeI : Finset Agent :=
        (Finset.univ : Finset Agent).filter fun a =>
          boundedEligible side marketSide bids price a ∧ a < i
      have hproper : beforeJ ⊂ beforeI := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro a ha
          rcases Finset.mem_filter.mp ha with ⟨haU, haE, haj⟩
          exact Finset.mem_filter.mpr ⟨haU, haE, haj.trans hji_lt⟩
        · intro heq
          have hj_mem_i : (j : Agent) ∈ beforeI :=
            Finset.mem_filter.mpr ⟨by simp, hj_eligible, hji_lt⟩
          have hj_not_mem_j : (j : Agent) ∉ beforeJ := by simp [beforeJ]
          exact hj_not_mem_j (heq ▸ hj_mem_i)
      have hcard := Finset.card_lt_card hproper
      have hrank_lt : earlierBoundedEligibleCount side marketSide bids price j <
          earlierBoundedEligibleCount side marketSide bids price i := by
        change beforeJ.card < beforeI.card
        exact hcard
      exact (Nat.ne_of_lt hrank_lt) (congrArg Fin.val hij).symm
  have hcard := Fintype.card_le_of_injective rank hrank_injective
  simpa [winners] using hcard

theorem boundedCappedThresholdAuction_supply_feasible
    {Agent : Type*} [Fintype Agent] [LinearOrder Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (priceRule : (Agent → ℝ) → ℝ) (capacity : ℕ)
    (bids : Agent → ℝ) :
    boundedCappedAllocationCount side marketSide priceRule capacity bids ≤
      capacity := by
  unfold boundedCappedAllocationCount
  exact boundedCappedWinner_card_le_capacity side marketSide bids
    (priceRule bids) capacity

/-! ## Section 11 sampling mechanisms -/

/-- The paper's integer version of the scaled sample capacity
`m k / (n-m)`. -/
def scaledSampleCapacity (sampleSize marketSize capacity : ℕ) : ℕ :=
  sampleSize * capacity / marketSize

/-- `opt` computed only from the designated sample side. -/
noncomputable def boundedSamplingPriceRule
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (sampleSide : Bool) (sampleCapacity : ℕ)
    (bids : Agent → ℝ) : ℝ :=
  boundedSupplyOptimalThreshold
    (restrictBidsBySide side sampleSide bids) sampleCapacity

theorem boundedSamplingPriceRule_update_market
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (sampleCapacity : ℕ)
    (bids : Agent → ℝ) (i : Agent) (report : ℝ)
    (hi : side i = !sampleSide) :
    boundedSamplingPriceRule side sampleSide sampleCapacity
        (Function.update bids i report) =
      boundedSamplingPriceRule side sampleSide sampleCapacity bids := by
  unfold boundedSamplingPriceRule
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    cases sampleSide <;> simp [restrictBidsBySide, hi]
  · simp [restrictBidsBySide, Function.update, hji]

/-- The bounded-supply single-price sampling auction: compute
`opt_{m k/(n-m)}` on the sample, offer it to the other side, and use a fixed
priority rule to cap sales at `k`. -/
noncomputable def boundedSinglePriceSamplingAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) : DigitalGoodsAuction Agent :=
  boundedCappedThresholdAuction side (!sampleSide)
    (boundedSamplingPriceRule side sampleSide
      (scaledSampleCapacity sampleSize marketSize capacity))
    capacity

theorem boundedSinglePriceSamplingAuction_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) :
    DigitalGoodsAuction.TruthfulDominantStrategy
      (boundedSinglePriceSamplingAuction side sampleSide
        sampleSize marketSize capacity) := by
  unfold boundedSinglePriceSamplingAuction
  apply boundedCappedThresholdAuction_truthful
  intro bids i report hi
  exact boundedSamplingPriceRule_update_market side sampleSide
    (scaledSampleCapacity sampleSize marketSize capacity) bids i report hi

theorem boundedSinglePriceSamplingAuction_supply_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) (bids : Agent → ℝ) :
    boundedCappedAllocationCount side (!sampleSide)
        (boundedSamplingPriceRule side sampleSide
          (scaledSampleCapacity sampleSize marketSize capacity))
        capacity bids ≤ capacity := by
  exact boundedCappedThresholdAuction_supply_feasible side (!sampleSide)
    (boundedSamplingPriceRule side sampleSide
      (scaledSampleCapacity sampleSize marketSize capacity)) capacity bids

/-- The half-sample dual-price bounded-supply mechanism.  Each side is offered
the opposite side's `opt_{k/2}` threshold, and each half is capped at `k/2`. -/
noncomputable def boundedDualPriceSamplingAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) : DigitalGoodsAuction Agent := by
  let left := boundedCappedThresholdAuction side false
    (boundedSamplingPriceRule side true (capacity / 2)) (capacity / 2)
  let right := boundedCappedThresholdAuction side true
    (boundedSamplingPriceRule side false (capacity / 2)) (capacity / 2)
  exact
    { allocation := fun bids i =>
        if side i = false then left.allocation bids i else right.allocation bids i
      payment := fun bids i =>
        if side i = false then left.payment bids i else right.payment bids i }

theorem boundedDualPriceSamplingAuction_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) :
    DigitalGoodsAuction.TruthfulDominantStrategy
      (boundedDualPriceSamplingAuction side capacity) := by
  classical
  let left := boundedCappedThresholdAuction side false
    (boundedSamplingPriceRule side true (capacity / 2)) (capacity / 2)
  let right := boundedCappedThresholdAuction side true
    (boundedSamplingPriceRule side false (capacity / 2)) (capacity / 2)
  have hleft : left.TruthfulDominantStrategy := by
    apply boundedCappedThresholdAuction_truthful
    intro bids i report hi
    exact boundedSamplingPriceRule_update_market side true (capacity / 2)
      bids i report (by cases h : side i <;> simp_all)
  have hright : right.TruthfulDominantStrategy := by
    apply boundedCappedThresholdAuction_truthful
    intro bids i report hi
    exact boundedSamplingPriceRule_update_market side false (capacity / 2)
      bids i report (by cases h : side i <;> simp_all)
  intro values i report
  by_cases hi : side i = false
  · simpa [boundedDualPriceSamplingAuction, left, right,
      DigitalGoodsAuction.utility, hi] using hleft values i report
  · have hitrue : side i = true := by cases h : side i <;> simp_all
    simpa [boundedDualPriceSamplingAuction, left, right,
      DigitalGoodsAuction.utility, hi, hitrue] using hright values i report

def boundedDualAllocationCount
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) (bids : Agent → ℝ) : ℕ :=
  boundedCappedAllocationCount side false
      (boundedSamplingPriceRule side true (capacity / 2)) (capacity / 2) bids +
    boundedCappedAllocationCount side true
      (boundedSamplingPriceRule side false (capacity / 2)) (capacity / 2) bids

theorem boundedDualPriceSamplingAuction_supply_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (capacity : ℕ) (bids : Agent → ℝ) :
    boundedDualAllocationCount side capacity bids ≤ capacity := by
  unfold boundedDualAllocationCount
  have hleft := boundedCappedThresholdAuction_supply_feasible side false
    (boundedSamplingPriceRule side true (capacity / 2)) (capacity / 2) bids
  have hright := boundedCappedThresholdAuction_supply_feasible side true
    (boundedSamplingPriceRule side false (capacity / 2)) (capacity / 2) bids
  omega

/-! ## Concentration and competitiveness on balanced samples -/

/-- Revenue after priority capping at a fixed price; the cardinal expression
is independent of which fixed-priority eligible bidders are retained. -/
def boundedSidePriceRevenue
    {Agent : Type*} [Fintype Agent]
    (side : Agent → Bool) (marketSide : Bool)
    (values : Agent → ℝ) (capacity : ℕ) (price : ℝ) : ℝ :=
  (min capacity (sideSaleCount side marketSide values price) : ℝ) * price

def boundedSinglePriceSamplingRevenue
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) (values : Agent → ℝ) : ℝ :=
  let p := boundedSamplingPriceRule side sampleSide
    (scaledSampleCapacity sampleSize marketSize capacity) values
  boundedSidePriceRevenue side (!sampleSide) values capacity p

theorem boundedSinglePriceSampling_competitive_on_balanced_sample
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (sampleSize marketSize capacity : ℕ) (values : Agent → ℝ)
    {beta gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hsample :
      beta * boundedSupplyFixedPriceBenchmark values capacity ≤
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
    gamma * beta * boundedSupplyFixedPriceBenchmark values capacity ≤
      boundedSinglePriceSamplingRevenue side sampleSide
        sampleSize marketSize capacity values := by
  let p := boundedSamplingPriceRule side sampleSide
    (scaledSampleCapacity sampleSize marketSize capacity) values
  let sampleWinners := min (scaledSampleCapacity sampleSize marketSize capacity)
    (sideSaleCount side sampleSide values p)
  let marketWinners := min capacity (sideSaleCount side (!sampleSide) values p)
  have hp : 0 ≤ p := boundedSupplyOptimalThreshold_nonneg
    (restrictBidsBySide side sampleSide values)
    (scaledSampleCapacity sampleSize marketSize capacity)
  have hscaled :
      gamma * (beta * boundedSupplyFixedPriceBenchmark values capacity) ≤
        gamma * ((sampleWinners : ℝ) * p) :=
    mul_le_mul_of_nonneg_left (by simpa [p, sampleWinners] using hsample) hgamma
  have hmarket : gamma * ((sampleWinners : ℝ) * p) ≤
      (marketWinners : ℝ) * p := by
    calc
      gamma * ((sampleWinners : ℝ) * p) =
          (gamma * (sampleWinners : ℝ)) * p := by ring
      _ ≤ (marketWinners : ℝ) * p :=
        mul_le_mul_of_nonneg_right (by simpa [p, sampleWinners, marketWinners] using hbalance) hp
  calc
    gamma * beta * boundedSupplyFixedPriceBenchmark values capacity =
        gamma * (beta * boundedSupplyFixedPriceBenchmark values capacity) := by ring
    _ ≤ gamma * ((sampleWinners : ℝ) * p) := hscaled
    _ ≤ (marketWinners : ℝ) * p := hmarket
    _ = boundedSinglePriceSamplingRevenue side sampleSide
        sampleSize marketSize capacity values := by
      simp [boundedSinglePriceSamplingRevenue, boundedSidePriceRevenue,
        p, marketWinners]

def boundedDualPriceSamplingRevenue
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (capacity : ℕ) (values : Agent → ℝ) : ℝ :=
  boundedSidePriceRevenue side false values (capacity / 2)
      (boundedSamplingPriceRule side true (capacity / 2) values) +
    boundedSidePriceRevenue side true values (capacity / 2)
      (boundedSamplingPriceRule side false (capacity / 2) values)

/-- Concrete good-event implication behind the paper's bounded dual-price
competitiveness statement.  Each side's opposite-sample benchmark share is
balanced by its capped market winner count. -/
theorem boundedDualPriceSampling_competitive_on_balanced_halves
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (capacity : ℕ) (values : Agent → ℝ)
    {target gamma : ℝ} (hgamma : 0 ≤ gamma)
    {sampleRevenueFalse sampleRevenueTrue : ℝ}
    (htarget : target ≤ sampleRevenueFalse + sampleRevenueTrue)
    (hfalse : gamma * sampleRevenueFalse ≤
      boundedSidePriceRevenue side false values (capacity / 2)
        (boundedSamplingPriceRule side true (capacity / 2) values))
    (htrue : gamma * sampleRevenueTrue ≤
      boundedSidePriceRevenue side true values (capacity / 2)
        (boundedSamplingPriceRule side false (capacity / 2) values)) :
    gamma * target ≤ boundedDualPriceSamplingRevenue side capacity values := by
  calc
    gamma * target ≤ gamma * (sampleRevenueFalse + sampleRevenueTrue) :=
      mul_le_mul_of_nonneg_left htarget hgamma
    _ = gamma * sampleRevenueFalse + gamma * sampleRevenueTrue := by ring
    _ ≤ boundedDualPriceSamplingRevenue side capacity values :=
      add_le_add hfalse htrue

/-! ## Combined qualitative competitiveness guarantees -/

/-- Turn a sampled bidder subset into the Boolean side assignment used by the
sampling mechanisms. -/
def sampledSideAssignment
    {Agent : Type*} [DecidableEq Agent]
    (sample : Finset Agent) (i : Agent) : Bool :=
  decide (i ∈ sample)

/-- The finite space of exactly `sampleSize` sampled bidders. -/
abbrev FixedSizeSampleSpace
    (Agent : Type*) [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) :=
  ↑((Finset.univ : Finset Agent).powersetCard sampleSize)

/-- Uniform law on the exactly-`sampleSize` bidder subsets. -/
noncomputable def uniformFixedSizeSampleLaw
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hsize : sampleSize ≤ Fintype.card Agent) :
    PMF (FixedSizeSampleSpace Agent sampleSize) := by
  letI : Nonempty (FixedSizeSampleSpace Agent sampleSize) :=
    Finset.nonempty_coe_sort.mpr
      (Finset.powersetCard_nonempty.mpr (by simpa using hsize))
  exact AppliedModelingLib.uniformPMF _

/-- Event probability is monotone under pointwise implication. -/
theorem pmfProb_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ ω, P ω → Q ω) :
    AppliedModelingLib.pmfProb law P ≤ AppliedModelingLib.pmfProb law Q := by
  unfold AppliedModelingLib.pmfProb
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro ω
  by_cases hP : P ω
  · simp [hP, hPQ ω hP]
  · by_cases hQ : Q ω <;> simp [hP, hQ]

/-- Event probability with the logically irrelevant predicate decision chosen
internally.  This keeps classical decidability out of paper-facing theorem
binders and prevents it from changing finite-carrier representation data. -/
noncomputable def pmfEventProbability
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (P : Ω → Prop) : ℝ := by
  letI := Classical.decPred P
  exact AppliedModelingLib.pmfProb law P

theorem pmfEventProbability_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (P Q : Ω → Prop)
    (hPQ : ∀ ω, P ω → Q ω) :
    pmfEventProbability law P ≤ pmfEventProbability law Q := by
  classical
  unfold pmfEventProbability
  exact pmfProb_mono law P Q hPQ

/-- The benchmark-capture and sample/market-balance event used by the bounded
single-price sampler.  Section 11 leaves the constants and the probability of
this event qualitative, so they remain explicit parameters in the combined
theorem below. -/
def boundedSinglePriceSamplingGoodEvent
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (sampleSize marketSize capacity : ℕ)
    (values : Agent → ℝ) (beta gamma : ℝ) : Prop :=
  let side := sampledSideAssignment sample
  let sampleCapacity :=
    scaledSampleCapacity sampleSize marketSize capacity
  let price := boundedSamplingPriceRule side true sampleCapacity values
  beta * boundedSupplyFixedPriceBenchmark values capacity ≤
      (min sampleCapacity
        (sideSaleCount side true values price) : ℝ) * price ∧
    gamma *
        (min sampleCapacity
          (sideSaleCount side true values price) : ℝ) ≤
      (min capacity
        (sideSaleCount side false values price) : ℝ)

/-- Revenue-competitiveness event for the bounded single-price sampler. -/
def boundedSinglePriceSamplingCompetitiveEvent
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (sampleSize marketSize capacity : ℕ)
    (values : Agent → ℝ) (beta gamma : ℝ) : Prop :=
  gamma * beta * boundedSupplyFixedPriceBenchmark values capacity ≤
    boundedSinglePriceSamplingRevenue
      (sampledSideAssignment sample) true
      sampleSize marketSize capacity values

theorem boundedSinglePriceSampling_competitive_of_good_event
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (sampleSize marketSize capacity : ℕ)
    (values : Agent → ℝ) {beta gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hgood : boundedSinglePriceSamplingGoodEvent sample
      sampleSize marketSize capacity values beta gamma) :
    boundedSinglePriceSamplingCompetitiveEvent sample
      sampleSize marketSize capacity values beta gamma := by
  rcases hgood with ⟨hsample, hbalance⟩
  exact boundedSinglePriceSampling_competitive_on_balanced_sample
    (sampledSideAssignment sample) true
    sampleSize marketSize capacity values hgamma hsample hbalance

/-- Combined formal content of Section 11's qualitative single-price claim.
For any law on sampled subsets, any lower bound `successProbability` on the
explicit good event is also a lower bound on the claimed competitive-revenue
event.  The same theorem records that every realized mechanism is truthful and
uses at most `capacity` units. -/
theorem boundedSinglePriceSampling_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (sampleLaw : PMF Sample) (sampleSet : Sample → Finset Agent)
    (sampleSize marketSize capacity : ℕ) (values : Agent → ℝ)
    {beta gamma successProbability : ℝ} (hgamma : 0 ≤ gamma)
    (hgood_probability :
      successProbability ≤ pmfEventProbability sampleLaw (fun sample =>
        boundedSinglePriceSamplingGoodEvent (sampleSet sample)
          sampleSize marketSize capacity values beta gamma)) :
    (∀ sample : Sample,
        DigitalGoodsAuction.TruthfulDominantStrategy
          (boundedSinglePriceSamplingAuction
            (sampledSideAssignment (sampleSet sample)) true
            sampleSize marketSize capacity)) ∧
      (∀ sample : Sample,
        boundedCappedAllocationCount
            (sampledSideAssignment (sampleSet sample)) false
            (boundedSamplingPriceRule
              (sampledSideAssignment (sampleSet sample)) true
              (scaledSampleCapacity sampleSize marketSize capacity))
            capacity values ≤ capacity) ∧
      successProbability ≤ pmfEventProbability sampleLaw (fun sample =>
        boundedSinglePriceSamplingCompetitiveEvent (sampleSet sample)
          sampleSize marketSize capacity values beta gamma) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro sample
    exact boundedSinglePriceSamplingAuction_truthful
      (sampledSideAssignment (sampleSet sample)) true
      sampleSize marketSize capacity
  · intro sample
    exact boundedSinglePriceSamplingAuction_supply_feasible
      (sampledSideAssignment (sampleSet sample)) true
      sampleSize marketSize capacity values
  · exact hgood_probability.trans (pmfEventProbability_mono sampleLaw _ _ fun sample hgood =>
      boundedSinglePriceSampling_competitive_of_good_event (sampleSet sample)
        sampleSize marketSize capacity values hgamma hgood)

/-- Fixed-cardinality specialization of the combined single-price guarantee.
This is the sampling law and the `m k/(n-m)` market-size substitution stated in
Section 11. -/
theorem boundedSinglePriceSampling_fixedSize_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize capacity : ℕ) (values : Agent → ℝ)
    (hsample_lt : sampleSize < Fintype.card Agent)
    {beta gamma successProbability : ℝ}
    (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (_hsuccess : 0 < successProbability)
    (_hsuccess_le_one : successProbability ≤ 1)
    (hgood_probability :
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
        (fun sample => boundedSinglePriceSamplingGoodEvent sample.1
          sampleSize (Fintype.card Agent - sampleSize) capacity
          values beta gamma)) :
    (∀ sample : FixedSizeSampleSpace Agent sampleSize,
        DigitalGoodsAuction.TruthfulDominantStrategy
          (boundedSinglePriceSamplingAuction
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
  classical
  have hgeneric := boundedSinglePriceSampling_combined_guarantee
    (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
    (fun sample : FixedSizeSampleSpace Agent sampleSize => sample.1)
    sampleSize (Fintype.card Agent - sampleSize) capacity values
    hgamma.le hgood_probability
  exact ⟨fun sample => hgeneric.1 sample,
    fun sample => hgeneric.2.1 sample, hgeneric.2.2⟩

/-- `F_{k/2}` captured by one side of a half-sample split. -/
def boundedHalfSampleBenchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (capacity : ℕ) (values : Agent → ℝ) : ℝ :=
  boundedSupplyFixedPriceBenchmark
    (restrictBidsBySide side sampleSide values) (capacity / 2)

/-- The benchmark-capture and two opposite-side balance conditions used by the
bounded dual-price sampler. -/
def boundedDualPriceSamplingGoodEvent
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (capacity : ℕ)
    (values : Agent → ℝ) (beta gamma : ℝ) : Prop :=
  let side := sampledSideAssignment sample
  beta * boundedSupplyFixedPriceBenchmark values capacity ≤
      boundedHalfSampleBenchmark side true capacity values +
        boundedHalfSampleBenchmark side false capacity values ∧
    gamma * boundedHalfSampleBenchmark side true capacity values ≤
      boundedSidePriceRevenue side false values (capacity / 2)
        (boundedSamplingPriceRule side true (capacity / 2) values) ∧
    gamma * boundedHalfSampleBenchmark side false capacity values ≤
      boundedSidePriceRevenue side true values (capacity / 2)
        (boundedSamplingPriceRule side false (capacity / 2) values)

/-- Revenue-competitiveness event for the bounded dual-price sampler. -/
def boundedDualPriceSamplingCompetitiveEvent
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (capacity : ℕ)
    (values : Agent → ℝ) (beta gamma : ℝ) : Prop :=
  gamma * beta * boundedSupplyFixedPriceBenchmark values capacity ≤
    boundedDualPriceSamplingRevenue
      (sampledSideAssignment sample) capacity values

theorem boundedDualPriceSampling_competitive_of_good_event
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (capacity : ℕ) (values : Agent → ℝ)
    {beta gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hgood : boundedDualPriceSamplingGoodEvent
      sample capacity values beta gamma) :
    boundedDualPriceSamplingCompetitiveEvent
      sample capacity values beta gamma := by
  rcases hgood with ⟨htarget, hfalse, htrue⟩
  have hcombined := boundedDualPriceSampling_competitive_on_balanced_halves
    (sampledSideAssignment sample) capacity values hgamma htarget hfalse htrue
  simpa [boundedDualPriceSamplingCompetitiveEvent, mul_assoc] using hcombined

/-- Combined formal content of Section 11's qualitative dual-price claim.
The source does not state a numerical success probability or competitive
constant; this theorem quantifies both and turns any proved lower bound on the
explicit good event into the corresponding revenue guarantee, while also
recording truthfulness and aggregate supply feasibility for every split. -/
theorem boundedDualPriceSampling_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (sampleLaw : PMF Sample) (sampleSet : Sample → Finset Agent)
    (capacity : ℕ)
    (values : Agent → ℝ)
    {beta gamma successProbability : ℝ} (hgamma : 0 ≤ gamma)
    (hgood_probability :
      successProbability ≤ pmfEventProbability sampleLaw (fun sample =>
        boundedDualPriceSamplingGoodEvent
          (sampleSet sample) capacity values beta gamma)) :
    (∀ sample : Sample,
        DigitalGoodsAuction.TruthfulDominantStrategy
          (boundedDualPriceSamplingAuction
            (sampledSideAssignment (sampleSet sample)) capacity)) ∧
      (∀ sample : Sample,
        boundedDualAllocationCount
            (sampledSideAssignment (sampleSet sample)) capacity values ≤
          capacity) ∧
      successProbability ≤ pmfEventProbability sampleLaw (fun sample =>
        boundedDualPriceSamplingCompetitiveEvent
          (sampleSet sample) capacity values beta gamma) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro sample
    exact boundedDualPriceSamplingAuction_truthful
      (sampledSideAssignment (sampleSet sample)) capacity
  · intro sample
    exact boundedDualPriceSamplingAuction_supply_feasible
      (sampledSideAssignment (sampleSet sample)) capacity values
  · exact hgood_probability.trans (pmfEventProbability_mono sampleLaw _ _ fun sample hgood =>
      boundedDualPriceSampling_competitive_of_good_event (sampleSet sample)
        capacity values hgamma hgood)

/-- Uniform half-sample specialization of the combined dual-price guarantee.
For odd populations the sample has `floor (n/2)` bidders and its complement
has the remaining bidders. -/
theorem boundedDualPriceSampling_fixedHalf_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (capacity : ℕ) (values : Agent → ℝ)
    {beta gamma successProbability : ℝ}
    (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (_hsuccess : 0 < successProbability)
    (_hsuccess_le_one : successProbability ≤ 1)
    (hgood_probability :
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw (Fintype.card Agent / 2)
          (Nat.div_le_self _ _))
        (fun sample => boundedDualPriceSamplingGoodEvent sample.1
          capacity values beta gamma)) :
    (∀ sample : FixedSizeSampleSpace Agent (Fintype.card Agent / 2),
        DigitalGoodsAuction.TruthfulDominantStrategy
          (boundedDualPriceSamplingAuction
            (sampledSideAssignment sample.1) capacity)) ∧
      (∀ sample : FixedSizeSampleSpace Agent (Fintype.card Agent / 2),
        boundedDualAllocationCount
            (sampledSideAssignment sample.1) capacity values ≤ capacity) ∧
      successProbability ≤ pmfEventProbability
        (uniformFixedSizeSampleLaw (Fintype.card Agent / 2)
          (Nat.div_le_self _ _))
        (fun sample => boundedDualPriceSamplingCompetitiveEvent sample.1
          capacity values beta gamma) := by
  classical
  have hgeneric := boundedDualPriceSampling_combined_guarantee
    (uniformFixedSizeSampleLaw (Fintype.card Agent / 2)
      (Nat.div_le_self _ _))
    (fun sample : FixedSizeSampleSpace Agent (Fintype.card Agent / 2) => sample.1)
    capacity values hgamma.le hgood_probability
  exact ⟨fun sample => hgeneric.1 sample,
    fun sample => hgeneric.2.1 sample, hgeneric.2.2⟩

/-- Number of eligible buyers discarded by a `capacity` cap. -/
def boundedRejectionCount (eligible capacity : ℕ) : ℕ :=
  eligible - min capacity eligible

theorem boundedRejectionCount_le_slack
    {eligible capacity slack : ℕ} (h : eligible ≤ capacity + slack) :
    boundedRejectionCount eligible capacity ≤ slack := by
  unfold boundedRejectionCount
  omega

/-- Combined probability form of Section 11's qualitative "few rejected
bidders" claim.  The source does not give a numerical success probability, so
the probability of the explicit market-count slack event remains a parameter;
the conclusion transfers it to the actual rejection count of the fixed-size
single-price sampler. -/
theorem boundedSinglePriceSampling_small_rejection_combined_guarantee
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize capacity slack : ℕ) (values : Agent → ℝ)
    (hsample_lt : sampleSize < Fintype.card Agent)
    {successProbability : ℝ}
    (_hsuccess : 0 < successProbability)
    (_hsuccess_le_one : successProbability ≤ 1)
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
  classical
  exact hcount_probability.trans
    (pmfEventProbability_mono _ _ _ fun _sample hcount =>
      boundedRejectionCount_le_slack hcount)

/-- Fixed-size sampling makes severe underrepresentation of any fixed
eligible population exponentially unlikely.  This is the quantitative
high-probability input used to bound cap rejections. -/
theorem boundedSampling_underrepresentation_probability
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
        (2 * (all.card : ℝ)))) :=
  lemma6_1_fixed_size_lower_tail heligible hsample_pos hsample_lt
    hdelta_pos hdelta_le_one

/-! ## Deterministic threshold extension and unlimited-supply transport -/

/-- Strict posted-threshold allocation with an explicit zero-supply branch.
Strict acceptance is the deterministic tie convention that makes the
own-erased `opt_k` construction capacity-feasible; a value exactly equal to
the threshold is indifferent and loses. -/
noncomputable def boundedStrictThresholdAuction
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) (capacity : ℕ) :
    DigitalGoodsAuction Agent :=
  { allocation := fun bids i =>
      if 0 < capacity ∧ threshold bids i < bids i then 1 else 0
    payment := fun bids i =>
      if 0 < capacity ∧ threshold bids i < bids i then threshold bids i else 0 }

theorem boundedStrictThresholdAuction_utility_eq
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) (capacity : ℕ)
    (values bids : Agent → ℝ) (i : Agent) :
    (boundedStrictThresholdAuction threshold capacity).utility values i bids =
      if 0 < capacity ∧ threshold bids i < bids i then
        values i - threshold bids i
      else 0 := by
  by_cases h : 0 < capacity ∧ threshold bids i < bids i <;>
    simp [DigitalGoodsAuction.utility, boundedStrictThresholdAuction, h]

theorem boundedStrictThresholdAuction_truthful
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) (capacity : ℕ)
    (hind : OwnBidIndependent threshold) :
    DigitalGoodsAuction.TruthfulDominantStrategy
      (boundedStrictThresholdAuction threshold capacity) := by
  intro values i report
  rw [boundedStrictThresholdAuction_utility_eq,
    boundedStrictThresholdAuction_utility_eq]
  rw [hind values i report]
  simp only [Function.update_self]
  by_cases hcapacity : 0 < capacity
  · by_cases htruth : threshold values i < values i
    · by_cases hreport : threshold values i < report
      · simp [hcapacity, htruth, hreport]
      · simpa [hcapacity, htruth, hreport] using
          sub_nonneg.mpr htruth.le
    · by_cases hreport : threshold values i < report
      · simpa [hcapacity, htruth, hreport] using
          sub_nonpos.mpr (le_of_not_gt htruth)
      · simp [hcapacity, htruth, hreport]
  · simp [hcapacity]

/-- Section 11's deterministic optimal-threshold extension: bidder `i` is
offered `opt_k` after erasing `i`'s own report.  Strict threshold ties are
rejected, which is utility-neutral and ensures that at most `k` bidders can
accept simultaneously. -/
noncomputable def boundedDeterministicOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) : DigitalGoodsAuction Agent :=
  boundedStrictThresholdAuction
    (ownErasedThreshold (fun _i bids =>
      boundedSupplyOptimalThreshold bids capacity)) capacity

theorem boundedDeterministicOptimalThresholdAuction_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) :
    DigitalGoodsAuction.TruthfulDominantStrategy
      (boundedDeterministicOptimalThresholdAuction
        (Agent := Agent) capacity) := by
  unfold boundedDeterministicOptimalThresholdAuction
  exact boundedStrictThresholdAuction_truthful _ capacity
    (ownErasedThreshold_ownBidIndependent
      (fun _i (_bids : Agent → ℝ) =>
        boundedSupplyOptimalThreshold _bids capacity))

noncomputable def boundedDeterministicOptimalThresholdWinnerSet
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) (bids : Agent → ℝ) : Finset Agent := by
  classical
  exact (Finset.univ : Finset Agent).filter fun i =>
    0 < capacity ∧
      ownErasedThreshold
          (fun _i erased => boundedSupplyOptimalThreshold erased capacity)
          bids i < bids i

noncomputable def boundedDeterministicOptimalThresholdAllocationCount
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) (bids : Agent → ℝ) : ℕ :=
  (boundedDeterministicOptimalThresholdWinnerSet capacity bids).card

/-- The own-erased `opt_k` mechanism cannot have more than `k` strict
acceptances.  If it did, choose the lowest-valued accepting bidder.  After
erasing that bidder there are still `k` bids at least as high, so posting the
bidder's value earns `k` times that value.  But `opt_k` is strictly lower and
cannot attain the benchmark, a contradiction. -/
theorem boundedDeterministicOptimalThresholdAuction_supply_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : ℕ) (bids : Agent → ℝ) :
    boundedDeterministicOptimalThresholdAllocationCount capacity bids ≤
      capacity := by
  classical
  let winners : Finset Agent :=
    boundedDeterministicOptimalThresholdWinnerSet capacity bids
  by_cases hcapacity : capacity = 0
  · subst capacity
    simp [boundedDeterministicOptimalThresholdAllocationCount,
      boundedDeterministicOptimalThresholdWinnerSet]
  · have hcapacity_pos : 0 < capacity := Nat.pos_of_ne_zero hcapacity
    by_contra hnot
    have hcapacity_lt : capacity < winners.card := by
      simpa [boundedDeterministicOptimalThresholdAllocationCount, winners]
        using Nat.lt_of_not_ge hnot
    have hwinners : winners.Nonempty := by
      exact Finset.card_pos.mp (lt_of_lt_of_le hcapacity_pos hcapacity_lt.le)
    obtain ⟨i, hi, hmin⟩ :=
      Finset.exists_min_image winners bids hwinners
    have hi_accepts :
        boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity < bids i := by
      have hi_mem :
          i ∈ (Finset.univ : Finset Agent).filter fun j =>
          0 < capacity ∧
            ownErasedThreshold
                (fun _j erased =>
                  boundedSupplyOptimalThreshold erased capacity)
                bids j < bids j := by
        simpa [winners, boundedDeterministicOptimalThresholdWinnerSet]
          using hi
      have hi' := (Finset.mem_filter.mp hi_mem).2.2
      simpa [ownErasedThreshold] using hi'
    have hi_nonneg : 0 ≤ bids i :=
      (boundedSupplyOptimalThreshold_nonneg (eraseOwnBid bids i) capacity).trans
        hi_accepts.le
    have hother_card : capacity ≤ (winners.erase i).card := by
      rw [Finset.card_erase_of_mem hi]
      omega
    have hother_subset :
        winners.erase i ⊆
          (Finset.univ : Finset Agent).filter fun j =>
            bids i ≤ eraseOwnBid bids i j := by
      intro j hj
      have hj_ne : j ≠ i := Finset.ne_of_mem_erase hj
      have hj_winner : j ∈ winners := (Finset.mem_erase.mp hj).2
      have hij : bids i ≤ bids j := hmin j hj_winner
      exact Finset.mem_filter.mpr
        ⟨by simp, by simpa [eraseOwnBid, Function.update, hj_ne] using hij⟩
    have hsale : capacity ≤ saleCount (eraseOwnBid bids i) (bids i) := by
      unfold saleCount
      exact hother_card.trans (Finset.card_le_card hother_subset)
    have hposted_revenue :
        boundedSupplySinglePriceRevenue (eraseOwnBid bids i) capacity (bids i) =
          (capacity : ℝ) * bids i := by
      unfold boundedSupplySinglePriceRevenue
      have hsale_real : (capacity : ℝ) ≤
          (saleCount (eraseOwnBid bids i) (bids i) : ℝ) := by
        exact_mod_cast hsale
      rw [min_eq_left hsale_real]
    have hposted_le_benchmark :
        (capacity : ℝ) * bids i ≤
          boundedSupplyFixedPriceBenchmark (eraseOwnBid bids i) capacity := by
      rw [← hposted_revenue]
      exact boundedSupplySinglePriceRevenue_le_benchmark
        (eraseOwnBid bids i) capacity hi_nonneg
    have hopt_revenue :
        boundedSupplySinglePriceRevenue (eraseOwnBid bids i) capacity
            (boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity) =
          boundedSupplyFixedPriceBenchmark (eraseOwnBid bids i) capacity :=
      boundedSupplyOptimalThreshold_revenue_eq_benchmark
        (eraseOwnBid bids i) capacity
    have hopt_upper :
        boundedSupplySinglePriceRevenue (eraseOwnBid bids i) capacity
            (boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity) ≤
          (capacity : ℝ) *
            boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity := by
      unfold boundedSupplySinglePriceRevenue
      have hcount_le :
          min capacity
              (saleCount (eraseOwnBid bids i)
                (boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity)) ≤
            capacity := min_le_left _ _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount_le)
        (boundedSupplyOptimalThreshold_nonneg (eraseOwnBid bids i) capacity)
    have hstrict :
        (capacity : ℝ) *
            boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity <
          (capacity : ℝ) * bids i := by
      exact mul_lt_mul_of_pos_left hi_accepts (by exact_mod_cast hcapacity_pos)
    have hbenchmark_upper :
        boundedSupplyFixedPriceBenchmark (eraseOwnBid bids i) capacity ≤
          (capacity : ℝ) *
            boundedSupplyOptimalThreshold (eraseOwnBid bids i) capacity := by
      rw [← hopt_revenue]
      exact hopt_upper
    have : (capacity : ℝ) * bids i < (capacity : ℝ) * bids i :=
      lt_of_le_of_lt
        (hposted_le_benchmark.trans hbenchmark_upper) hstrict
    exact (lt_irrefl _ this)

theorem boundedSupplySinglePriceRevenue_full_supply
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) :
    boundedSupplySinglePriceRevenue values (Fintype.card Agent) p =
      singlePriceRevenue values p := by
  unfold boundedSupplySinglePriceRevenue
  rw [min_eq_right (by exact_mod_cast saleCount_le_card values p)]
  exact (singlePriceRevenue_eq_saleCount_mul values p).symm

theorem candidateBoundedSupplyRevenue_full_supply
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (i : Agent) :
    candidateBoundedSupplyRevenue values (Fintype.card Agent) i =
      candidateFixedPriceRevenue values 1 i := by
  classical
  by_cases hi : 0 ≤ values i
  · have hwinner : 1 ≤ saleCount values (values i) := by
      unfold saleCount
      apply Finset.one_le_card.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨by simp, le_rfl⟩⟩
    simp [candidateBoundedSupplyRevenue, candidateFixedPriceRevenue,
      hi, hwinner, boundedSupplySinglePriceRevenue_full_supply]
  · simp [candidateBoundedSupplyRevenue, candidateFixedPriceRevenue, hi]

theorem boundedSupplyFixedPriceBenchmark_full_supply
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) :
    boundedSupplyFixedPriceBenchmark values (Fintype.card Agent) =
      finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  unfold boundedSupplyFixedPriceBenchmark finiteCandidateFixedPriceBenchmark
  congr 1
  funext i
  exact candidateBoundedSupplyRevenue_full_supply values i

/-- Every unlimited-supply upper bound transports verbatim to the bounded
model at `k=n`, because that slice is definitionally the full-supply case. -/
theorem unlimitedUpperBound_transports_to_boundedSupply
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {bound : ℝ}
    (hunlimited : M.revenue values ≤
      bound * finiteCandidateFixedPriceBenchmark values 1) :
    M.revenue values ≤
      bound * boundedSupplyFixedPriceBenchmark values (Fintype.card Agent) := by
  rwa [boundedSupplyFixedPriceBenchmark_full_supply]

end


end GHW01DigitalGoods
