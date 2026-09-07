import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Count
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AppliedModelingLib
namespace Auction

/--
An unlimited-supply digital-goods auction.

The allocation quantity is represented as a real number so this same interface
can later admit fractional relaxations, lotteries in expectation, or position
auction click-through weights.  For the posted-price theorem below, allocations
are always `0` or `1`.
-/
structure DigitalGoodsAuction (Agent : Type*) where
  allocation : (Agent → ℝ) → Agent → ℝ
  payment : (Agent → ℝ) → Agent → ℝ

namespace DigitalGoodsAuction

variable {Agent : Type*}

/-- Quasilinear utility for a digital-good bidder with value `values i`. -/
def utility (M : DigitalGoodsAuction Agent)
    (values : Agent → ℝ) (i : Agent) (bids : Agent → ℝ) : ℝ :=
  values i * M.allocation bids i - M.payment bids i

/--
Dominant-strategy truthfulness for direct-report single-parameter auctions:
holding other reports fixed, replacing agent `i`'s truthful report by any
`report` cannot improve `i`'s utility.
-/
def TruthfulDominantStrategy [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

/--
Truthfulness forces the allocation probability/quantity offered to a bidder to
be monotone in that bidder's own bid. This is the reusable single-parameter
mechanism fact behind the win-probability monotonicity lemma.
-/
theorem allocation_mono_own_bid_of_truthful [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) (hM : M.TruthfulDominantStrategy)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := by
  classical
  let lowProfile : Agent → ℝ := Function.update bids i low
  let highProfile : Agent → ℝ := Function.update bids i high
  have h_update_high_low :
      Function.update highProfile i low = lowProfile := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [lowProfile, highProfile]
    · simp [lowProfile, highProfile, Function.update, hji]
  have h_update_low_high :
      Function.update lowProfile i high = highProfile := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [lowProfile, highProfile]
    · simp [lowProfile, highProfile, Function.update, hji]
  have hhigh :
      high * M.allocation lowProfile i - M.payment lowProfile i ≤
        high * M.allocation highProfile i - M.payment highProfile i := by
    simpa [DigitalGoodsAuction.utility, highProfile, h_update_high_low]
      using hM highProfile i low
  have hlow :
      low * M.allocation highProfile i - M.payment highProfile i ≤
        low * M.allocation lowProfile i - M.payment lowProfile i := by
    simpa [DigitalGoodsAuction.utility, lowProfile, h_update_low_high]
      using hM lowProfile i high
  by_contra hnot
  have hgt :
      M.allocation highProfile i < M.allocation lowProfile i :=
    lt_of_not_ge hnot
  nlinarith

/--
Algebraic form of the win-probability monotonicity lemma proof. If the two
truthfulness comparisons hold for values `bᵢ < bⱼ`, win probabilities `pᵢ,pⱼ`,
and conditional expected costs `cᵢ,cⱼ`, then the lower-value bid cannot have
larger win probability.
-/
theorem winProbability_mono_of_truthful_utility_inequalities
    {bi bj pi pj ci cj : ℝ} (hbid : bi < bj)
    (hlow : pj * (bi - cj) ≤ pi * (bi - ci))
    (hhigh : pi * (bj - ci) ≤ pj * (bj - cj)) :
    pi ≤ pj := by
  nlinarith

/--
Certificate form of the final algebra in the digital-goods revenue theorem.
After truthfulness and telescoping rewrite expected revenue as a weighted sum
of fixed-price revenues, nonnegative weights of total mass at most one and the
benchmark bound `fixedPriceRevenue i <= fixedPriceBenchmark` imply
`expectedRevenue <= fixedPriceBenchmark`.
-/
theorem expectedRevenue_le_fixedPriceBenchmark_of_weighted_certificate
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
  exact le_trans hrevenue
    (FiniteSum.weighted_sum_le_bound_of_nonneg_sum_le_one
      weight fixedPriceRevenue hweight_nonneg hweight_sum hfixed
      hbenchmark_nonneg)

/-- Truthful utility is always nonnegative. -/
def IndividuallyRational (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent), 0 ≤ M.utility values i values

/-- The mechanism never pays money to agents. -/
def NoPositiveTransfers (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent), 0 ≤ M.payment bids i

/-- Total auction revenue under a bid profile. -/
noncomputable def revenue [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (bids : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment bids i

theorem revenue_nonneg_of_noPositiveTransfers [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (hM : M.NoPositiveTransfers)
    (bids : Agent → ℝ) :
    0 ≤ M.revenue bids := by
  classical
  unfold revenue
  exact Finset.sum_nonneg fun i _ => hM bids i

end DigitalGoodsAuction

variable {Agent : Type*}

/--
An anonymous or personalized take-it-or-leave-it posted-price auction for an
unlimited-supply digital good.
-/
noncomputable def postedPrice (price : Agent → ℝ) : DigitalGoodsAuction Agent where
  allocation bids i := if price i ≤ bids i then 1 else 0
  payment bids i := if price i ≤ bids i then price i else 0

theorem postedPrice_utility_eq
    (price : Agent → ℝ) (values bids : Agent → ℝ) (i : Agent) :
    (postedPrice price).utility values i bids =
      if price i ≤ bids i then values i - price i else 0 := by
  by_cases h : price i ≤ bids i <;>
    simp [DigitalGoodsAuction.utility, postedPrice, h]

/--
Posted prices are dominant-strategy truthful in the unlimited-supply
digital-goods model.  This is the first reusable truthfulness lemma for the
2021 Test-of-Time digital-goods auction track.
-/
theorem postedPrice_truthful [DecidableEq Agent] (price : Agent → ℝ) :
    (postedPrice price).TruthfulDominantStrategy := by
  intro values i report
  have htruthUtility :
      (postedPrice price).utility values i values =
        if price i ≤ values i then values i - price i else 0 := by
    exact postedPrice_utility_eq price values values i
  have hreportUtility :
      (postedPrice price).utility values i (Function.update values i report) =
        if price i ≤ report then values i - price i else 0 := by
    rw [postedPrice_utility_eq]
    simp [Function.update]
  rw [htruthUtility, hreportUtility]
  by_cases htruth : price i ≤ values i
  · by_cases hreport : price i ≤ report
    · simp [htruth, hreport]
    · simp [htruth, hreport]
  · by_cases hreport : price i ≤ report
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (le_of_lt (lt_of_not_ge htruth))
    · simp [htruth, hreport]

theorem postedPrice_individuallyRational (price : Agent → ℝ) :
    (postedPrice price).IndividuallyRational := by
  intro values i
  rw [postedPrice_utility_eq]
  by_cases h : price i ≤ values i
  · simp [h, sub_nonneg.mpr h]
  · simp [h]

theorem postedPrice_noPositiveTransfers
    (price : Agent → ℝ) (hprice : ∀ i, 0 ≤ price i) :
    (postedPrice price).NoPositiveTransfers := by
  intro bids i
  by_cases h : price i ≤ bids i
  · simpa [postedPrice, h] using hprice i
  · simp [postedPrice, h]

theorem postedPrice_revenue_eq [Fintype Agent]
    (price : Agent → ℝ) (bids : Agent → ℝ) :
    (postedPrice price).revenue bids =
      ∑ i : Agent, if price i ≤ bids i then price i else 0 := by
  simp [DigitalGoodsAuction.revenue, postedPrice]

/--
Revenue of a single anonymous posted price against a valuation/bid profile.
For the 2021 digital-goods paper this is the basic fixed-price benchmark term.
-/
noncomputable def singlePriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Agent, if p ≤ values i then p else 0

/-- Number of bidders who accept a single price. -/
noncomputable def saleCount [Fintype Agent] (values : Agent → ℝ) (p : ℝ) : ℕ :=
  ((Finset.univ : Finset Agent).filter fun i => p ≤ values i).card

theorem saleCount_le_card [Fintype Agent] (values : Agent → ℝ) (p : ℝ) :
    saleCount values p ≤ Fintype.card Agent := by
  classical
  unfold saleCount
  simpa using
    Finset.card_filter_le (s := (Finset.univ : Finset Agent))
      (p := fun i => p ≤ values i)

theorem singlePriceRevenue_eq_saleCount_mul [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) :
    singlePriceRevenue values p = (saleCount values p : ℝ) * p := by
  classical
  rw [singlePriceRevenue, saleCount, ← Finset.sum_filter]
  simp

theorem singlePriceRevenue_nonneg [Fintype Agent]
    (values : Agent → ℝ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ singlePriceRevenue values p := by
  classical
  rw [singlePriceRevenue_eq_saleCount_mul]
  exact mul_nonneg (Nat.cast_nonneg _) hp

theorem singlePriceRevenue_le_saleCount_mul_bound [Fintype Agent]
    (values : Agent → ℝ) {p h : ℝ}
    (hp : 0 ≤ p)
    (hbound : ∀ i, values i ≤ h) :
    singlePriceRevenue values p ≤ (saleCount values p : ℝ) * h := by
  classical
  rw [singlePriceRevenue_eq_saleCount_mul]
  by_cases hcount_zero : saleCount values p = 0
  · simp [hcount_zero]
  · have hcount_pos : 0 < saleCount values p := Nat.pos_of_ne_zero hcount_zero
    have hwinners_nonempty :
        ((Finset.univ : Finset Agent).filter fun i => p ≤ values i).Nonempty := by
      apply Finset.card_pos.mp
      simpa [saleCount] using hcount_pos
    obtain ⟨i, hi⟩ := hwinners_nonempty
    have hp_le_value : p ≤ values i := (Finset.mem_filter.mp hi).2
    have hp_le_h : p ≤ h := le_trans hp_le_value (hbound i)
    exact mul_le_mul_of_nonneg_left hp_le_h (Nat.cast_nonneg _)

theorem postedPrice_const_revenue_eq_singlePriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) :
    (postedPrice fun _ : Agent => p).revenue values =
      singlePriceRevenue values p := by
  simp [postedPrice_revenue_eq, singlePriceRevenue]

/--
Certificate-style fixed-price benchmark for digital goods.

The Goldberg-Hartline-Wright benchmark is a maximum over prices satisfying
extra sale-count restrictions.  This predicate records the exact upper-bound
property without committing yet to the finite maximizer proof.
-/
def IsFixedPriceBenchmark [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (benchmark : ℝ) : Prop :=
  (∃ p, 0 ≤ p ∧ minWinners ≤ saleCount values p ∧
    benchmark = singlePriceRevenue values p) ∧
  ∀ p, 0 ≤ p → minWinners ≤ saleCount values p →
    singlePriceRevenue values p ≤ benchmark

/-- The `F^(2)`-style benchmark interface: one price, at least two winners. -/
def IsTwoWinnerFixedPriceBenchmark [Fintype Agent]
    (values : Agent → ℝ) (benchmark : ℝ) : Prop :=
  IsFixedPriceBenchmark values 2 benchmark

/-- Any fixed-price benchmark certificate has nonnegative value. -/
theorem fixedPriceBenchmark_nonneg [Fintype Agent]
    (values : Agent → ℝ) {minWinners : ℕ} {benchmark : ℝ}
    (hbenchmark : IsFixedPriceBenchmark values minWinners benchmark) :
    0 ≤ benchmark := by
  rcases hbenchmark.1 with ⟨p, hp_nonneg, _hfeasible, hbench⟩
  rw [hbench]
  exact singlePriceRevenue_nonneg values hp_nonneg

/--
Dyadic-bin certificate behind the dyadic-bin benchmark theorem. If a bin has at least a `1/m`
share of total multi-price value `T`, and all values in the bin lie between
`low` and `2 * low`, then the fixed-price benchmark is large enough to satisfy
`T <= (2*m) * benchmark`.
-/
theorem fixedPriceBenchmark_totalValue_le_of_factor_two_bin
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {benchmark T m low : ℝ} {bin : Finset Agent}
    (hbenchmark : IsFixedPriceBenchmark values 1 benchmark)
    (hbin_nonempty : bin.Nonempty)
    (hm_nonneg : 0 ≤ m)
    (hlow_nonneg : 0 ≤ low)
    (hT : T ≤ m * (∑ i ∈ bin, values i))
    (hbin_accept : ∀ i, i ∈ bin → low ≤ values i)
    (hbin_factor_two : ∀ i, i ∈ bin → values i ≤ 2 * low) :
    T ≤ (2 * m) * benchmark := by
  classical
  have hbin_subset_winners :
      bin ⊆ ((Finset.univ : Finset Agent).filter fun i => low ≤ values i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨by simp, hbin_accept i hi⟩
  have hbin_card_le_sale :
      bin.card ≤ saleCount values low := by
    unfold saleCount
    exact Finset.card_le_card hbin_subset_winners
  have hbin_card_pos : 0 < bin.card :=
    Finset.card_pos.mpr hbin_nonempty
  have hfeasible : 1 ≤ saleCount values low := by
    exact le_trans (Nat.succ_le_of_lt hbin_card_pos) hbin_card_le_sale
  have hrev_le_benchmark :
      singlePriceRevenue values low ≤ benchmark :=
    hbenchmark.2 low hlow_nonneg hfeasible
  have hbin_revenue_le_single :
      (bin.card : ℝ) * low ≤ singlePriceRevenue values low := by
    rw [singlePriceRevenue_eq_saleCount_mul]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hbin_card_le_sale) hlow_nonneg
  have hbin_sum_upper :
      (∑ i ∈ bin, values i) ≤ (∑ _i ∈ bin, 2 * low) := by
    exact Finset.sum_le_sum fun i hi => hbin_factor_two i hi
  have hbin_sum_le_two_single :
      (∑ i ∈ bin, values i) ≤ 2 * singlePriceRevenue values low := by
    calc
      (∑ i ∈ bin, values i)
          ≤ (∑ _i ∈ bin, 2 * low) := hbin_sum_upper
      _ = (bin.card : ℝ) * (2 * low) := by simp
      _ = 2 * ((bin.card : ℝ) * low) := by ring
      _ ≤ 2 * singlePriceRevenue values low := by
        nlinarith [hbin_revenue_le_single]
  have hbin_sum_le_two_benchmark :
      (∑ i ∈ bin, values i) ≤ 2 * benchmark := by
    nlinarith [hbin_sum_le_two_single, hrev_le_benchmark]
  have hm_bound :
      m * (∑ i ∈ bin, values i) ≤ m * (2 * benchmark) :=
    mul_le_mul_of_nonneg_left hbin_sum_le_two_benchmark hm_nonneg
  nlinarith

/--
Partition/candidate-bin version of the dyadic-bin benchmark theorem certificate. If a
finite family of factor-two bins accounts for total value `T`, then averaging
selects a bin carrying at least a `1 / card` share, and the fixed-price
benchmark satisfies the corresponding `2 * card` bound.
-/
theorem fixedPriceBenchmark_totalValue_le_of_factor_two_partition
    [Fintype Agent] [DecidableEq Agent]
    {Bin : Type*} [Fintype Bin] [Nonempty Bin]
    (values : Agent → ℝ) {benchmark T : ℝ}
    (bins : Bin → Finset Agent) (low : Bin → ℝ)
    (hbenchmark : IsFixedPriceBenchmark values 1 benchmark)
    (hbins_nonempty : ∀ k, (bins k).Nonempty)
    (hlow_nonneg : ∀ k, 0 ≤ low k)
    (hT : T ≤ ∑ k : Bin, ∑ i ∈ bins k, values i)
    (hbin_accept : ∀ k i, i ∈ bins k → low k ≤ values i)
    (hbin_factor_two : ∀ k i, i ∈ bins k → values i ≤ 2 * low k) :
    T ≤ (2 * (Fintype.card Bin : ℝ)) * benchmark := by
  classical
  obtain ⟨k, hkshare⟩ :=
    FiniteSum.exists_total_le_card_mul_of_le_sum
      (fun k : Bin => ∑ i ∈ bins k, values i) hT
  exact fixedPriceBenchmark_totalValue_le_of_factor_two_bin
    values hbenchmark (hbins_nonempty k)
    (by exact_mod_cast (Nat.zero_le (Fintype.card Bin)))
    (hlow_nonneg k) hkshare
    (hbin_accept k) (hbin_factor_two k)

/--
Empty-bin-safe factor-two bin bound. A nonempty bin is bounded by the
fixed-price benchmark via the posted price at its floor; an empty bin has zero
mass and is bounded by benchmark nonnegativity.
-/
theorem fixedPriceBenchmark_bin_value_le_two_benchmark_of_factor_two
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {benchmark low : ℝ} {bin : Finset Agent}
    (hbenchmark : IsFixedPriceBenchmark values 1 benchmark)
    (hlow_nonneg : 0 ≤ low)
    (hbin_accept : ∀ i, i ∈ bin → low ≤ values i)
    (hbin_factor_two : ∀ i, i ∈ bin → values i ≤ 2 * low) :
    (∑ i ∈ bin, values i) ≤ 2 * benchmark := by
  by_cases hnonempty : bin.Nonempty
  · have hbin_bound :
        (∑ i ∈ bin, values i) ≤ (2 * 1) * benchmark :=
      fixedPriceBenchmark_totalValue_le_of_factor_two_bin
        (values := values) (benchmark := benchmark)
        (T := ∑ i ∈ bin, values i) (m := 1) (low := low) (bin := bin)
        hbenchmark hnonempty (by norm_num) hlow_nonneg
        (by simp) hbin_accept hbin_factor_two
    simpa using hbin_bound
  · have hbin_empty : bin = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hbenchmark_nonneg : 0 ≤ benchmark :=
      fixedPriceBenchmark_nonneg values hbenchmark
    simp [hbin_empty]
    nlinarith

/--
Factor-two partition certificate allowing empty bins. This is the version used
by canonical dyadic partitions, where some power-of-two ranges may contain no
bidders.
-/
theorem fixedPriceBenchmark_totalValue_le_of_factor_two_partition_allow_empty
    [Fintype Agent] [DecidableEq Agent]
    {Bin : Type*} [Fintype Bin]
    (values : Agent → ℝ) {benchmark T : ℝ}
    (bins : Bin → Finset Agent) (low : Bin → ℝ)
    (hbenchmark : IsFixedPriceBenchmark values 1 benchmark)
    (hlow_nonneg : ∀ k, 0 ≤ low k)
    (hT : T ≤ ∑ k : Bin, ∑ i ∈ bins k, values i)
    (hbin_accept : ∀ k i, i ∈ bins k → low k ≤ values i)
    (hbin_factor_two : ∀ k i, i ∈ bins k → values i ≤ 2 * low k) :
    T ≤ (2 * (Fintype.card Bin : ℝ)) * benchmark := by
  have hsum_le :
      (∑ k : Bin, ∑ i ∈ bins k, values i) ≤
        ∑ _k : Bin, 2 * benchmark := by
    exact Finset.sum_le_sum fun k _hk =>
      fixedPriceBenchmark_bin_value_le_two_benchmark_of_factor_two
        values hbenchmark (hlow_nonneg k) (hbin_accept k)
        (hbin_factor_two k)
  calc
    T ≤ ∑ k : Bin, ∑ i ∈ bins k, values i := hT
    _ ≤ ∑ _k : Bin, 2 * benchmark := hsum_le
    _ = (2 * (Fintype.card Bin : ℝ)) * benchmark := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/--
Revenue from using bidder `i`'s value as the candidate single price, with
infeasible prices assigned value `0`.
-/
noncomputable def candidateFixedPriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) : ℝ :=
  if 0 ≤ values i ∧ minWinners ≤ saleCount values (values i) then
    singlePriceRevenue values (values i)
  else 0

theorem candidateFixedPriceRevenue_nonneg [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) :
    0 ≤ candidateFixedPriceRevenue values minWinners i := by
  classical
  by_cases h : 0 ≤ values i ∧ minWinners ≤ saleCount values (values i)
  · simpa [candidateFixedPriceRevenue, h] using
      singlePriceRevenue_nonneg values h.1
  · simp [candidateFixedPriceRevenue, h]

/--
Finite candidate-price benchmark obtained by maximizing over bidder values.

The full `F^(2)` theorem still needs the paper lemma that a globally optimal
single price may be chosen from a bidder value. This definition provides the
finite maximizer needed once that reduction is proved.
-/
noncomputable def finiteCandidateFixedPriceBenchmark [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    (candidateFixedPriceRevenue values minWinners)

theorem candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) :
    candidateFixedPriceRevenue values minWinners i ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  unfold finiteCandidateFixedPriceBenchmark
  exact Finset.le_sup'
    (s := (Finset.univ : Finset Agent))
    (f := candidateFixedPriceRevenue values minWinners)
    (b := i) (by simp)

theorem finiteCandidateFixedPriceBenchmark_nonneg
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateFixedPriceBenchmark values minWinners := by
  obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
  exact le_trans (candidateFixedPriceRevenue_nonneg values minWinners i)
    (candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark
      values minWinners i)

theorem singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent)
    (hprice : 0 ≤ values i)
    (hwinners : minWinners ≤ saleCount values (values i)) :
    singlePriceRevenue values (values i) ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  have hcand :
      candidateFixedPriceRevenue values minWinners i =
        singlePriceRevenue values (values i) := by
    simp [candidateFixedPriceRevenue, hprice, hwinners]
  rw [← hcand]
  exact candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark
    values minWinners i

/--
Any nonnegative feasible fixed price is dominated by a feasible bidder-value
candidate price, provided at least one winner is required.

This is the finite benchmark-reduction lemma for the digital-goods track: after
this point, it is enough to maximize over bidder values.
-/
theorem singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hfeasible : minWinners ≤ saleCount values p) :
    singlePriceRevenue values p ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  have hwinners_card : winners.card = saleCount values p := by
    simp [winners, saleCount]
  have hmin_pos : 0 < minWinners :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one hmin
  have hwinners_nonempty : winners.Nonempty := by
    apply Finset.card_pos.mp
    rw [hwinners_card]
    exact lt_of_lt_of_le hmin_pos hfeasible
  let winnerValues : Finset ℝ := winners.image values
  have hwinnerValues_nonempty : winnerValues.Nonempty :=
    hwinners_nonempty.image values
  let q : ℝ := winnerValues.min' hwinnerValues_nonempty
  have hq_mem : q ∈ winnerValues := by
    exact Finset.min'_mem winnerValues hwinnerValues_nonempty
  obtain ⟨i, hi_winner, hiq⟩ := Finset.mem_image.mp hq_mem
  have hp_le_of_winnerValue : ∀ x ∈ winnerValues, p ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact (Finset.mem_filter.mp hj).2
  have hpq : p ≤ q := by
    exact Finset.le_min' (s := winnerValues)
      (H := hwinnerValues_nonempty) p hp_le_of_winnerValue
  have hq_le_of_winner : ∀ j, j ∈ winners → q ≤ values j := by
    intro j hj
    have hmem : values j ∈ winnerValues :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    exact Finset.min'_le winnerValues (values j) hmem
  have hwinners_subset_q :
      winners ⊆
        ((Finset.univ : Finset Agent).filter fun j => q ≤ values j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨by simp, hq_le_of_winner j hj⟩
  have hcount_le : saleCount values p ≤ saleCount values q := by
    rw [← hwinners_card]
    unfold saleCount
    exact Finset.card_le_card hwinners_subset_q
  have hrev_le_q : singlePriceRevenue values p ≤ singlePriceRevenue values q := by
    rw [singlePriceRevenue_eq_saleCount_mul values p,
      singlePriceRevenue_eq_saleCount_mul values q]
    have hcount_cast :
        (saleCount values p : ℝ) ≤ (saleCount values q : ℝ) := by
      exact_mod_cast hcount_le
    have hq_nonneg : 0 ≤ q := le_trans hp hpq
    calc
      (saleCount values p : ℝ) * p
          ≤ (saleCount values p : ℝ) * q :=
            mul_le_mul_of_nonneg_left hpq (Nat.cast_nonneg _)
      _ ≤ (saleCount values q : ℝ) * q :=
            mul_le_mul_of_nonneg_right hcount_cast hq_nonneg
  have hq_nonneg : 0 ≤ q := le_trans hp hpq
  have hq_feasible : minWinners ≤ saleCount values q :=
    le_trans hfeasible hcount_le
  have hq_rev_le_benchmark :
      singlePriceRevenue values q ≤
        finiteCandidateFixedPriceBenchmark values minWinners := by
    rw [← hiq]
    exact singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
      values minWinners i (by simpa [hiq] using hq_nonneg)
      (by simpa [hiq] using hq_feasible)
  exact le_trans hrev_le_q hq_rev_le_benchmark

theorem exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    ∃ i : Agent,
      finiteCandidateFixedPriceBenchmark values minWinners =
        candidateFixedPriceRevenue values minWinners i := by
  classical
  let H : (Finset.univ : Finset Agent).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
    exact ⟨i, by simp⟩
  obtain ⟨i, _hi, hmax⟩ :=
    (Finset.univ : Finset Agent).exists_mem_eq_sup'
      (f := candidateFixedPriceRevenue values minWinners) H
  exact ⟨i, hmax⟩

/-- A bidder whose value attains the finite candidate-price benchmark. -/
noncomputable def finiteCandidateBenchmarkBidder [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : Agent :=
  Classical.choose
    (exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
      values minWinners)

/-- Candidate price selected from a benchmark-attaining bidder value. -/
noncomputable def finiteCandidateBenchmarkPrice [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  values (finiteCandidateBenchmarkBidder values minWinners)

/--
Nonnegative offer price extracted from the finite candidate benchmark. If the
selected bidder value is not a feasible nonnegative candidate, use price `0`.
-/
noncomputable def finiteCandidateOfferPrice [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  let i := finiteCandidateBenchmarkBidder values minWinners
  if 0 ≤ values i ∧ minWinners ≤ saleCount values (values i) then
    values i
  else
    0

/-- Candidate offer prices are either zero or one of the submitted bidder values. -/
noncomputable def finiteCandidatePriceSet [Fintype Agent]
    (values : Agent → ℝ) : Finset ℝ :=
  insert 0 ((Finset.univ : Finset Agent).image values)

theorem finiteCandidateOfferPrice_mem_priceSet [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    finiteCandidateOfferPrice values minWinners ∈
      finiteCandidatePriceSet values := by
  classical
  let i := finiteCandidateBenchmarkBidder values minWinners
  by_cases hsel : 0 ≤ values i ∧ minWinners ≤ saleCount values (values i)
  · simp [finiteCandidateOfferPrice, finiteCandidatePriceSet, i, hsel]
  · simp [finiteCandidateOfferPrice, finiteCandidatePriceSet, i, hsel]

theorem finiteCandidateOfferPrice_nonneg [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateOfferPrice values minWinners := by
  classical
  let i := finiteCandidateBenchmarkBidder values minWinners
  by_cases h : 0 ≤ values i ∧ minWinners ≤ saleCount values (values i)
  · simp [finiteCandidateOfferPrice, i, h]
  · simp [finiteCandidateOfferPrice, i, h]

theorem finiteCandidateOfferPrice_le_of_values_le
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) {h : ℝ}
    (hh_nonneg : 0 ≤ h)
    (hbound : ∀ i, values i ≤ h) :
    finiteCandidateOfferPrice values minWinners ≤ h := by
  classical
  let i := finiteCandidateBenchmarkBidder values minWinners
  by_cases hsel : 0 ≤ values i ∧ minWinners ≤ saleCount values (values i)
  · simpa [finiteCandidateOfferPrice, i, hsel] using hbound i
  · simpa [finiteCandidateOfferPrice, i, hsel] using hh_nonneg

theorem finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    finiteCandidateFixedPriceBenchmark values minWinners =
      candidateFixedPriceRevenue values minWinners
        (finiteCandidateBenchmarkBidder values minWinners) := by
  exact Classical.choose_spec
    (exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
      values minWinners)

theorem singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    singlePriceRevenue values
      (finiteCandidateOfferPrice values minWinners) =
        finiteCandidateFixedPriceBenchmark values minWinners := by
  classical
  let i := finiteCandidateBenchmarkBidder values minWinners
  have hbench :
      finiteCandidateFixedPriceBenchmark values minWinners =
        candidateFixedPriceRevenue values minWinners i := by
    simpa [i] using
      finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
        values minWinners
  by_cases hsel : 0 ≤ values i ∧
      minWinners ≤ saleCount values (values i)
  · have hprice :
        finiteCandidateOfferPrice values minWinners = values i := by
      simp [finiteCandidateOfferPrice, i, hsel]
    rw [hprice, hbench]
    simp [candidateFixedPriceRevenue, hsel]
  · have hprice :
        finiteCandidateOfferPrice values minWinners = 0 := by
      simp [finiteCandidateOfferPrice, i, hsel]
    have hbench_zero :
        finiteCandidateFixedPriceBenchmark values minWinners = 0 := by
      simpa [candidateFixedPriceRevenue, hsel] using hbench
    rw [hprice, hbench_zero]
    simp [singlePriceRevenue]

/--
If all bidder values are at least one and the finite candidate benchmark is
positive, then the selected nonnegative candidate offer price is also at least
one. The only alternative in `finiteCandidateOfferPrice` is the fallback price
`0`, which would make the selected benchmark revenue zero.
-/
theorem finiteCandidateOfferPrice_ge_one_of_benchmark_pos
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hbenchmark_pos :
      0 < finiteCandidateFixedPriceBenchmark values minWinners) :
    1 ≤ finiteCandidateOfferPrice values minWinners := by
  classical
  let i := finiteCandidateBenchmarkBidder values minWinners
  by_cases h : 0 ≤ values i ∧ minWinners ≤ saleCount values (values i)
  · simpa [finiteCandidateOfferPrice, i, h] using hvalue_ge_one i
  · have hprice_zero :
        finiteCandidateOfferPrice values minWinners = 0 := by
      simp [finiteCandidateOfferPrice, i, h]
    have hbenchmark_zero :
        finiteCandidateFixedPriceBenchmark values minWinners = 0 := by
      rw [← singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark
        values minWinners, hprice_zero]
      simp [singlePriceRevenue]
    nlinarith

theorem finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ}
    (hmin : 1 ≤ minWinners)
    (hexists : ∃ p, 0 ≤ p ∧ minWinners ≤ saleCount values p) :
    IsFixedPriceBenchmark values minWinners
      (finiteCandidateFixedPriceBenchmark values minWinners) := by
  classical
  constructor
  · let i := finiteCandidateBenchmarkBidder values minWinners
    have hbench :
        finiteCandidateFixedPriceBenchmark values minWinners =
          candidateFixedPriceRevenue values minWinners i := by
      simpa [i] using
        finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
          values minWinners
    by_cases hsel : 0 ≤ values i ∧
        minWinners ≤ saleCount values (values i)
    · refine ⟨values i, hsel.1, hsel.2, ?_⟩
      simpa [candidateFixedPriceRevenue, hsel] using hbench
    · have hbench_zero :
          finiteCandidateFixedPriceBenchmark values minWinners = 0 := by
        simpa [candidateFixedPriceRevenue, hsel] using hbench
      obtain ⟨p, hp, hfeasible⟩ := hexists
      have hrev_le :
          singlePriceRevenue values p ≤
            finiteCandidateFixedPriceBenchmark values minWinners :=
        singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
          values hmin hp hfeasible
      have hrev_nonneg : 0 ≤ singlePriceRevenue values p :=
        singlePriceRevenue_nonneg values hp
      have hrev_zero : singlePriceRevenue values p = 0 := by
        exact le_antisymm (by simpa [hbench_zero] using hrev_le) hrev_nonneg
      refine ⟨p, hp, hfeasible, ?_⟩
      rw [hbench_zero, hrev_zero]
  · intro p hp hfeasible
    exact singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      values hmin hp hfeasible

theorem finiteCandidateFixedPriceBenchmark_isTwoWinnerFixedPriceBenchmark_of_feasible
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ)
    (hexists : ∃ p, 0 ≤ p ∧ 2 ≤ saleCount values p) :
    IsTwoWinnerFixedPriceBenchmark values
      (finiteCandidateFixedPriceBenchmark values 2) := by
  exact finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible
    values (minWinners := 2) (by decide) hexists

/--
A threshold price rule is own-bid independent when changing bidder `i`'s report
does not change the price offered to `i`.
-/
def OwnBidIndependent [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent) (report : ℝ),
    threshold (Function.update bids i report) i = threshold bids i

/-- Bid profile with bidder `i`'s own bid erased to `0`. -/
def eraseOwnBid [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) : Agent → ℝ :=
  Function.update bids i 0

theorem eraseOwnBid_update_self [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) (report : ℝ) :
    eraseOwnBid (Function.update bids i report) i = eraseOwnBid bids i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [eraseOwnBid]
  · simp [eraseOwnBid, Function.update, h]

/--
Build a threshold rule from a pricing rule that only sees bidder `i`'s own bid
after it has been erased. This is the direct formal hook for random-sampling
and market-price auctions whose offer to `i` is computed from other bidders.
-/
def ownErasedThreshold [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i => priceRule i (eraseOwnBid bids i)

theorem ownErasedThreshold_ownBidIndependent [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    OwnBidIndependent (ownErasedThreshold priceRule) := by
  intro bids i report
  exact congrArg (priceRule i) (eraseOwnBid_update_self bids i report)

/-- Keep bids on one side of a sample partition and zero the rest. -/
def restrictBidsBySide (side : Agent → Bool) (keep : Bool)
    (bids : Agent → ℝ) : Agent → ℝ :=
  fun j => if side j = keep then bids j else 0

theorem finiteCandidateOfferPrice_restrictBidsBySide_mem_priceSet
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (minWinners : ℕ) :
    finiteCandidateOfferPrice
        (restrictBidsBySide side keep values) minWinners ∈
      finiteCandidatePriceSet values := by
  classical
  let restricted := restrictBidsBySide side keep values
  let i := finiteCandidateBenchmarkBidder restricted minWinners
  by_cases hsel : 0 ≤ restricted i ∧ minWinners ≤ saleCount restricted (restricted i)
  · by_cases hkeep : side i = keep
    · have hprice :
          finiteCandidateOfferPrice restricted minWinners = values i := by
        have hsel' :
            0 ≤ values i ∧ minWinners ≤ saleCount restricted (values i) := by
          simpa [restricted, restrictBidsBySide, hkeep] using hsel
        simp [finiteCandidateOfferPrice, restricted, restrictBidsBySide, i, hsel', hkeep]
      rw [hprice]
      simp [finiteCandidatePriceSet]
    · have hprice :
          finiteCandidateOfferPrice restricted minWinners = 0 := by
        have hprice_restricted :
            finiteCandidateOfferPrice restricted minWinners = restricted i := by
          simp [finiteCandidateOfferPrice, i, hsel]
        have hrestricted_zero : restricted i = 0 := by
          simp [restricted, restrictBidsBySide, hkeep]
        rw [hprice_restricted, hrestricted_zero]
      rw [hprice]
      simp [finiteCandidatePriceSet]
  · have hprice :
        finiteCandidateOfferPrice restricted minWinners = 0 := by
      simp [finiteCandidateOfferPrice, restricted, i, hsel]
    rw [hprice]
    simp [finiteCandidatePriceSet]

/-- Number of members of a finite set that lie on a chosen sample side. -/
noncomputable def sideCountInSet
    (side : Agent → Bool) (keep : Bool) (s : Finset Agent) : ℕ :=
  (s.filter fun i => side i = keep).card

theorem sideCountInSet_eq_sum_indicator
    (side : Agent → Bool) (keep : Bool) (s : Finset Agent) :
    (sideCountInSet side keep s : ℝ) =
      ∑ i ∈ s, if side i = keep then (1 : ℝ) else 0 := by
  classical
  rw [sideCountInSet, ← Finset.sum_filter]
  simp

theorem sideCountInSet_add_not_eq_card
    (side : Agent → Bool) (keep : Bool) (s : Finset Agent) :
    sideCountInSet side keep s + sideCountInSet side (!keep) s = s.card := by
  classical
  have hbool : ∀ b : Bool, (b = !keep) ↔ ¬ b = keep := by
    intro b
    cases keep <;> cases b <;> simp
  unfold sideCountInSet
  rw [show s.filter (fun i => side i = !keep) =
      s.filter (fun i => ¬ side i = keep) by
        ext i
        simp [hbool (side i)]]
  exact Finset.card_filter_add_card_filter_not
    (s := s) (p := fun i => side i = keep)

/--
Paper-style top-prefix interface for finite digital-goods bid profiles.  The
set `top m` represents the `m` highest bids.  The only property Section 6
needs is threshold closure: if at most `m` agents accept price `p`, then all
agents accepting `p` lie in the top `m` prefix.
-/
structure TopPrefixFamily [Fintype Agent] (values : Agent → ℝ) where
  top : ℕ → Finset Agent
  card_top : ∀ {m : ℕ}, m ≤ Fintype.card Agent → (top m).card = m
  threshold_subset :
    ∀ {p : ℝ} {m : ℕ},
      saleCount values p ≤ m →
      m ≤ Fintype.card Agent →
        ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆ top m

/-- The first `m` indices of `Fin n`, used as the concrete sorted top prefix. -/
def finPrefixByIndex (n m : ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun i : Fin n => i.val < m

theorem finPrefixByIndex_card {n m : ℕ} (hm : m ≤ n) :
    (finPrefixByIndex n m).card = m := by
  rw [finPrefixByIndex, ← Fintype.card_coe]
  let e : {i : Fin n // i.val < m} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun j => ⟨⟨j.val, lt_of_lt_of_le j.2 hm⟩, j.2⟩
      left_inv := by
        intro x
        cases x with
        | mk i hi => simp
      right_inv := by
        intro j
        cases j with
        | mk j hj => simp }
  simpa using Fintype.card_congr e

/--
Concrete top-prefix family for a finite bid vector indexed in nonincreasing
order.  The top `m` bids are simply indices `< m`.
-/
def finSortedTopPrefixFamily {n : ℕ} (values : Fin n → ℝ)
    (hmono : ∀ i j : Fin n, i.val ≤ j.val → values j ≤ values i) :
    TopPrefixFamily values where
  top m := finPrefixByIndex n m
  card_top := by
    intro m hm
    exact finPrefixByIndex_card
      (n := n) (m := m) (by simpa [Fintype.card_fin] using hm)
  threshold_subset := by
    intro p m hsale hm i hi
    have hi_win : p ≤ values i := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    by_contra hnot
    have hmi : m ≤ i.val := Nat.le_of_not_gt hnot
    let pref : Finset (Fin n) := finPrefixByIndex n m
    let winners : Finset (Fin n) :=
      (Finset.univ : Finset (Fin n)).filter fun j => p ≤ values j
    have hprefix_card : pref.card = m := by
      simpa [pref, Fintype.card_fin] using
        finPrefixByIndex_card
          (n := n) (m := m) (by simpa [Fintype.card_fin] using hm)
    have hi_not_prefix : i ∉ pref := by
      simp [pref, finPrefixByIndex, hnot]
    have hprefix_subset : pref ⊆ winners := by
      intro j hj
      have hj_lt : j.val < m := by
        simpa [pref, finPrefixByIndex] using hj
      have hji : j.val ≤ i.val := le_trans (Nat.le_of_lt hj_lt) hmi
      have hv : values i ≤ values j := hmono j i hji
      exact Finset.mem_filter.mpr ⟨by simp, le_trans hi_win hv⟩
    have hi_winner : i ∈ winners :=
      Finset.mem_filter.mpr ⟨by simp, hi_win⟩
    have hinsert_subset : insert i pref ⊆ winners := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjp
      · exact hi_winner
      · exact hprefix_subset hjp
    have hcard_insert : (insert i pref).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hi_not_prefix, hprefix_card]
    have hcard_le : m + 1 ≤ saleCount values p := by
      have h := Finset.card_le_card hinsert_subset
      rw [hcard_insert] at h
      simpa [winners, saleCount] using h
    omega

/-- Number of bidders on a chosen sample side who accept price `p` in the
original bid profile. -/
noncomputable def sideSaleCount [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) : ℕ :=
  ((Finset.univ : Finset Agent).filter fun i => side i = keep ∧ p ≤ values i).card

theorem sideSaleCount_eq_sum_indicator_winners [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) :
    (sideSaleCount side keep values p : ℝ) =
      ∑ i ∈ ((Finset.univ : Finset Agent).filter fun i => p ≤ values i),
        if side i = keep then (1 : ℝ) else 0 := by
  classical
  have hfilter :
      ((Finset.univ : Finset Agent).filter fun i =>
          side i = keep ∧ p ≤ values i) =
        (((Finset.univ : Finset Agent).filter fun i => p ≤ values i).filter
          fun i => side i = keep) := by
    ext i
    simp [and_comm]
  rw [sideSaleCount, hfilter, ← Finset.sum_filter]
  simp

theorem sideSaleCount_le_sideCountInSet_of_winner_subset
    [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) {s : Finset Agent}
    (hsubset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆ s) :
    sideSaleCount side keep values p ≤ sideCountInSet side keep s := by
  classical
  unfold sideSaleCount sideCountInSet
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨_hi_univ, hside, hp⟩
  exact Finset.mem_filter.mpr
    ⟨hsubset (Finset.mem_filter.mpr ⟨by simp, hp⟩), hside⟩

theorem sideSaleCount_add_not_eq_saleCount [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) :
    sideSaleCount side keep values p +
        sideSaleCount side (!keep) values p =
      saleCount values p := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  have hbool : ∀ b : Bool, (b = !keep) ↔ ¬ b = keep := by
    intro b
    cases keep <;> cases b <;> simp
  have hkeep :
      ((Finset.univ : Finset Agent).filter fun i =>
          side i = keep ∧ p ≤ values i) =
        winners.filter fun i => side i = keep := by
    ext i
    simp [winners, and_comm]
  have hnot :
      ((Finset.univ : Finset Agent).filter fun i =>
          side i = !keep ∧ p ≤ values i) =
        winners.filter fun i => ¬ side i = keep := by
    ext i
    simp [winners, hbool (side i), and_comm]
  unfold sideSaleCount saleCount
  rw [hkeep, hnot, Finset.card_filter_add_card_filter_not]

theorem sideSaleCount_le_two_not_of_saleCount_le_three_not [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ)
    (hcount :
      saleCount values p ≤ 3 * sideSaleCount side (!keep) values p) :
    sideSaleCount side keep values p ≤
      2 * sideSaleCount side (!keep) values p := by
  have hsum := sideSaleCount_add_not_eq_saleCount side keep values p
  omega

theorem sideSaleCount_le_saleCount_restrictBidsBySide [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) :
    sideSaleCount side keep values p ≤
      saleCount (restrictBidsBySide side keep values) p := by
  classical
  unfold sideSaleCount saleCount
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hi_univ, hside, hp⟩
  exact Finset.mem_filter.mpr
    ⟨hi_univ, by simpa [restrictBidsBySide, hside] using hp⟩

/--
If `m` bidders on a sample side accept price `p`, then the restricted profile's
single-price revenue at `p` is at least `m*p`.
-/
theorem sideSaleCount_mul_price_le_singlePriceRevenue_restrictBidsBySide
    [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {p : ℝ} (hp : 0 ≤ p) :
    (sideSaleCount side keep values p : ℝ) * p ≤
      singlePriceRevenue (restrictBidsBySide side keep values) p := by
  rw [singlePriceRevenue_eq_saleCount_mul]
  exact mul_le_mul_of_nonneg_right
    (by
      exact_mod_cast
        sideSaleCount_le_saleCount_restrictBidsBySide side keep values p)
    hp

/--
Section 6 deterministic bridge: if enough optimal-price winners fall on a
sample side, the finite candidate benchmark of the restricted profile is at
least the revenue from those sampled winners at that price.
-/
theorem sideSaleCount_mul_price_le_finiteCandidateBenchmark_restrictBidsBySide
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hcount : minWinners ≤ sideSaleCount side keep values p) :
    (sideSaleCount side keep values p : ℝ) * p ≤
      finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side keep values) minWinners := by
  have hside_le_sale :
      sideSaleCount side keep values p ≤
        saleCount (restrictBidsBySide side keep values) p :=
    sideSaleCount_le_saleCount_restrictBidsBySide side keep values p
  have hfeasible :
      minWinners ≤ saleCount (restrictBidsBySide side keep values) p :=
    le_trans hcount hside_le_sale
  have hsingle_le :
      singlePriceRevenue (restrictBidsBySide side keep values) p ≤
        finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners :=
    singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      (restrictBidsBySide side keep values) hmin hp hfeasible
  exact le_trans
    (sideSaleCount_mul_price_le_singlePriceRevenue_restrictBidsBySide
      side keep values hp)
    hsingle_le

/--
Section 6 deterministic sample-good bridge. If a chosen sample side contains
at least a third of the original winners at price `p`, then the original
single-price revenue at `p` is at most three times the restricted sample
benchmark.
-/
theorem singlePriceRevenue_le_three_finiteCandidateBenchmark_restrictBidsBySide
    [Fintype Agent] [Nonempty Agent]
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
  rw [singlePriceRevenue_eq_saleCount_mul]
  have hcount_cast :
      (saleCount values p : ℝ) ≤
        3 * (sideSaleCount side keep values p : ℝ) := by
    exact_mod_cast hthird
  have hrev_count :
      (saleCount values p : ℝ) * p ≤
        (3 * (sideSaleCount side keep values p : ℝ)) * p :=
    mul_le_mul_of_nonneg_right hcount_cast hp
  have hsample :
      (sideSaleCount side keep values p : ℝ) * p ≤
        finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners :=
    sideSaleCount_mul_price_le_finiteCandidateBenchmark_restrictBidsBySide
      side keep values hmin hp hcount_min
  calc
    (saleCount values p : ℝ) * p
        ≤ (3 * (sideSaleCount side keep values p : ℝ)) * p := hrev_count
    _ = 3 * ((sideSaleCount side keep values p : ℝ) * p) := by ring
    _ ≤ 3 * finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners := by
        exact mul_le_mul_of_nonneg_left hsample (by norm_num)

/-- Revenue from a single posted price restricted to one side of a partition. -/
noncomputable def sidePriceRevenue [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Agent, if side i = keep ∧ p ≤ values i then p else 0

theorem sidePriceRevenue_eq_sideSaleCount_mul [Fintype Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (p : ℝ) :
    sidePriceRevenue side keep values p =
      (sideSaleCount side keep values p : ℝ) * p := by
  classical
  rw [sidePriceRevenue, sideSaleCount, ← Finset.sum_filter]
  simp

/-! ## Weighted Pairing Auction -/

/-- Total bid value `T` used by the weighted-pairing auction. -/
noncomputable def totalBidValue [Fintype Agent] (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, values i

/--
For nonnegative bid profiles, revenue from any anonymous fixed price is bounded
by the total bid value.
-/
theorem singlePriceRevenue_le_totalBidValue_of_nonneg
    [Fintype Agent] (values : Agent → ℝ) (p : ℝ)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i) :
    singlePriceRevenue values p ≤ totalBidValue values := by
  classical
  unfold singlePriceRevenue totalBidValue
  exact Finset.sum_le_sum fun i _hi => by
    by_cases hwin : p ≤ values i
    · simpa [hwin] using hwin
    · simp [hwin, hvalues_nonneg i]

/--
Expected payment of bidder `i` in the weighted-pairing auction. Bidder `i`
draws another bidder `j` with probability proportional to `values j`; if
`values j <= values i`, bidder `i` wins and pays `values j`.
-/
noncomputable def weightedPairingExpectedPayment
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (i : Agent) : ℝ :=
  ∑ j : Agent,
    if j ≠ i ∧ values j ≤ values i then
      (values j) ^ 2 / (totalBidValue values - values i)
    else
      0

/-- Expected revenue of the weighted-pairing auction. -/
noncomputable def weightedPairingExpectedRevenue
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, weightedPairingExpectedPayment values i

theorem weightedPairingExpectedRevenue_eq_sum_payments
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) :
    weightedPairingExpectedRevenue values =
      ∑ i : Agent, weightedPairingExpectedPayment values i := by
  rfl

theorem weightedPairingExpectedPayment_eq_filtered_square_sum_div
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (i : Agent) :
    weightedPairingExpectedPayment values i =
      (∑ j ∈ (Finset.univ : Finset Agent).filter
          (fun j => j ≠ i ∧ values j ≤ values i),
        (values j) ^ 2) /
        (totalBidValue values - values i) := by
  rw [weightedPairingExpectedPayment]
  rw [Finset.sum_filter]
  conv_rhs => rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases h : j ≠ i ∧ values j ≤ values i <;>
      simp [h, div_eq_mul_inv]

theorem weightedPairingExpectedPayment_le_div_of_filtered_square_sum_le
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (i : Agent) {numeratorBound : ℝ}
    (hnum :
      (∑ j ∈ (Finset.univ : Finset Agent).filter
          (fun j => j ≠ i ∧ values j ≤ values i),
        (values j) ^ 2) ≤ numeratorBound)
    (hden_nonneg : 0 ≤ totalBidValue values - values i) :
    weightedPairingExpectedPayment values i ≤
      numeratorBound / (totalBidValue values - values i) := by
  rw [weightedPairingExpectedPayment_eq_filtered_square_sum_div]
  exact div_le_div_of_nonneg_right hnum hden_nonneg

theorem weightedPairingExpectedRevenue_nonneg_of_den_nonneg
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ)
    (hden : ∀ i : Agent, 0 ≤ totalBidValue values - values i) :
    0 ≤ weightedPairingExpectedRevenue values := by
  classical
  unfold weightedPairingExpectedRevenue weightedPairingExpectedPayment
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => by
      by_cases hpair : j ≠ i ∧ values j ≤ values i
      · simp [hpair, div_nonneg (sq_nonneg (values j)) (hden i)]
      · simp [hpair]

theorem finiteCandidateFixedPriceBenchmark_restrictBidsBySide_le_sideSaleCount_mul_bound
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (minWinners : ℕ) {h : ℝ}
    (hh_nonneg : 0 ≤ h)
    (hbound : ∀ i, values i ≤ h) :
    finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side keep values) minWinners ≤
      (sideSaleCount side keep values
        (finiteCandidateOfferPrice
          (restrictBidsBySide side keep values) minWinners) : ℝ) * h := by
  classical
  let restricted := restrictBidsBySide side keep values
  let q := finiteCandidateOfferPrice restricted minWinners
  have hp_nonneg : 0 ≤ q :=
    finiteCandidateOfferPrice_nonneg restricted minWinners
  have hrestricted_bound : ∀ i, restricted i ≤ h := by
    intro i
    by_cases hkeep : side i = keep
    · simpa [restricted, restrictBidsBySide, hkeep] using hbound i
    · simpa [restricted, restrictBidsBySide, hkeep] using hh_nonneg
  have hq_le_h : q ≤ h := by
    simpa [restricted, q] using
      finiteCandidateOfferPrice_le_of_values_le
        restricted minWinners hh_nonneg hrestricted_bound
  have hbench_eq :
      finiteCandidateFixedPriceBenchmark restricted minWinners =
        singlePriceRevenue restricted q := by
    rw [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark]
  rcases hp_nonneg.eq_or_lt with hp_zero | hp_pos
  · have hbench_zero :
        finiteCandidateFixedPriceBenchmark restricted minWinners = 0 := by
      rw [hbench_eq, ← hp_zero]
      simp [singlePriceRevenue]
    rw [hbench_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hh_nonneg
  have hside_count :
      sideSaleCount side keep values q =
        saleCount restricted q := by
    unfold sideSaleCount saleCount restricted restrictBidsBySide
    congr 1
    ext i
    by_cases hkeep : side i = keep
    · simp [hkeep]
    · have hp_not_zero : ¬ q ≤ (0 : ℝ) := not_le_of_gt hp_pos
      simp [hkeep, hp_not_zero]
  have hsingle_eq :
      singlePriceRevenue restricted q =
        (sideSaleCount side keep values q : ℝ) * q := by
    rw [singlePriceRevenue_eq_saleCount_mul]
    rw [← hside_count]
  rw [hbench_eq, hsingle_eq]
  exact mul_le_mul_of_nonneg_left hq_le_h (Nat.cast_nonneg _)

theorem restrictBidsBySide_update_of_not_kept [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (bids : Agent → ℝ) (i : Agent) (report : ℝ)
    (hkeep : side i ≠ keep) :
    restrictBidsBySide side keep (Function.update bids i report) =
      restrictBidsBySide side keep bids := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [restrictBidsBySide, hkeep]
  · simp [restrictBidsBySide, Function.update, hji]

/--
Finite-candidate cross-sample threshold rule: each bidder is offered the
candidate benchmark price computed from the opposite side of the partition.
-/
noncomputable def crossSampleCandidateThreshold
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i =>
    finiteCandidateBenchmarkPrice
      (restrictBidsBySide side (!side i) bids) minWinners

theorem crossSampleCandidateThreshold_ownBidIndependent
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    OwnBidIndependent (crossSampleCandidateThreshold side minWinners) := by
  intro bids i report
  unfold crossSampleCandidateThreshold
  apply congrArg (fun profile =>
    finiteCandidateBenchmarkPrice profile minWinners)
  apply restrictBidsBySide_update_of_not_kept
  cases side i <;> simp

/--
Cross-sample threshold rule using the nonnegative finite candidate offer price.
This is the deterministic core of the RSOP auction for a fixed partition.
-/
noncomputable def crossSampleCandidateOfferThreshold
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i =>
    finiteCandidateOfferPrice
      (restrictBidsBySide side (!side i) bids) minWinners

theorem crossSampleCandidateOfferThreshold_ownBidIndependent
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    OwnBidIndependent (crossSampleCandidateOfferThreshold side minWinners) := by
  intro bids i report
  unfold crossSampleCandidateOfferThreshold
  apply congrArg (fun profile =>
    finiteCandidateOfferPrice profile minWinners)
  apply restrictBidsBySide_update_of_not_kept
  cases side i <;> simp

theorem crossSampleCandidateOfferThreshold_nonneg
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (minWinners : ℕ)
    (bids : Agent → ℝ) (i : Agent) :
    0 ≤ crossSampleCandidateOfferThreshold side minWinners bids i := by
  exact finiteCandidateOfferPrice_nonneg
    (restrictBidsBySide side (!side i) bids) minWinners

/--
Digital-goods auction that offers every bidder a threshold price and sells iff
the bid meets that threshold.
-/
noncomputable def thresholdPriceAuction [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : DigitalGoodsAuction Agent where
  allocation bids i := if threshold bids i ≤ bids i then 1 else 0
  payment bids i := if threshold bids i ≤ bids i then threshold bids i else 0

theorem thresholdPriceAuction_utility_eq [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (values bids : Agent → ℝ) (i : Agent) :
    (thresholdPriceAuction threshold).utility values i bids =
      if threshold bids i ≤ bids i then values i - threshold bids i else 0 := by
  by_cases h : threshold bids i ≤ bids i <;>
    simp [DigitalGoodsAuction.utility, thresholdPriceAuction, h]

/--
Own-bid independent threshold-price auctions are dominant-strategy truthful.
This is the reusable DSIC core for random-sampling and market-price
digital-goods auctions.
-/
theorem thresholdPriceAuction_truthful [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hind : OwnBidIndependent threshold) :
    (thresholdPriceAuction threshold).TruthfulDominantStrategy := by
  intro values i report
  have htruthUtility :
      (thresholdPriceAuction threshold).utility values i values =
        if threshold values i ≤ values i then
          values i - threshold values i
        else 0 := by
    exact thresholdPriceAuction_utility_eq threshold values values i
  have hreportUtility :
      (thresholdPriceAuction threshold).utility values i
          (Function.update values i report) =
        if threshold values i ≤ report then
          values i - threshold values i
        else 0 := by
    rw [thresholdPriceAuction_utility_eq]
    simp [Function.update, hind values i report]
  rw [htruthUtility, hreportUtility]
  by_cases htruth : threshold values i ≤ values i
  · by_cases hreport : threshold values i ≤ report
    · simp [htruth, hreport]
    · simp [htruth, hreport]
  · by_cases hreport : threshold values i ≤ report
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (le_of_lt (lt_of_not_ge htruth))
    · simp [htruth, hreport]

theorem ownErasedThresholdPriceAuction_truthful [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    (thresholdPriceAuction
      (ownErasedThreshold priceRule)).TruthfulDominantStrategy := by
  exact thresholdPriceAuction_truthful _
    (ownErasedThreshold_ownBidIndependent priceRule)

theorem crossSampleCandidateThresholdPriceAuction_truthful
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (thresholdPriceAuction
      (crossSampleCandidateThreshold side minWinners)).TruthfulDominantStrategy := by
  exact thresholdPriceAuction_truthful _
    (crossSampleCandidateThreshold_ownBidIndependent side minWinners)

theorem crossSampleCandidateOfferThresholdPriceAuction_truthful
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (thresholdPriceAuction
      (crossSampleCandidateOfferThreshold side minWinners)).TruthfulDominantStrategy := by
  exact thresholdPriceAuction_truthful _
    (crossSampleCandidateOfferThreshold_ownBidIndependent side minWinners)

theorem thresholdPriceAuction_individuallyRational [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) :
    (thresholdPriceAuction threshold).IndividuallyRational := by
  intro values i
  rw [thresholdPriceAuction_utility_eq]
  by_cases h : threshold values i ≤ values i
  · simp [h, sub_nonneg.mpr h]
  · simp [h]

theorem thresholdPriceAuction_noPositiveTransfers [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hthreshold : ∀ bids i, 0 ≤ threshold bids i) :
    (thresholdPriceAuction threshold).NoPositiveTransfers := by
  intro bids i
  by_cases h : threshold bids i ≤ bids i
  · simpa [thresholdPriceAuction, h] using hthreshold bids i
  · simp [thresholdPriceAuction, h]

theorem crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (thresholdPriceAuction
      (crossSampleCandidateOfferThreshold side minWinners)).NoPositiveTransfers := by
  exact thresholdPriceAuction_noPositiveTransfers _
    (crossSampleCandidateOfferThreshold_nonneg side minWinners)

/--
For a fixed sample side, the cross-sample offer auction earns at least the
posted-price revenue from the opposite side at the price selected from that
sample.
-/
theorem sidePriceRevenue_opposite_finiteCandidateOfferPrice_le_crossSampleRevenue
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (minWinners : ℕ) :
    sidePriceRevenue side (!keep) values
        (finiteCandidateOfferPrice
          (restrictBidsBySide side keep values) minWinners) ≤
      (thresholdPriceAuction
        (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
  classical
  let p :=
    finiteCandidateOfferPrice
      (restrictBidsBySide side keep values) minWinners
  unfold DigitalGoodsAuction.revenue sidePriceRevenue
  refine Finset.sum_le_sum ?_
  intro i _hi
  by_cases hwin : side i = !keep ∧ p ≤ values i
  · have hp_accept : p ≤ values i := hwin.2
    have hthreshold :
        crossSampleCandidateOfferThreshold side minWinners values i = p := by
      cases keep <;> cases hside : side i <;>
        simp [crossSampleCandidateOfferThreshold, p, hside] at hwin ⊢
    have hleft :
        (if side i = !keep ∧ p ≤ values i then p else 0) = p := by
      simp [hwin]
    have hright :
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners)).payment values i = p := by
      simp [thresholdPriceAuction, hthreshold, hp_accept]
    rw [hleft, hright]
  · have hnpt :
        0 ≤
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).payment values i :=
      crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers
        side minWinners values i
    have hleft :
        (if side i = !keep ∧ p ≤ values i then p else 0) = 0 := by
      simp [hwin]
    rw [hleft]
    exact hnpt

/--
Section 6 deterministic revenue-good bridge. If the non-sample side has at
least half as many acceptors as the sample side at the sample-selected offer
price, the cross-sample auction revenue is at least half of the sample
benchmark.
-/
theorem finiteCandidateBenchmark_restrictBidsBySide_le_two_crossSampleRevenue
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
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
  classical
  let p :=
    finiteCandidateOfferPrice
      (restrictBidsBySide side keep values) minWinners
  have hsample_revenue :
      finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners =
        singlePriceRevenue (restrictBidsBySide side keep values) p := by
    rw [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark]
  have hsample_count :
      singlePriceRevenue (restrictBidsBySide side keep values) p =
        (saleCount (restrictBidsBySide side keep values) p : ℝ) * p := by
    exact singlePriceRevenue_eq_saleCount_mul
      (restrictBidsBySide side keep values) p
  have hp_nonneg :
      0 ≤ p := by
    exact finiteCandidateOfferPrice_nonneg
      (restrictBidsBySide side keep values) minWinners
  rcases hp_nonneg.eq_or_lt with hp_zero | hp_pos
  · have hbench_zero :
        finiteCandidateFixedPriceBenchmark
            (restrictBidsBySide side keep values) minWinners = 0 := by
      rw [hsample_revenue, ← hp_zero]
      simp [singlePriceRevenue]
    have hrevenue_nonneg :
        0 ≤
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).revenue values :=
      DigitalGoodsAuction.revenue_nonneg_of_noPositiveTransfers
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners))
        (crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers
          side minWinners)
        values
    rw [hbench_zero]
    nlinarith
  have hcount_cast :
      (saleCount (restrictBidsBySide side keep values) p : ℝ) ≤
        2 * (sideSaleCount side (!keep) values p : ℝ) := by
    have hside_count :
        sideSaleCount side keep values p =
          saleCount (restrictBidsBySide side keep values) p := by
      classical
      unfold sideSaleCount saleCount restrictBidsBySide
      congr 1
      ext i
      by_cases hkeep : side i = keep
      · simp [hkeep]
      · have hp_not_zero : ¬ p ≤ (0 : ℝ) := not_le_of_gt hp_pos
        simp [hkeep, hp_not_zero]
    rw [← hside_count]
    exact_mod_cast hhalf
  have hsample_le_opposite :
      singlePriceRevenue (restrictBidsBySide side keep values) p ≤
        2 * sidePriceRevenue side (!keep) values p := by
    rw [hsample_count, sidePriceRevenue_eq_sideSaleCount_mul]
    calc
      (saleCount (restrictBidsBySide side keep values) p : ℝ) * p
          ≤ (2 * (sideSaleCount side (!keep) values p : ℝ)) * p :=
            mul_le_mul_of_nonneg_right hcount_cast hp_nonneg
      _ = 2 * ((sideSaleCount side (!keep) values p : ℝ) * p) := by ring
  have hopp :
      sidePriceRevenue side (!keep) values p ≤
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
    simpa [p] using
      sidePriceRevenue_opposite_finiteCandidateOfferPrice_le_crossSampleRevenue
        side keep values minWinners
  calc
    finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side keep values) minWinners
        = singlePriceRevenue (restrictBidsBySide side keep values) p :=
          hsample_revenue
    _ ≤ 2 * sidePriceRevenue side (!keep) values p := hsample_le_opposite
    _ ≤ 2 *
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).revenue values :=
        mul_le_mul_of_nonneg_left hopp (by norm_num)

/--
Uniform average revenue of the deterministic cross-sample offer auction over
all sample partitions.
-/
noncomputable def averageCrossSampleCandidateOfferRevenue
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  (∑ side : Agent → Bool,
      (thresholdPriceAuction
        (crossSampleCandidateOfferThreshold side minWinners)).revenue values) /
    (Fintype.card (Agent → Bool) : ℝ)

theorem averageCrossSampleCandidateOfferRevenue_nonneg
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ averageCrossSampleCandidateOfferRevenue values minWinners := by
  classical
  unfold averageCrossSampleCandidateOfferRevenue
  have hsum :
      0 ≤ ∑ side : Agent → Bool,
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
    exact Finset.sum_nonneg fun side _ =>
      DigitalGoodsAuction.revenue_nonneg_of_noPositiveTransfers _
        (crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers
          side minWinners)
        values
  have hcard_nonneg : 0 ≤ (Fintype.card (Agent → Bool) : ℝ) := by
    exact_mod_cast (Nat.zero_le _ : 0 ≤ Fintype.card (Agent → Bool))
  exact div_nonneg hsum hcard_nonneg

/-- The finite `F^(2)` fixed-price benchmark value. -/
noncomputable def twoWinnerFixedPriceBenchmarkValue
    [Fintype Agent] [Nonempty Agent] (values : Agent → ℝ) : ℝ :=
  finiteCandidateFixedPriceBenchmark values 2

/--
Certificate that the cross-sample offer auction is `ratio`-competitive against
the two-winner fixed-price benchmark.
-/
def CrossSampleOfferApproximationCertificate
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (ratio : ℝ) : Prop :=
  twoWinnerFixedPriceBenchmarkValue values ≤
    ratio * averageCrossSampleCandidateOfferRevenue values 2

theorem crossSampleOffer_competitive_of_certificate
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (ratio : ℝ)
    (hcert : CrossSampleOfferApproximationCertificate values ratio) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      ratio * averageCrossSampleCandidateOfferRevenue values 2 := by
  exact hcert

/-! ### Two-value deterministic bid-independent lower-bound model -/

/--
Revenue of a deterministic bid-independent threshold rule on a two-value input.
`usesHighPrice nh nl = true` means that a bidder whose own bid is erased is
offered the high price `H`; `false` means the bidder is offered price `1`.
The arguments `nh,nl` are the numbers of high- and low-valued bidders visible
after erasing the bidder being priced.
-/
def twoValueBidIndependentThresholdRevenue
    (usesHighPrice : ℕ → ℕ → Bool) (H highCount lowCount : ℕ) : ℝ :=
  (highCount : ℝ) *
      (if usesHighPrice (highCount - 1) lowCount then (H : ℝ) else 1) +
    (lowCount : ℝ) *
      (if usesHighPrice highCount (lowCount - 1) then 0 else 1)

/--
At a low-to-high threshold transition, all high bidders pay `1` and all low
bidders are rejected, so revenue is at most the high-bid count.
-/
theorem twoValueBidIndependentThresholdRevenue_transition_bound
    (usesHighPrice : ℕ → ℕ → Bool) (H highCount lowCount : ℕ)
    (hhigh : usesHighPrice (highCount - 1) lowCount = false)
    (hlow : usesHighPrice highCount (lowCount - 1) = true) :
    twoValueBidIndependentThresholdRevenue usesHighPrice H highCount lowCount ≤
      (highCount : ℝ) := by
  simp [twoValueBidIndependentThresholdRevenue, hhigh, hlow]

/--
If low bidders are offered the high price, then the two-value auction revenue
is at most `H * highCount`: low bidders are rejected and each high bidder pays
at most the high price.
-/
theorem twoValueBidIndependentThresholdRevenue_start_high_bound
    (usesHighPrice : ℕ → ℕ → Bool) (H highCount lowCount : ℕ)
    (hH_ge_one : 1 ≤ (H : ℝ))
    (hlow : usesHighPrice highCount (lowCount - 1) = true) :
    twoValueBidIndependentThresholdRevenue usesHighPrice H highCount lowCount ≤
      (H : ℝ) * (highCount : ℝ) := by
  by_cases hhigh : usesHighPrice (highCount - 1) lowCount = true
  · simp [twoValueBidIndependentThresholdRevenue, hhigh, hlow, mul_comm]
  · have hhigh_false : usesHighPrice (highCount - 1) lowCount = false := by
      cases h : usesHighPrice (highCount - 1) lowCount
      · rfl
      · exact False.elim (hhigh h)
    simp [twoValueBidIndependentThresholdRevenue, hhigh_false, hlow]
    have hcount_nonneg : 0 ≤ (highCount : ℝ) := by exact_mod_cast Nat.zero_le highCount
    nlinarith

/--
Finite construction for the deterministic-threshold lower-bound theorem on binary values. For any deterministic
bid-independent two-price rule that uses the high price on the all-high endpoint,
there is a two-value input whose revenue is an `O(1/H)` fraction of the fixed
price benchmark lower bound, while the side condition `alpha * H <= F` holds.

The paper sets `m = h^2 alpha`; this theorem keeps the exact lower-bound
condition on `m` explicit so it can be reused with any integer scale.
-/
theorem twoValueBidIndependent_exists_low_revenue_witness
    (usesHighPrice : ℕ → ℕ → Bool) {H alpha m : ℕ}
    (hH_ge_one : 1 ≤ (H : ℝ))
    (halpha_lt_m : alpha < m)
    (hm_large : (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) ≤ (m + 1 : ℝ))
    (hend : usesHighPrice m 0 = true) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (H : ℝ) *
          twoValueBidIndependentThresholdRevenue usesHighPrice H highCount lowCount ≤
        fixedPriceLowerBound ∧
      (H : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  have hH_nonneg : 0 ≤ (H : ℝ) := le_trans zero_le_one hH_ge_one
  by_cases hstart : usesHighPrice alpha (m - alpha) = true
  · refine ⟨alpha, m - alpha + 1, (m + 1 : ℝ), ?_, ?_⟩
    · have hlow :
          usesHighPrice alpha ((m - alpha + 1) - 1) = true := by
        simpa using hstart
      have hrev :=
        twoValueBidIndependentThresholdRevenue_start_high_bound
          usesHighPrice H alpha (m - alpha + 1) hH_ge_one hlow
      have hmul :
          (H : ℝ) *
              twoValueBidIndependentThresholdRevenue
                usesHighPrice H alpha (m - alpha + 1) ≤
            (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) :=
        mul_le_mul_of_nonneg_left hrev hH_nonneg
      exact le_trans hmul hm_large
    · have halpha_nonneg : 0 ≤ (alpha : ℝ) := by exact_mod_cast Nat.zero_le alpha
      have hside_to_square :
          (H : ℝ) * (alpha : ℝ) ≤
            (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) := by
        calc
          (H : ℝ) * (alpha : ℝ) =
              1 * ((H : ℝ) * (alpha : ℝ)) := by ring
          _ ≤ (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hH_ge_one
                (mul_nonneg hH_nonneg halpha_nonneg)
      exact le_trans hside_to_square hm_large
  · have hstart_false : usesHighPrice alpha (m - alpha) = false := by
      cases h : usesHighPrice alpha (m - alpha)
      · rfl
      · exact False.elim (hstart h)
    obtain ⟨k, halpha_lt_k, hk_le_m, hkprev, hkcurr⟩ :=
      FiniteSum.exists_bool_transition
        (fun k => usesHighPrice k (m - k))
        halpha_lt_m hstart_false (by simpa using hend)
    refine ⟨k, m - k + 1, (H : ℝ) * (k : ℝ), ?_, ?_⟩
    · have hprev :
          usesHighPrice (k - 1) (m - k + 1) = false := by
        have hk_pos : 0 < k :=
          lt_of_le_of_lt (Nat.zero_le alpha) halpha_lt_k
        have hlow_eq : m - (k - 1) = m - k + 1 :=
          FiniteSum.nat_sub_pred_eq_sub_add_one_of_pos_le hk_pos hk_le_m
        simpa [hlow_eq] using hkprev
      have hcurr :
          usesHighPrice k ((m - k + 1) - 1) = true := by
        simpa using hkcurr
      have hrev :=
        twoValueBidIndependentThresholdRevenue_transition_bound
          usesHighPrice H k (m - k + 1) hprev hcurr
      exact le_trans
        (mul_le_mul_of_nonneg_left hrev hH_nonneg)
        (le_refl ((H : ℝ) * (k : ℝ)))
    · have halpha_le_k : alpha ≤ k := le_of_lt halpha_lt_k
      have halpha_cast : (alpha : ℝ) ≤ (k : ℝ) := by exact_mod_cast halpha_le_k
      exact mul_le_mul_of_nonneg_left halpha_cast hH_nonneg

/--
Revenue of an arbitrary deterministic bid-independent threshold price rule on
a two-value input with high value `H` and low value `1`.

The price offered to a high bidder sees one fewer high bidder; the price offered
to a low bidder sees one fewer low bidder. A bidder pays the threshold exactly
when her value meets it.
-/
noncomputable def twoValueBidIndependentPriceRevenue
    (price : ℕ → ℕ → ℝ) (H highCount lowCount : ℕ) : ℝ :=
  (highCount : ℝ) *
      (if price (highCount - 1) lowCount ≤ (H : ℝ) then
        price (highCount - 1) lowCount else 0) +
    (lowCount : ℝ) *
      (if price highCount (lowCount - 1) ≤ 1 then
        price highCount (lowCount - 1) else 0)

/-- Concrete bidder type for a binary-valued input with `highCount` high bids
and `lowCount` low bids. -/
abbrev TwoValueAgent (highCount lowCount : ℕ) :=
  Fin highCount ⊕ Fin lowCount

/-- Binary-valued bid profile with high value `H` and low value `1`. -/
def twoValueBidProfile (H highCount lowCount : ℕ) :
    TwoValueAgent highCount lowCount → ℝ
  | Sum.inl _ => (H : ℝ)
  | Sum.inr _ => 1

theorem singlePriceRevenue_twoValueBidProfile_one
    {H highCount lowCount : ℕ}
    (hH_ge_one : 1 ≤ (H : ℝ)) :
    singlePriceRevenue (twoValueBidProfile H highCount lowCount) 1 =
      (highCount + lowCount : ℝ) := by
  classical
  unfold singlePriceRevenue
  simp [twoValueBidProfile, hH_ge_one, Finset.sum_const, nsmul_eq_mul]

theorem singlePriceRevenue_twoValueBidProfile_high
    {H highCount lowCount : ℕ}
    (hH_gt_one : 1 < (H : ℝ)) :
    singlePriceRevenue (twoValueBidProfile H highCount lowCount) (H : ℝ) =
      (H : ℝ) * (highCount : ℝ) := by
  classical
  have hlow : ¬ (H : ℝ) ≤ 1 := not_le_of_gt hH_gt_one
  unfold singlePriceRevenue
  simp [twoValueBidProfile, hlow, Finset.sum_const, nsmul_eq_mul]
  ring

/--
The one-winner finite fixed-price benchmark on a binary two-value input. The
empty-profile fallback is zero; all Section 9 witnesses below are nonempty.
-/
noncomputable def twoValueFixedPriceBenchmark
    (H highCount lowCount : ℕ) : ℝ :=
  if hzero : highCount + lowCount = 0 then 0 else
    @finiteCandidateFixedPriceBenchmark
      (TwoValueAgent highCount lowCount) inferInstance
      (by
        have hsum_pos : 0 < highCount + lowCount :=
          Nat.pos_of_ne_zero hzero
        by_cases hhigh_pos : 0 < highCount
        · exact ⟨Sum.inl ⟨0, hhigh_pos⟩⟩
        · have hhigh_zero : highCount = 0 :=
            Nat.eq_zero_of_not_pos hhigh_pos
          have hlow_pos : 0 < lowCount := by
            by_contra hlow_not
            have hlow_zero : lowCount = 0 :=
              Nat.eq_zero_of_not_pos hlow_not
            simp [hhigh_zero, hlow_zero] at hsum_pos
          exact ⟨Sum.inr ⟨0, hlow_pos⟩⟩)
      (twoValueBidProfile H highCount lowCount) 1

/--
Canonical erased-bid list for a binary input: `highCount` copies of the high
value followed by `lowCount` copies of the low value `1`.
-/
def twoValueErasedBidList (H highCount lowCount : ℕ) : List ℝ :=
  List.replicate highCount (H : ℝ) ++ List.replicate lowCount 1

/--
Restrict a paper-style anonymous bid-independent price rule on erased bid
lists to binary inputs. On binary inputs the canonical list is determined by
the high/low counts, which is the count-threshold model used in the deterministic-threshold lower-bound theorem.
-/
def twoValueListBidIndependentThresholdPrice
    (priceRule : List ℝ → ℝ) (H : ℕ) : ℕ → ℕ → ℝ :=
  fun highCount lowCount =>
    priceRule (twoValueErasedBidList H highCount lowCount)

/-- Count high-value bids in an anonymous binary erased-bid list. -/
noncomputable def twoValueHighCountInList (H : ℕ) (bids : List ℝ) : ℕ :=
  bids.countP fun x => decide (x = (H : ℝ))

/-- Count low-value `1` bids in an anonymous binary erased-bid list. -/
noncomputable def twoValueLowCountInList (_H : ℕ) (bids : List ℝ) : ℕ :=
  bids.countP fun x => decide (x = (1 : ℝ))

/--
Convert a count-threshold binary price rule into anonymous erased-bid-list
form by counting high and low values in the list.
-/
noncomputable def twoValueCountListPriceRule
    (thresholdPrice : ℕ → ℕ → ℝ) (H : ℕ) : List ℝ → ℝ :=
  fun bids =>
    thresholdPrice (twoValueHighCountInList H bids)
      (twoValueLowCountInList H bids)

theorem list_countP_replicate_eq {α : Type*} (p : α → Bool) (a : α) :
    ∀ n : ℕ, (List.replicate n a).countP p =
      if p a = true then n else 0
  | 0 => by simp [List.countP_nil]
  | n + 1 => by
      rw [List.replicate_succ, List.countP_cons,
        list_countP_replicate_eq p a n]
      by_cases h : p a = true <;> simp [h]

theorem twoValueErasedBidList_highCount
    {H highCount lowCount : ℕ} (hH_ne_one : (H : ℝ) ≠ 1) :
    twoValueHighCountInList H
        (twoValueErasedBidList H highCount lowCount) =
      highCount := by
  classical
  rw [twoValueHighCountInList, twoValueErasedBidList, List.countP_append,
    list_countP_replicate_eq, list_countP_replicate_eq]
  have hne : (1 : ℝ) ≠ H := hH_ne_one.symm
  simp [hne]

theorem twoValueErasedBidList_lowCount
    {H highCount lowCount : ℕ} (hH_ne_one : (H : ℝ) ≠ 1) :
    twoValueLowCountInList H
        (twoValueErasedBidList H highCount lowCount) =
      lowCount := by
  classical
  rw [twoValueLowCountInList, twoValueErasedBidList, List.countP_append,
    list_countP_replicate_eq, list_countP_replicate_eq]
  simp [hH_ne_one]

theorem twoValueListBidIndependentThresholdPrice_countListPriceRule
    (thresholdPrice : ℕ → ℕ → ℝ) {H : ℕ}
    (hH_ne_one : (H : ℝ) ≠ 1) :
    twoValueListBidIndependentThresholdPrice
        (twoValueCountListPriceRule thresholdPrice H) H =
      thresholdPrice := by
  funext highCount lowCount
  rw [twoValueListBidIndependentThresholdPrice, twoValueCountListPriceRule,
    twoValueErasedBidList_highCount hH_ne_one,
    twoValueErasedBidList_lowCount hH_ne_one]

theorem finiteCandidateFixedPriceBenchmark_twoValue_one_price_ge_total
    {H highCount lowCount : ℕ}
    [Nonempty (TwoValueAgent highCount lowCount)]
    (hH_ge_one : 1 ≤ (H : ℝ)) :
    (highCount + lowCount : ℝ) ≤
      twoValueFixedPriceBenchmark H highCount lowCount := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty (TwoValueAgent highCount lowCount))
  have hsum_pos : 0 < highCount + lowCount := by
    cases i with
    | inl hi =>
        have hhigh_pos : 0 < highCount :=
          lt_of_le_of_lt (Nat.zero_le hi.val) hi.2
        exact lt_of_lt_of_le hhigh_pos (Nat.le_add_right highCount lowCount)
    | inr lo =>
        have hlow_pos : 0 < lowCount :=
          lt_of_le_of_lt (Nat.zero_le lo.val) lo.2
        have hlow_le_sum : lowCount ≤ highCount + lowCount := by
          rw [Nat.add_comm]
          exact Nat.le_add_right lowCount highCount
        exact lt_of_lt_of_le hlow_pos hlow_le_sum
  have hsum_ne : highCount + lowCount ≠ 0 := ne_of_gt hsum_pos
  have hi_accept : 1 ≤ twoValueBidProfile H highCount lowCount i := by
    cases i <;> simp [twoValueBidProfile, hH_ge_one]
  have hfilter_nonempty :
      ((Finset.univ : Finset (TwoValueAgent highCount lowCount)).filter
          fun i => 1 ≤ twoValueBidProfile H highCount lowCount i).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨by simp, hi_accept⟩⟩
  have hfeasible :
      1 ≤ saleCount (twoValueBidProfile H highCount lowCount) 1 := by
    unfold saleCount
    exact Finset.card_pos.mpr hfilter_nonempty
  have hrev_le :
      singlePriceRevenue
          (twoValueBidProfile H highCount lowCount) 1 ≤
        finiteCandidateFixedPriceBenchmark
          (twoValueBidProfile H highCount lowCount) 1 :=
    singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      (twoValueBidProfile H highCount lowCount)
      (minWinners := 1) (by decide) (by norm_num) hfeasible
  rw [twoValueFixedPriceBenchmark, dif_neg hsum_ne]
  simpa [singlePriceRevenue_twoValueBidProfile_one hH_ge_one] using hrev_le

theorem finiteCandidateFixedPriceBenchmark_twoValue_high_price_ge
    {H highCount lowCount : ℕ}
    [Nonempty (TwoValueAgent highCount lowCount)]
    (hH_ge_two : 2 ≤ H) (hhigh_pos : 0 < highCount) :
    (H : ℝ) * (highCount : ℝ) ≤
      twoValueFixedPriceBenchmark H highCount lowCount := by
  classical
  have hsum_pos : 0 < highCount + lowCount :=
    lt_of_lt_of_le hhigh_pos (Nat.le_add_right highCount lowCount)
  have hsum_ne : highCount + lowCount ≠ 0 := ne_of_gt hsum_pos
  have hH_gt_one : 1 < (H : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hH_ge_two)
  have hfeasible :
      1 ≤ saleCount
        (twoValueBidProfile H highCount lowCount) (H : ℝ) := by
    let i : TwoValueAgent highCount lowCount := Sum.inl ⟨0, hhigh_pos⟩
    have hi_accept : (H : ℝ) ≤ twoValueBidProfile H highCount lowCount i := by
      simp [i, twoValueBidProfile]
    have hfilter_nonempty :
        ((Finset.univ : Finset (TwoValueAgent highCount lowCount)).filter
            fun i => (H : ℝ) ≤
              twoValueBidProfile H highCount lowCount i).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨by simp, hi_accept⟩⟩
    unfold saleCount
    exact Finset.card_pos.mpr hfilter_nonempty
  have hrev_le :
      singlePriceRevenue
          (twoValueBidProfile H highCount lowCount) (H : ℝ) ≤
        finiteCandidateFixedPriceBenchmark
          (twoValueBidProfile H highCount lowCount) 1 :=
    singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      (twoValueBidProfile H highCount lowCount)
      (minWinners := 1) (by decide)
      (by exact_mod_cast (Nat.zero_le H : 0 ≤ H)) hfeasible
  rw [twoValueFixedPriceBenchmark, dif_neg hsum_ne]
  simpa [singlePriceRevenue_twoValueBidProfile_high hH_gt_one] using hrev_le

/--
Threshold rule induced by a count-based bid-independent price function on the
concrete binary-valued bidder type.
-/
def twoValueCountThresholdPrice
    (price : ℕ → ℕ → ℝ) (highCount lowCount : ℕ) :
    (TwoValueAgent highCount lowCount → ℝ) →
      TwoValueAgent highCount lowCount → ℝ :=
  fun _ i =>
    match i with
    | Sum.inl _ => price (highCount - 1) lowCount
    | Sum.inr _ => price highCount (lowCount - 1)

/--
The count-threshold revenue formula is exactly the concrete threshold-auction
revenue on the binary-valued bidder type.
-/
theorem thresholdPriceAuction_twoValueCountThreshold_revenue_eq
    (price : ℕ → ℕ → ℝ) (H highCount lowCount : ℕ) :
    (thresholdPriceAuction
      (twoValueCountThresholdPrice price highCount lowCount)).revenue
        (twoValueBidProfile H highCount lowCount) =
      twoValueBidIndependentPriceRevenue price H highCount lowCount := by
  classical
  rw [DigitalGoodsAuction.revenue]
  rw [Fintype.sum_sum_type]
  simp [thresholdPriceAuction, twoValueCountThresholdPrice,
    twoValueBidProfile, twoValueBidIndependentPriceRevenue, Finset.sum_const,
    nsmul_eq_mul]

/--
For arbitrary threshold prices, a low-to-high transition still forces revenue
at most the number of high bidders: high bidders are offered price at most `1`,
while low bidders are offered price above `1` and reject.
-/
theorem twoValueBidIndependentPriceRevenue_transition_bound
    (price : ℕ → ℕ → ℝ) (H highCount lowCount : ℕ)
    (hH_ge_one : 1 ≤ (H : ℝ))
    (hhigh : price (highCount - 1) lowCount ≤ 1)
    (hlow : 1 < price highCount (lowCount - 1)) :
    twoValueBidIndependentPriceRevenue price H highCount lowCount ≤
      (highCount : ℝ) := by
  have hH_nonneg : 0 ≤ (H : ℝ) := le_trans zero_le_one hH_ge_one
  have hhigh_le_H : price (highCount - 1) lowCount ≤ (H : ℝ) :=
    le_trans hhigh hH_ge_one
  have hlow_not_le : ¬ price highCount (lowCount - 1) ≤ 1 :=
    not_le_of_gt hlow
  simp [twoValueBidIndependentPriceRevenue, hhigh_le_H, hlow_not_le]
  have hcount_nonneg : 0 ≤ (highCount : ℝ) := by exact_mod_cast Nat.zero_le highCount
  nlinarith

/--
If low bidders are offered a price above `1`, arbitrary threshold-price revenue
is at most `H * highCount`.
-/
theorem twoValueBidIndependentPriceRevenue_start_high_bound
    (price : ℕ → ℕ → ℝ) (H highCount lowCount : ℕ)
    (hH_ge_one : 1 ≤ (H : ℝ))
    (hlow : 1 < price highCount (lowCount - 1)) :
    twoValueBidIndependentPriceRevenue price H highCount lowCount ≤
      (H : ℝ) * (highCount : ℝ) := by
  have hH_nonneg : 0 ≤ (H : ℝ) := le_trans zero_le_one hH_ge_one
  have hlow_not_le : ¬ price highCount (lowCount - 1) ≤ 1 :=
    not_le_of_gt hlow
  by_cases hhigh : price (highCount - 1) lowCount ≤ (H : ℝ)
  · simp [twoValueBidIndependentPriceRevenue, hhigh, hlow_not_le]
    have hcount_nonneg : 0 ≤ (highCount : ℝ) := by exact_mod_cast Nat.zero_le highCount
    calc
      (highCount : ℝ) * price (highCount - 1) lowCount
          ≤ (highCount : ℝ) * (H : ℝ) :=
            mul_le_mul_of_nonneg_left hhigh hcount_nonneg
      _ = (H : ℝ) * (highCount : ℝ) := by ring
  · simp [twoValueBidIndependentPriceRevenue, hhigh, hlow_not_le]
    have hcount_nonneg : 0 ≤ (highCount : ℝ) := by exact_mod_cast Nat.zero_le highCount
    exact mul_nonneg hH_nonneg hcount_nonneg

/--
If the all-high erased profile is offered price at most `1`, the all-high input
with one additional bidder already gives the `1/H` revenue-ratio witness.
-/
theorem twoValueBidIndependentPriceRevenue_all_high_low_offer_bound
    (price : ℕ → ℕ → ℝ) (H m : ℕ)
    (hH_ge_one : 1 ≤ (H : ℝ))
    (hend_low : price m 0 ≤ 1) :
    twoValueBidIndependentPriceRevenue price H (m + 1) 0 ≤
      (m + 1 : ℝ) := by
  have hend_le_H : price m 0 ≤ (H : ℝ) :=
    le_trans hend_low hH_ge_one
  simp [twoValueBidIndependentPriceRevenue, hend_le_H]
  have hm_nonneg : 0 ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.zero_le (m + 1)
  nlinarith

/--
Deterministic-threshold lower-bound theorem for arbitrary deterministic bid-independent threshold prices
on binary values. There is a two-value input whose revenue is at most a `1/H`
fraction of a feasible fixed-price benchmark lower bound, while
`alpha * H <= F` holds.
-/
theorem twoValueBidIndependentPrice_exists_low_revenue_witness
    (price : ℕ → ℕ → ℝ) {H alpha m : ℕ}
    (hH_ge_one : 1 ≤ (H : ℝ))
    (halpha_lt_m : alpha < m)
    (hm_large : (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) ≤ (m + 1 : ℝ)) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (H : ℝ) *
          twoValueBidIndependentPriceRevenue price H highCount lowCount ≤
        fixedPriceLowerBound ∧
      (H : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  classical
  have hH_nonneg : 0 ≤ (H : ℝ) := le_trans zero_le_one hH_ge_one
  by_cases hend_low : price m 0 ≤ 1
  · refine ⟨m + 1, 0, (H : ℝ) * (m + 1 : ℝ), ?_, ?_⟩
    · have hrev :=
        twoValueBidIndependentPriceRevenue_all_high_low_offer_bound
          price H m hH_ge_one hend_low
      exact mul_le_mul_of_nonneg_left hrev hH_nonneg
    · have halpha_le_m_succ : alpha ≤ m + 1 :=
        Nat.le_trans (le_of_lt halpha_lt_m) (Nat.le_succ m)
      have halpha_cast : (alpha : ℝ) ≤ (m + 1 : ℝ) := by
        exact_mod_cast halpha_le_m_succ
      exact mul_le_mul_of_nonneg_left halpha_cast hH_nonneg
  · have hend_high : 1 < price m 0 := lt_of_not_ge hend_low
    let highOffer : ℕ → Bool := fun k => decide (1 < price k (m - k))
    by_cases hstart : 1 < price alpha (m - alpha)
    · refine ⟨alpha, m - alpha + 1, (m + 1 : ℝ), ?_, ?_⟩
      · have hlow :
            1 < price alpha ((m - alpha + 1) - 1) := by
          simpa using hstart
        have hrev :=
          twoValueBidIndependentPriceRevenue_start_high_bound
            price H alpha (m - alpha + 1) hH_ge_one hlow
        have hmul :
            (H : ℝ) *
                twoValueBidIndependentPriceRevenue
                  price H alpha (m - alpha + 1) ≤
              (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) :=
          mul_le_mul_of_nonneg_left hrev hH_nonneg
        exact le_trans hmul hm_large
      · have halpha_nonneg : 0 ≤ (alpha : ℝ) := by exact_mod_cast Nat.zero_le alpha
        have hside_to_square :
            (H : ℝ) * (alpha : ℝ) ≤
              (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) := by
          calc
            (H : ℝ) * (alpha : ℝ) =
                1 * ((H : ℝ) * (alpha : ℝ)) := by ring
            _ ≤ (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hH_ge_one
                  (mul_nonneg hH_nonneg halpha_nonneg)
        exact le_trans hside_to_square hm_large
    · have hstart_false : highOffer alpha = false := by
        dsimp [highOffer]
        simp [hstart]
      have hend_true : highOffer m = true := by
        dsimp [highOffer]
        simpa using hend_high
      obtain ⟨k, halpha_lt_k, hk_le_m, hkprev, hkcurr⟩ :=
        FiniteSum.exists_bool_transition highOffer halpha_lt_m
          hstart_false hend_true
      refine ⟨k, m - k + 1, (H : ℝ) * (k : ℝ), ?_, ?_⟩
      · have hk_pos : 0 < k :=
          lt_of_le_of_lt (Nat.zero_le alpha) halpha_lt_k
        have hlow_eq : m - (k - 1) = m - k + 1 :=
          FiniteSum.nat_sub_pred_eq_sub_add_one_of_pos_le hk_pos hk_le_m
        have hprev_not : ¬ 1 < price (k - 1) (m - (k - 1)) := by
          dsimp [highOffer] at hkprev
          by_contra hgt
          simp [hgt] at hkprev
        have hprev_le : price (k - 1) (m - k + 1) ≤ 1 := by
          simpa [hlow_eq] using le_of_not_gt hprev_not
        have hcurr_gt_old : 1 < price k (m - k) := by
          dsimp [highOffer] at hkcurr
          by_contra hnot
          simp [hnot] at hkcurr
        have hcurr_gt :
            1 < price k ((m - k + 1) - 1) := by
          simpa using hcurr_gt_old
        have hrev :=
          twoValueBidIndependentPriceRevenue_transition_bound
            price H k (m - k + 1) hH_ge_one hprev_le hcurr_gt
        exact le_trans
          (mul_le_mul_of_nonneg_left hrev hH_nonneg)
          (le_refl ((H : ℝ) * (k : ℝ)))
      · have halpha_le_k : alpha ≤ k := le_of_lt halpha_lt_k
        have halpha_cast : (alpha : ℝ) ≤ (k : ℝ) := by exact_mod_cast halpha_le_k
        exact mul_le_mul_of_nonneg_left halpha_cast hH_nonneg

/--
The scaled choice `m = H^2 * alpha` for the arbitrary-threshold deterministic
lower-bound construction.
-/
theorem twoValueBidIndependentPrice_exists_low_revenue_witness_scaled
    (price : ℕ → ℕ → ℝ) {H alpha : ℕ}
    (hH_ge_two : 2 ≤ H) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (H : ℝ) *
          twoValueBidIndependentPriceRevenue price H highCount lowCount ≤
        fixedPriceLowerBound ∧
      (H : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  let m : ℕ := H * H * alpha
  have hH_ge_one_nat : 1 ≤ H := le_trans (by decide : 1 ≤ 2) hH_ge_two
  have hH_ge_one_real : 1 ≤ (H : ℝ) := by exact_mod_cast hH_ge_one_nat
  have hfactor_ge_four : 4 ≤ H * H :=
    Nat.mul_le_mul hH_ge_two hH_ge_two
  have hfactor_gt_one : 1 < H * H :=
    lt_of_lt_of_le (by decide : 1 < 4) hfactor_ge_four
  have halpha_lt_m : alpha < m := by
    dsimp [m]
    exact (Nat.lt_mul_iff_one_lt_left halpha_pos).2 hfactor_gt_one
  have hm_large :
      (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) ≤
        (m + 1 : ℝ) := by
    dsimp [m]
    simp
    nlinarith
  exact twoValueBidIndependentPrice_exists_low_revenue_witness
    (price := price) (H := H) (alpha := alpha) (m := m)
    hH_ge_one_real halpha_lt_m hm_large

/--
The deterministic-threshold lower-bound theorem with the scaled finite
construction and the actual fixed-price benchmark on the constructed two-value
input. This strengthens the certificate-valued witness above by proving the
witness lower bound is feasible for the one-winner fixed-price benchmark `F`.
-/
theorem twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark_attained
    (price : ℕ → ℕ → ℝ) {H alpha : ℕ}
    (hH_ge_two : 2 ≤ H) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (H : ℝ) *
          twoValueBidIndependentPriceRevenue price H highCount lowCount ≤
        twoValueFixedPriceBenchmark H highCount lowCount ∧
      (H : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark H highCount lowCount := by
  classical
  let m : ℕ := H * H * alpha
  have hH_ge_one_nat : 1 ≤ H := le_trans (by decide : 1 ≤ 2) hH_ge_two
  have hH_ge_one_real : 1 ≤ (H : ℝ) := by exact_mod_cast hH_ge_one_nat
  have hH_nonneg : 0 ≤ (H : ℝ) := by
    exact_mod_cast (Nat.zero_le H : 0 ≤ H)
  have hfactor_ge_four : 4 ≤ H * H :=
    Nat.mul_le_mul hH_ge_two hH_ge_two
  have hfactor_gt_one : 1 < H * H :=
    lt_of_lt_of_le (by decide : 1 < 4) hfactor_ge_four
  have halpha_lt_m : alpha < m := by
    dsimp [m]
    exact (Nat.lt_mul_iff_one_lt_left halpha_pos).2 hfactor_gt_one
  have hm_large :
      (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) ≤
        (m + 1 : ℝ) := by
    dsimp [m]
    simp
    nlinarith
  by_cases hend_low : price m 0 ≤ 1
  · refine ⟨m + 1, 0, Nat.succ_pos m, ?_⟩
    haveI : Nonempty (TwoValueAgent (m + 1) 0) :=
      ⟨Sum.inl ⟨0, Nat.succ_pos m⟩⟩
    have hrev :=
      twoValueBidIndependentPriceRevenue_all_high_low_offer_bound
        price H m hH_ge_one_real hend_low
    have hbench :
        (H : ℝ) * (m + 1 : ℝ) ≤
          twoValueFixedPriceBenchmark H (m + 1) 0 := by
      simpa [Nat.cast_add] using
        (finiteCandidateFixedPriceBenchmark_twoValue_high_price_ge
          (H := H) (highCount := m + 1) (lowCount := 0)
          hH_ge_two (Nat.succ_pos m))
    constructor
    · exact le_trans (mul_le_mul_of_nonneg_left hrev hH_nonneg) hbench
    · have halpha_le_m_succ : alpha ≤ m + 1 :=
        Nat.le_trans (le_of_lt halpha_lt_m) (Nat.le_succ m)
      have halpha_cast : (alpha : ℝ) ≤ (m + 1 : ℝ) := by
        exact_mod_cast halpha_le_m_succ
      exact le_trans
        (mul_le_mul_of_nonneg_left halpha_cast hH_nonneg) hbench
  · have hend_high : 1 < price m 0 := lt_of_not_ge hend_low
    let highOffer : ℕ → Bool := fun k => decide (1 < price k (m - k))
    by_cases hstart : 1 < price alpha (m - alpha)
    · refine ⟨alpha, m - alpha + 1, halpha_pos, ?_⟩
      haveI : Nonempty (TwoValueAgent alpha (m - alpha + 1)) :=
        ⟨Sum.inr ⟨0, Nat.succ_pos (m - alpha)⟩⟩
      have hlow :
          1 < price alpha ((m - alpha + 1) - 1) := by
        simpa using hstart
      have hrev :=
        twoValueBidIndependentPriceRevenue_start_high_bound
          price H alpha (m - alpha + 1) hH_ge_one_real hlow
      have hmul :
          (H : ℝ) *
              twoValueBidIndependentPriceRevenue
                price H alpha (m - alpha + 1) ≤
            (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) :=
        mul_le_mul_of_nonneg_left hrev hH_nonneg
      have htotal_eq : alpha + (m - alpha + 1) = m + 1 := by
        calc
          alpha + (m - alpha + 1) = alpha + (m - alpha) + 1 := by
            rw [← Nat.add_assoc]
          _ = m + 1 := by
            rw [Nat.add_sub_of_le (le_of_lt halpha_lt_m)]
      have hbench_total :
          ((alpha : ℕ) : ℝ) + ((m - alpha + 1 : ℕ) : ℝ) ≤
            twoValueFixedPriceBenchmark H alpha (m - alpha + 1) :=
        finiteCandidateFixedPriceBenchmark_twoValue_one_price_ge_total
          (H := H) (highCount := alpha) (lowCount := m - alpha + 1)
          hH_ge_one_real
      have hbench :
          (m + 1 : ℝ) ≤
            twoValueFixedPriceBenchmark H alpha (m - alpha + 1) := by
        have hcast :
            ((alpha : ℕ) : ℝ) + ((m - alpha + 1 : ℕ) : ℝ) =
              (m + 1 : ℝ) := by
          exact_mod_cast htotal_eq
        calc
          (m + 1 : ℝ) =
              ((alpha : ℕ) : ℝ) + ((m - alpha + 1 : ℕ) : ℝ) := hcast.symm
          _ ≤ twoValueFixedPriceBenchmark H alpha (m - alpha + 1) :=
              hbench_total
      constructor
      · exact le_trans (le_trans hmul hm_large) hbench
      · have halpha_nonneg : 0 ≤ (alpha : ℝ) := by
          exact_mod_cast Nat.zero_le alpha
        have hside_to_square :
            (H : ℝ) * (alpha : ℝ) ≤
              (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) := by
          calc
            (H : ℝ) * (alpha : ℝ) =
                1 * ((H : ℝ) * (alpha : ℝ)) := by ring
            _ ≤ (H : ℝ) * ((H : ℝ) * (alpha : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hH_ge_one_real
                  (mul_nonneg hH_nonneg halpha_nonneg)
        exact le_trans (le_trans hside_to_square hm_large) hbench
    · have hstart_false : highOffer alpha = false := by
        dsimp [highOffer]
        simp [hstart]
      have hend_true : highOffer m = true := by
        dsimp [highOffer]
        simpa using hend_high
      obtain ⟨k, halpha_lt_k, hk_le_m, hkprev, hkcurr⟩ :=
        FiniteSum.exists_bool_transition highOffer halpha_lt_m
          hstart_false hend_true
      have hk_pos : 0 < k :=
        lt_of_lt_of_le halpha_pos (le_of_lt halpha_lt_k)
      refine ⟨k, m - k + 1, hk_pos, ?_⟩
      haveI : Nonempty (TwoValueAgent k (m - k + 1)) :=
        ⟨Sum.inl ⟨0, hk_pos⟩⟩
      have hbench :
          (H : ℝ) * (k : ℝ) ≤
            twoValueFixedPriceBenchmark H k (m - k + 1) :=
        finiteCandidateFixedPriceBenchmark_twoValue_high_price_ge
          (H := H) (highCount := k) (lowCount := m - k + 1)
          hH_ge_two hk_pos
      have hk_pos_for_sub : 0 < k :=
        lt_of_le_of_lt (Nat.zero_le alpha) halpha_lt_k
      have hlow_eq : m - (k - 1) = m - k + 1 :=
        FiniteSum.nat_sub_pred_eq_sub_add_one_of_pos_le
          hk_pos_for_sub hk_le_m
      have hprev_not : ¬ 1 < price (k - 1) (m - (k - 1)) := by
        dsimp [highOffer] at hkprev
        by_contra hgt
        simp [hgt] at hkprev
      have hprev_le : price (k - 1) (m - k + 1) ≤ 1 := by
        simpa [hlow_eq] using le_of_not_gt hprev_not
      have hcurr_gt_old : 1 < price k (m - k) := by
        dsimp [highOffer] at hkcurr
        by_contra hnot
        simp [hnot] at hkcurr
      have hcurr_gt :
          1 < price k ((m - k + 1) - 1) := by
        simpa using hcurr_gt_old
      have hrev :=
        twoValueBidIndependentPriceRevenue_transition_bound
          price H k (m - k + 1) hH_ge_one_real hprev_le hcurr_gt
      constructor
      · exact le_trans
          (le_trans (mul_le_mul_of_nonneg_left hrev hH_nonneg)
            (le_refl ((H : ℝ) * (k : ℝ)))) hbench
      · have halpha_le_k : alpha ≤ k := le_of_lt halpha_lt_k
        have halpha_cast : (alpha : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast halpha_le_k
        exact le_trans
          (mul_le_mul_of_nonneg_left halpha_cast hH_nonneg) hbench

/--
Compatibility form of the attained scaled-benchmark witness.  The stronger
theorem above additionally records that the high value `H` occurs in the
constructed binary input.
-/
theorem twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark
    (price : ℕ → ℕ → ℝ) {H alpha : ℕ}
    (hH_ge_two : 2 ≤ H) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (H : ℝ) *
          twoValueBidIndependentPriceRevenue price H highCount lowCount ≤
        twoValueFixedPriceBenchmark H highCount lowCount ∧
      (H : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark H highCount lowCount := by
  obtain ⟨highCount, lowCount, _hattained, hrev, hscale⟩ :=
    twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark_attained
      price hH_ge_two halpha_pos
  exact ⟨highCount, lowCount, hrev, hscale⟩

/--
the deterministic-threshold lower-bound theorem for a paper-style anonymous bid-independent price rule `f` on
erased bid lists. Its binary restriction is exactly the count-threshold rule
above, so the adversarial two-value input is obtained from the count-threshold
theorem.
-/
theorem twoValueListBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark
    (priceRule : List ℝ → ℝ) {H alpha : ℕ}
    (hH_ge_two : 2 ≤ H) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (H : ℝ) *
          twoValueBidIndependentPriceRevenue
            (twoValueListBidIndependentThresholdPrice priceRule H)
            H highCount lowCount ≤
        twoValueFixedPriceBenchmark H highCount lowCount ∧
      (H : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark H highCount lowCount := by
  exact twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark
    (twoValueListBidIndependentThresholdPrice priceRule H)
    hH_ge_two halpha_pos

/-- Attained form of the erased-list scaled-benchmark witness. -/
theorem twoValueListBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark_attained
    (priceRule : List ℝ → ℝ) {H alpha : ℕ}
    (hH_ge_two : 2 ≤ H) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (H : ℝ) *
          twoValueBidIndependentPriceRevenue
            (twoValueListBidIndependentThresholdPrice priceRule H)
            H highCount lowCount ≤
        twoValueFixedPriceBenchmark H highCount lowCount ∧
      (H : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark H highCount lowCount := by
  exact twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark_attained
    (twoValueListBidIndependentThresholdPrice priceRule H)
    hH_ge_two halpha_pos

/-! ### Deterministic single-parameter offer slices -/

/--
Utility from reporting `report` in a deterministic single-parameter offer
slice. `none` means rejection; `some p` means winning and paying `p`.
-/
def deterministicOfferUtility (offer : ℝ → Option ℝ)
    (value report : ℝ) : ℝ :=
  match offer report with
  | some price => value - price
  | none => 0

/-- Dominant-strategy truthfulness for a fixed-other-bids deterministic offer. -/
def DeterministicOfferTruthful (offer : ℝ → Option ℝ) : Prop :=
  ∀ value report,
    deterministicOfferUtility offer value report ≤
      deterministicOfferUtility offer value value

/-- A winning bidder is never charged above her own report. -/
def DeterministicOfferFeasible (offer : ℝ → Option ℝ) : Prop :=
  ∀ report price, offer report = some price → price ≤ report

/--
Bid-independence/critical-price shape for a deterministic offer slice: either
the bidder is always rejected, or there is a critical price `v` such that bids
below `v` lose and bids above `v` win at price `v`. The boundary bid `v` may
either win or lose, matching the open/closed interval alternatives in the source
the offer-slice characterization.
-/
def DeterministicOfferBidIndependent (offer : ℝ → Option ℝ) : Prop :=
  (∀ report, offer report = none) ∨
    ∃ criticalPrice,
      (∀ report price, offer report = some price → price = criticalPrice) ∧
      (∀ report, report < criticalPrice → offer report = none) ∧
      (∀ report, criticalPrice < report → offer report = some criticalPrice)

/--
A deterministic offer slice is dominated by a threshold if every winning report
pays exactly that threshold and the threshold is no larger than the winning
report.
-/
def DeterministicOfferThresholdDominates
    (offer : ℝ → Option ℝ) (threshold : ℝ) : Prop :=
  ∀ report price,
    offer report = some price → price = threshold ∧ threshold ≤ report

/--
the offer-slice characterization lemma payment-constancy step: in a truthful deterministic offer slice,
any two winning reports must be charged the same price.
-/
theorem deterministicOffer_payment_eq_of_truthful_wins
    {offer : ℝ → Option ℝ} (htruth : DeterministicOfferTruthful offer)
    {x y px py : ℝ}
    (hx : offer x = some px) (hy : offer y = some py) :
    px = py := by
  have hxy := htruth x y
  have hyx := htruth y x
  simp [deterministicOfferUtility, hx, hy] at hxy hyx
  linarith

/--
the offer-slice characterization lemma monotonicity step: if a lower report wins in a truthful
deterministic offer slice, then every higher report also wins.
-/
theorem deterministicOffer_winning_mono_of_truthful
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    (hfeasible : DeterministicOfferFeasible offer)
    {x y px : ℝ} (hxy : x < y)
    (hx : offer x = some px) :
    ∃ py, offer y = some py := by
  cases hy : offer y with
  | some py => exact ⟨py, rfl⟩
  | none =>
      have hreport := htruth y x
      have hpx_le_x : px ≤ x := hfeasible x px hx
      simp [deterministicOfferUtility, hx, hy] at hreport
      nlinarith

/--
the offer-slice characterization lemma losing-prefix step: if a higher report loses in a truthful
feasible deterministic offer slice, then every lower report also loses.
-/
theorem deterministicOffer_losing_anti_mono_of_truthful
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    (hfeasible : DeterministicOfferFeasible offer)
    {x y : ℝ} (hxy : x < y)
    (hy : offer y = none) :
    offer x = none := by
  cases hx : offer x with
  | none => rfl
  | some px =>
      obtain ⟨py, hpy⟩ :=
        deterministicOffer_winning_mono_of_truthful htruth hfeasible hxy hx
      rw [hy] at hpy
      contradiction

/--
Offer-slice characterization lemma. A truthful feasible deterministic
single-parameter offer is bid-independent: it is either always rejecting, or it
has a critical price with losing reports below it and winning reports above it.
-/
theorem deterministicOffer_bidIndependent_of_truthful
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    (hfeasible : DeterministicOfferFeasible offer) :
    DeterministicOfferBidIndependent offer := by
  classical
  by_cases hwin : ∃ report price, offer report = some price
  · rcases hwin with ⟨w, criticalPrice, hw⟩
    refine Or.inr ⟨criticalPrice, ?_, ?_, ?_⟩
    · intro report price hreport
      exact deterministicOffer_payment_eq_of_truthful_wins htruth hreport hw
    · intro report hlt
      cases hreport : offer report with
      | none => rfl
      | some price =>
          have hprice_eq :
              price = criticalPrice :=
            deterministicOffer_payment_eq_of_truthful_wins htruth hreport hw
          have hcrit_le_report : criticalPrice ≤ report := by
            rw [← hprice_eq]
            exact hfeasible report price hreport
          nlinarith
    · intro report hlt
      cases hreport : offer report with
      | some price =>
          have hprice_eq :
              price = criticalPrice :=
            deterministicOffer_payment_eq_of_truthful_wins htruth hreport hw
          simpa [hprice_eq] using hreport
      | none =>
          have hdsic := htruth report w
          simp [deterministicOfferUtility, hw, hreport] at hdsic
          nlinarith
  · exact Or.inl (by
      intro report
      cases hreport : offer report with
      | none => rfl
      | some price =>
          exact False.elim (hwin ⟨report, price, hreport⟩))

/--
Critical-price domination extracted from a bid-independent deterministic offer
slice. The always-rejecting case is dominated by the arbitrary threshold `0`;
otherwise the critical price dominates every winning report.
-/
theorem deterministicOffer_exists_thresholdDominates_of_bidIndependent
    {offer : ℝ → Option ℝ}
    (hbid : DeterministicOfferBidIndependent offer) :
    ∃ threshold, DeterministicOfferThresholdDominates offer threshold := by
  rcases hbid with hallReject | hcritical
  · refine ⟨0, ?_⟩
    intro report price hoff
    rw [hallReject report] at hoff
    contradiction
  · rcases hcritical with
      ⟨criticalPrice, hpayment, hlosesBelow, _hwinsAbove⟩
    refine ⟨criticalPrice, ?_⟩
    intro report price hoff
    constructor
    · exact hpayment report price hoff
    · by_contra hnot
      have hlt : report < criticalPrice := lt_of_not_ge hnot
      rw [hlosesBelow report hlt] at hoff
      contradiction

namespace DigitalGoodsAuction

/-- A deterministic digital-goods auction has binary allocation outcomes. -/
def BinaryAllocation (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ bids i, M.allocation bids i = 0 ∨ M.allocation bids i = 1

/-- A digital-goods auction charges rejected bidders zero. -/
def LosersPayZero (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ bids i, M.allocation bids i = 0 → M.payment bids i = 0

theorem losersPayZero_of_individuallyRational_noPositiveTransfers
    (M : DigitalGoodsAuction Agent)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers) :
    M.LosersPayZero := by
  intro bids i halloc
  have hir := hIR bids i
  have hnpt := hNPT bids i
  simp [DigitalGoodsAuction.utility, halloc] at hir
  exact le_antisymm (by linarith) hnpt

end DigitalGoodsAuction

/--
The single-bidder deterministic offer slice induced by a full digital-goods
auction after fixing the other bids.
-/
noncomputable def deterministicAuctionOffer [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) (bids : Agent → ℝ) (i : Agent) :
    ℝ → Option ℝ :=
  fun report =>
    let profile := Function.update bids i report
    if M.allocation profile i = 1 then
      some (M.payment profile i)
    else
      none

theorem deterministicAuctionOfferUtility_eq_auctionUtility
    [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hbinary : M.BinaryAllocation)
    (hloser : M.LosersPayZero)
    (bids : Agent → ℝ) (i : Agent) (value report : ℝ) :
    deterministicOfferUtility
        (deterministicAuctionOffer M bids i) value report =
      M.utility (Function.update bids i value) i
        (Function.update bids i report) := by
  classical
  unfold deterministicOfferUtility deterministicAuctionOffer
  unfold DigitalGoodsAuction.utility
  by_cases halloc : M.allocation (Function.update bids i report) i = 1
  · simp [halloc]
  · have halloc_zero :
        M.allocation (Function.update bids i report) i = 0 := by
      rcases hbinary (Function.update bids i report) i with hzero | hone
      · exact hzero
      · exact False.elim (halloc hone)
    have hpay_zero :
        M.payment (Function.update bids i report) i = 0 :=
      hloser (Function.update bids i report) i halloc_zero
    simp [halloc_zero, hpay_zero]

theorem deterministicAuctionOffer_truthful_of_auction_truthful
    [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : M.TruthfulDominantStrategy)
    (hbinary : M.BinaryAllocation)
    (hloser : M.LosersPayZero)
    (bids : Agent → ℝ) (i : Agent) :
    DeterministicOfferTruthful (deterministicAuctionOffer M bids i) := by
  intro value report
  let values := Function.update bids i value
  have hprofile :
      Function.update values i report = Function.update bids i report := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [values]
    · simp [values, Function.update, hji]
  have hdsic := htruth values i report
  rw [deterministicAuctionOfferUtility_eq_auctionUtility
      M hbinary hloser bids i value report]
  rw [deterministicAuctionOfferUtility_eq_auctionUtility
      M hbinary hloser bids i value value]
  simpa [values, hprofile] using hdsic

theorem deterministicAuctionOffer_feasible_of_individuallyRational
    [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hIR : M.IndividuallyRational)
    (bids : Agent → ℝ) (i : Agent) :
    DeterministicOfferFeasible (deterministicAuctionOffer M bids i) := by
  intro report price hoff
  unfold deterministicAuctionOffer at hoff
  by_cases halloc : M.allocation (Function.update bids i report) i = 1
  · simp [halloc] at hoff
    subst price
    have hir := hIR (Function.update bids i report) i
    simp [DigitalGoodsAuction.utility, halloc] at hir
    linarith
  · simp [halloc] at hoff

/--
Auction-level form of the offer-slice characterization lemma. Every fixed-other-bids slice of a
truthful, individually rational, no-positive-transfers deterministic
digital-goods auction is bid-independent in the critical-price sense.
-/
theorem deterministicAuctionOffer_bidIndependent_of_truthful
    [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : M.TruthfulDominantStrategy)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    DeterministicOfferBidIndependent (deterministicAuctionOffer M bids i) := by
  have hloser : M.LosersPayZero :=
    DigitalGoodsAuction.losersPayZero_of_individuallyRational_noPositiveTransfers
      M hIR hNPT
  exact deterministicOffer_bidIndependent_of_truthful
    (deterministicAuctionOffer_truthful_of_auction_truthful
      M htruth hbinary hloser bids i)
    (deterministicAuctionOffer_feasible_of_individuallyRational
      M hIR bids i)

/--
If a deterministic auction offer slice is dominated by a nonnegative threshold,
then the actual payment at any report is bounded by the corresponding posted
threshold revenue term.
-/
theorem deterministicAuction_payment_le_threshold_of_offer_thresholdDominates
    [DecidableEq Agent]
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
  classical
  by_cases halloc : M.allocation (Function.update bids i value) i = 1
  · have hoff :
        deterministicAuctionOffer M bids i value =
          some (M.payment (Function.update bids i value) i) := by
      unfold deterministicAuctionOffer
      simp [halloc]
    obtain ⟨hpay, hthreshold_le_value⟩ :=
      hdom value (M.payment (Function.update bids i value) i) hoff
    rw [hpay]
    simp [hthreshold_le_value]
  · have halloc_zero :
        M.allocation (Function.update bids i value) i = 0 := by
      rcases hbinary (Function.update bids i value) i with hzero | hone
      · exact hzero
      · exact False.elim (halloc hone)
    have hpay_zero :
        M.payment (Function.update bids i value) i = 0 :=
      hloser (Function.update bids i value) i halloc_zero
    rw [hpay_zero]
    by_cases hle : threshold ≤ value
    · simp [hle, hthreshold_nonneg]
    · simp [hle]

/--
Truthful, individually rational, no-positive-transfers deterministic auctions
produce nonnegative threshold-dominating offer slices after fixing other bids.
-/
theorem deterministicAuctionOffer_exists_nonnegative_thresholdDominates_of_truthful
    [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : M.TruthfulDominantStrategy)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    ∃ threshold,
      0 ≤ threshold ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer M bids i) threshold := by
  classical
  have hbid :
      DeterministicOfferBidIndependent (deterministicAuctionOffer M bids i) :=
    deterministicAuctionOffer_bidIndependent_of_truthful
      M htruth hIR hNPT hbinary bids i
  rcases hbid with hallReject | hcritical
  · refine ⟨0, le_rfl, ?_⟩
    intro report price hoff
    rw [hallReject report] at hoff
    contradiction
  · rcases hcritical with
      ⟨criticalPrice, hpayment, hlosesBelow, hwinsAbove⟩
    have hwin :
        deterministicAuctionOffer M bids i (criticalPrice + 1) =
          some criticalPrice := by
      exact hwinsAbove (criticalPrice + 1) (by linarith)
    have hcritical_nonneg : 0 ≤ criticalPrice := by
      unfold deterministicAuctionOffer at hwin
      by_cases halloc :
          M.allocation (Function.update bids i (criticalPrice + 1)) i = 1
      · simp [halloc] at hwin
        rw [← hwin]
        exact hNPT (Function.update bids i (criticalPrice + 1)) i
      · simp [halloc] at hwin
    refine ⟨criticalPrice, hcritical_nonneg, ?_⟩
    intro report price hoff
    constructor
    · exact hpayment report price hoff
    · by_contra hnot
      have hlt : report < criticalPrice := lt_of_not_ge hnot
      rw [hlosesBelow report hlt] at hoff
      contradiction

end Auction
end AppliedModelingLib
