import AppliedModelingLib.MechanismDesign.Auctions.DigitalGoods

/-!
# Theorem 7.2 benchmark bridge

The source hypothesis `F^(1) >= 2h`, together with the upper bound `v_i <= h`,
forces every benchmark-attaining one-winner candidate to sell to at least two
bidders.  Therefore the finite candidate versions of `F^(1)` and `F^(2)`
coincide.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib
open AppliedModelingLib.Auction

noncomputable section

/-- Requiring two winners can only decrease the finite candidate-price benchmark. -/
theorem finiteCandidateFixedPriceBenchmark_two_le_one
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) :
    finiteCandidateFixedPriceBenchmark values 2 ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let i : Agent := finiteCandidateBenchmarkBidder values 2
  have hF2_selected :
      finiteCandidateFixedPriceBenchmark values 2 =
        candidateFixedPriceRevenue values 2 i := by
    simpa [i] using
      finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue values 2
  by_cases hi : 0 ≤ values i ∧ 2 ≤ saleCount values (values i)
  · have hi_one : 0 ≤ values i ∧ 1 ≤ saleCount values (values i) := by
      constructor
      · exact hi.1
      · omega
    have hF2_eq_revenue :
        finiteCandidateFixedPriceBenchmark values 2 =
          singlePriceRevenue values (values i) := by
      rw [hF2_selected]
      simp [candidateFixedPriceRevenue, hi]
    have hF1_eq_revenue :
        candidateFixedPriceRevenue values 1 i =
          singlePriceRevenue values (values i) := by
      simp [candidateFixedPriceRevenue, hi_one]
    calc
      finiteCandidateFixedPriceBenchmark values 2 =
          singlePriceRevenue values (values i) := hF2_eq_revenue
      _ = candidateFixedPriceRevenue values 1 i := hF1_eq_revenue.symm
      _ ≤ finiteCandidateFixedPriceBenchmark values 1 :=
        candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark values 1 i
  · have hF2_zero : finiteCandidateFixedPriceBenchmark values 2 = 0 := by
      rw [hF2_selected]
      simp [candidateFixedPriceRevenue, hi]
    rw [hF2_zero]
    exact finiteCandidateFixedPriceBenchmark_nonneg values 1

/-- Under the high-benchmark premise used by GHW Theorem 7.2, the finite
one-winner and two-winner candidate fixed-price benchmarks agree. -/
theorem finiteCandidateFixedPriceBenchmark_one_eq_twoWinner
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (h : ℝ)
    (hh_ge_one : 1 ≤ h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hbenchmark_large : 2 * h ≤ finiteCandidateFixedPriceBenchmark values 1) :
    finiteCandidateFixedPriceBenchmark values 1 =
      twoWinnerFixedPriceBenchmarkValue values := by
  classical
  let i1 : Agent := finiteCandidateBenchmarkBidder values 1
  have hF1_selected :
      finiteCandidateFixedPriceBenchmark values 1 =
        candidateFixedPriceRevenue values 1 i1 := by
    simpa [i1] using
      finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue values 1
  have hh_pos : 0 < h := lt_of_lt_of_le zero_lt_one hh_ge_one
  have hF1_pos : 0 < finiteCandidateFixedPriceBenchmark values 1 := by
    nlinarith
  have hi1_feasible :
      0 ≤ values i1 ∧ 1 ≤ saleCount values (values i1) := by
    by_contra hnot
    have hzero : candidateFixedPriceRevenue values 1 i1 = 0 := by
      simp [candidateFixedPriceRevenue, hnot]
    rw [hF1_selected, hzero] at hF1_pos
    exact (lt_irrefl 0 hF1_pos)
  have hi1_two_winners : 2 ≤ saleCount values (values i1) := by
    by_contra hnot_two
    have hcount_le_one : saleCount values (values i1) ≤ 1 := by
      omega
    have hrev_le_h : singlePriceRevenue values (values i1) ≤ h := by
      calc
        singlePriceRevenue values (values i1) ≤
            (saleCount values (values i1) : ℝ) * h :=
          singlePriceRevenue_le_saleCount_mul_bound values hi1_feasible.1 hvalue_le_h
        _ ≤ h := by
          have hcount_cast : (saleCount values (values i1) : ℝ) ≤ 1 := by
            exact_mod_cast hcount_le_one
          nlinarith
    have hF1_eq_revenue :
        finiteCandidateFixedPriceBenchmark values 1 =
          singlePriceRevenue values (values i1) := by
      rw [hF1_selected]
      simp [candidateFixedPriceRevenue, hi1_feasible]
    have hF1_le_h : finiteCandidateFixedPriceBenchmark values 1 ≤ h := by
      rw [hF1_eq_revenue]
      exact hrev_le_h
    nlinarith
  have hF1_le_F2 :
      finiteCandidateFixedPriceBenchmark values 1 ≤
        finiteCandidateFixedPriceBenchmark values 2 := by
    have hrev_le_F2 : singlePriceRevenue values (values i1) ≤
        finiteCandidateFixedPriceBenchmark values 2 :=
      singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
        values 2 i1 hi1_feasible.1 hi1_two_winners
    have hF1_eq_revenue :
        finiteCandidateFixedPriceBenchmark values 1 =
          singlePriceRevenue values (values i1) := by
      rw [hF1_selected]
      simp [candidateFixedPriceRevenue, hi1_feasible]
    simpa [hF1_eq_revenue] using hrev_le_F2
  have hF2_pos : 0 < finiteCandidateFixedPriceBenchmark values 2 :=
    lt_of_lt_of_le hF1_pos hF1_le_F2
  let i2 : Agent := finiteCandidateBenchmarkBidder values 2
  have hF2_selected :
      finiteCandidateFixedPriceBenchmark values 2 =
        candidateFixedPriceRevenue values 2 i2 := by
    simpa [i2] using
      finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue values 2
  have hi2_feasible :
      0 ≤ values i2 ∧ 2 ≤ saleCount values (values i2) := by
    by_contra hnot
    have hzero : candidateFixedPriceRevenue values 2 i2 = 0 := by
      simp [candidateFixedPriceRevenue, hnot]
    rw [hF2_selected, hzero] at hF2_pos
    exact (lt_irrefl 0 hF2_pos)
  have hF2_le_F1 :
      finiteCandidateFixedPriceBenchmark values 2 ≤
        finiteCandidateFixedPriceBenchmark values 1 := by
    have hrev_le_F1 : singlePriceRevenue values (values i2) ≤
        finiteCandidateFixedPriceBenchmark values 1 :=
      singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
        values 1 i2 hi2_feasible.1 (by omega)
    have hF2_eq_revenue :
        finiteCandidateFixedPriceBenchmark values 2 =
          singlePriceRevenue values (values i2) := by
      rw [hF2_selected]
      simp [candidateFixedPriceRevenue, hi2_feasible]
    simpa [hF2_eq_revenue] using hrev_le_F1
  exact le_antisymm hF1_le_F2 hF2_le_F1

end

end GHW01DigitalGoods
