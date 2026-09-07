import AppliedModelingLib.MechanismDesign.Auctions.DigitalGoods

/-!
# Source Model for the Weighted-Pairing Auction

This module states the operational sampling rule used for the weighted-pairing
auction.  It separates the source model's domain conditions from the closed
revenue expression already provided by the reusable auction library.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib.Auction
open scoped BigOperators

noncomputable section

/-- A bid profile on which the source weighted-pairing sampling rule is a
probability distribution for every bidder. -/
structure WeightedPairingSourceProfile
    {Agent : Type*} [Fintype Agent] (bids : Agent → ℝ) : Prop where
  bid_nonneg : ∀ i : Agent, 0 ≤ bids i
  positive_other_bid_mass :
    ∀ i : Agent, 0 < totalBidValue bids - bids i

/-- A nonnegative bid profile with a positive other-bid denominator for every
bidder is a valid source weighted-pairing profile. -/
theorem weightedPairingSourceProfile_of_nonnegative_and_denominator_pos
    {Agent : Type*} [Fintype Agent] (bids : Agent → ℝ)
    (hbid_nonneg : ∀ i : Agent, 0 ≤ bids i)
    (hother_mass : ∀ i : Agent, 0 < totalBidValue bids - bids i) :
    WeightedPairingSourceProfile bids :=
  ⟨hbid_nonneg, hother_mass⟩

/-- In the source weighted-pairing rule, bidder `i` samples no bid of its own,
and samples each other bidder's bid proportionally to that bid. -/
noncomputable def weightedPairingOfferProbability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (i j : Agent) : ℝ :=
  if j = i then 0 else bids j / (totalBidValue bids - bids i)

/-- The source offer probability is zero on bidder `i`'s own bid. -/
theorem weightedPairingOfferProbability_self
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) :
    weightedPairingOfferProbability bids i i = 0 := by
  simp [weightedPairingOfferProbability]

/-- On a source-admissible profile, every offered-bid probability is
nonnegative. -/
theorem weightedPairingOfferProbability_nonneg
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i j : Agent) :
    0 ≤ weightedPairingOfferProbability bids i j := by
  by_cases hji : j = i
  · simp [weightedPairingOfferProbability, hji]
  · simp only [weightedPairingOfferProbability, if_neg hji]
    exact div_nonneg (source.bid_nonneg j)
      (le_of_lt (source.positive_other_bid_mass i))

/-- The non-self bids sum to the total bid mass excluding bidder `i`. -/
private theorem weightedPairing_nonself_bid_sum
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) :
    (∑ j : Agent, if j = i then 0 else bids j) =
      totalBidValue bids - bids i := by
  classical
  have herase :
      (∑ j ∈ (Finset.univ : Finset Agent).erase i, bids j) + bids i =
        ∑ j : Agent, bids j := by
    simpa using
      (Finset.sum_erase_add (s := (Finset.univ : Finset Agent)) bids
        (Finset.mem_univ i))
  rw [totalBidValue]
  calc
    ∑ j : Agent, (if j = i then 0 else bids j) =
        ∑ j ∈ (Finset.univ : Finset Agent).filter (fun j => j ≠ i), bids j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hji]
    _ = ∑ j ∈ (Finset.univ : Finset Agent).erase i, bids j := by
      rw [Finset.filter_ne']
    _ = (∑ j : Agent, bids j) - bids i := by
      linarith

/-- Strictly positive bids and a distinct bidder for every bidder make the
source weighted-pairing probability rule well-defined. -/
theorem weightedPairingSourceProfile_of_positive_and_distinct
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ)
    (hbid_pos : ∀ i : Agent, 0 < bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i) :
    WeightedPairingSourceProfile bids := by
  refine ⟨fun i => le_of_lt (hbid_pos i), ?_⟩
  intro i
  obtain ⟨j, hji⟩ := hdistinct i
  have hterms_nonneg :
      ∀ x ∈ (Finset.univ : Finset Agent),
        0 ≤ if x = i then 0 else bids x := by
    intro x _
    by_cases hxi : x = i
    · simp [hxi]
    · exact le_of_lt (by simpa [hxi] using hbid_pos x)
  have hterm_le :
      (if j = i then 0 else bids j) ≤
        ∑ x : Agent, if x = i then 0 else bids x := by
    exact Finset.single_le_sum hterms_nonneg (Finset.mem_univ j)
  have hnonself_pos :
      0 < ∑ x : Agent, if x = i then 0 else bids x := by
    rw [if_neg hji] at hterm_le
    exact lt_of_lt_of_le (hbid_pos j) hterm_le
  simpa only [weightedPairing_nonself_bid_sum bids i] using hnonself_pos

/-- The source's normalized lower-bid convention, together with the fact
that each bidder has another bid available to sample, constructs the internal
probability-domain certificate.  The latter condition is forced by the
source instruction to sample a bid from `B_i`; it is kept explicit rather
than treating the singleton case as a totalized probability formula. -/
theorem weightedPairingSourceProfile_of_unit_lower_bound_and_distinct
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ)
    (hbid_ge_one : ∀ i : Agent, 1 ≤ bids i)
    (hdistinct : ∀ i : Agent, ∃ j : Agent, j ≠ i) :
    WeightedPairingSourceProfile bids := by
  apply weightedPairingSourceProfile_of_positive_and_distinct bids
  · intro i
    exact lt_of_lt_of_le zero_lt_one (hbid_ge_one i)
  · exact hdistinct

/-- On a source-admissible profile, the offered-bid probabilities for each
bidder have total mass one. -/
theorem weightedPairingOfferProbability_sum_eq_one
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) :
    ∑ j : Agent, weightedPairingOfferProbability bids i j = 1 := by
  let denominator := totalBidValue bids - bids i
  have hdenominator_ne : denominator ≠ 0 :=
    ne_of_gt (source.positive_other_bid_mass i)
  have hsum :
      (∑ j : Agent, if j = i then 0 else bids j) = denominator := by
    simpa [denominator] using weightedPairing_nonself_bid_sum bids i
  calc
    ∑ j : Agent, weightedPairingOfferProbability bids i j =
        ∑ j : Agent, (if j = i then 0 else bids j) / denominator := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;>
        simp [weightedPairingOfferProbability, denominator, hji]
    _ = (∑ j : Agent, if j = i then 0 else bids j) / denominator := by
      simpa only [div_eq_mul_inv] using
        (Finset.sum_mul (s := (Finset.univ : Finset Agent))
          (f := fun j : Agent => if j = i then 0 else bids j)
          (a := denominator⁻¹)).symm
    _ = denominator / denominator := by rw [hsum]
    _ = 1 := div_self hdenominator_ne

/-- The source operational expected payment for bidder `i`: draw an offered
bid according to the source rule, sell to `i` when that bid is no larger than
`i`'s bid, and charge the offered bid. -/
noncomputable def weightedPairingSourceExpectedPayment
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) : ℝ :=
  ∑ j : Agent,
    weightedPairingOfferProbability bids i j *
      if bids j ≤ bids i then bids j else 0

/-- The source operational expected revenue is the sum of the bidders'
expected payments. -/
noncomputable def weightedPairingSourceOperationalExpectedRevenue
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) : ℝ :=
  ∑ i : Agent, weightedPairingSourceExpectedPayment bids source i

/-- The source operational payment rule reduces to the library's closed
weighted-pairing expected-payment expression. -/
theorem weightedPairingSourceExpectedPayment_eq_weightedPairingExpectedPayment
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) :
    weightedPairingSourceExpectedPayment bids source i =
      weightedPairingExpectedPayment bids i := by
  unfold weightedPairingSourceExpectedPayment weightedPairingExpectedPayment
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [weightedPairingOfferProbability]
  · by_cases hle : bids j ≤ bids i
    · have hpair : j ≠ i ∧ bids j ≤ bids i := ⟨hji, hle⟩
      simp only [weightedPairingOfferProbability, if_neg hji,
        if_pos hle, if_pos hpair]
      rw [div_eq_mul_inv, pow_two]
      ring
    · simp [weightedPairingOfferProbability, hji, hle]

/-- On every source-admissible profile, the source operational expected
revenue is exactly the existing weighted-pairing revenue expression. -/
theorem weightedPairingRevenue_source_definition
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) :
    weightedPairingSourceOperationalExpectedRevenue bids source =
      weightedPairingExpectedRevenue bids := by
  unfold weightedPairingSourceOperationalExpectedRevenue weightedPairingExpectedRevenue
  apply Finset.sum_congr rfl
  intro i _
  exact weightedPairingSourceExpectedPayment_eq_weightedPairingExpectedPayment
    bids source i

end

end GHW01DigitalGoods
