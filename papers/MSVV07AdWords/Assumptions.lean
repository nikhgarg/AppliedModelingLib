import MSVV07AdWords.ProofInterface

/-!
# Paper Assumptions: MSVV07 AdWords

This file records source theorem conditions used by the compact MSVV paper
interface. They are finite-run, small-bids, and model-extension conditions from
Theorem 8 and Sections 6/8, not proof certificates.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing

/-- The AdWords model has nonnegative bids. -/
-- audit-premise: hbid : I.NonnegativeBids
abbrev assumption_nonnegative_bids
    {Advertiser Query : Type*} (I : Proof.PaperInstance Advertiser Query) : Prop :=
  I.NonnegativeBids

/-- The explicit finite-error theorem uses an epsilon in `[0,1]`. -/
-- audit-premise: hepsilon : 0 ≤ epsilon
-- audit-premise: hepsilon_le_one : epsilon ≤ 1
abbrev assumption_epsilon_range (epsilon : ℝ) : Prop :=
  0 ≤ epsilon ∧ epsilon ≤ 1

/-- Section 6 alive-bidder next-price rule is parameterized by an alive predicate. -/
-- audit-premise: alive : Advertiser → Query → Prop
abbrev assumption_alive_bidder_predicate
    {Advertiser Query : Type*} (_alive : Advertiser → Query → Prop) : Prop :=
  ∀ a q, _alive a q ∨ ¬ _alive a q

/-- Section 6 all-bidders next-price charges satisfy the effective small-bids condition. -/
-- audit-premise: hnext_small : ∀ a q, section6_next_highest_bid_all I a q ≤ epsilon * I.budget a
abbrev assumption_next_highest_all_small_bids
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : Proof.PaperInstance Advertiser Query) (epsilon : ℝ) : Prop :=
  ∀ a q, Proof.section6_next_highest_bid_all I a q ≤ epsilon * I.budget a

/-- Section 6 alive-bidders next-price charges satisfy the effective small-bids condition. -/
-- audit-premise: hnext_small : ∀ a q, section6_next_highest_bid_alive I alive a q ≤ epsilon * I.budget a
abbrev assumption_next_highest_alive_small_bids
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : Proof.PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (epsilon : ℝ) : Prop :=
  ∀ a q, Proof.section6_next_highest_bid_alive I alive a q ≤ epsilon * I.budget a

/-- Section 6 click-through rates are probabilities. -/
-- audit-premise: hctr_nonneg : ∀ a q, 0 ≤ ctr a q
-- audit-premise: hctr_le_one : ∀ a q, ctr a q ≤ 1
abbrev assumption_click_through_rates_probability_bounds
    {Advertiser Query : Type*} (ctr : Advertiser → Query → ℝ) : Prop :=
  (∀ a q, 0 ≤ ctr a q) ∧ (∀ a q, ctr a q ≤ 1)

/-- Section 6 delayed-entry extension is parameterized by an availability predicate. -/
-- audit-premise: available : Advertiser → Query → Prop
abbrev assumption_availability_predicate
    {Advertiser Query : Type*} (_available : Advertiser → Query → Prop) : Prop :=
  ∀ a q, _available a q ∨ ¬ _available a q

/-- Section 8 advertiser weights are nonnegative. -/
-- audit-premise: hweight_nonneg : ∀ a, 0 ≤ weight a
abbrev assumption_weighted_bids_nonnegative_weights
    {Advertiser : Type*} (weight : Advertiser → ℝ) : Prop :=
  ∀ a, 0 ≤ weight a

/-- Section 8 weighted effective bids satisfy the small-bids condition. -/
-- audit-premise: hweighted_small : ∀ a q, weight a * I.bid a q ≤ epsilon * I.budget a
abbrev assumption_weighted_effective_small_bids
    {Advertiser Query : Type*}
    (I : Proof.PaperInstance Advertiser Query) (weight : Advertiser → ℝ)
    (epsilon : ℝ) : Prop :=
  ∀ a q, weight a * I.bid a q ≤ epsilon * I.budget a

end MSVV07PaperFacing
end Online
end AppliedModelingLib
