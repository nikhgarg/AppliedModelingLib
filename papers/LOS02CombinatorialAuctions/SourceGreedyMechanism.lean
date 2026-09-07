import AppliedModelingLib.MechanismDesign.Auctions.Combinatorial

/-!
# Source-facing average-greedy mechanism

Section 10 uses one concrete order and one concrete payment calculation.  This
wrapper deliberately exposes those two source operations rather than treating
the reusable order-rule constructor as the paper mechanism itself.
-/

namespace LOS02CombinatorialAuctions

open AppliedModelingLib.Auction

namespace SourceGreedy

/-- Definition 10.1's payment for the concrete average-per-good order.  The
`nextDenied` argument is fixed to the first qualifying later bid of that same
complete greedy run, rather than left as an arbitrary function. -/
noncomputable def averagePayment {Bidder Item : Type*}
    [Fintype Bidder] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) : ℝ := by
  letI : DecidableEq Bidder := LinearOrder.toDecidableEq
  letI : DecidableEq Item := Classical.decEq Item
  exact singleMindedGreedyPaymentFromNextDenied bids
    (singleMindedGreedyAcceptedFromOrder bids
      (singleMindedAverageOrderOf bids))
    (singleMindedGreedyNextDeniedFromOrder bids
      (singleMindedAverageOrderOf bids)) j

/-- The Section 7/10 average-per-good greedy mechanism: process the complete
fixed-priority average order, and charge an accepted bidder from the first later
bid that the same run denies because of that bidder.  Equality decisions are
local implementation choices, not source-model premises. -/
noncomputable def averageGreedyMechanism {Bidder Item : Type*}
    [Fintype Bidder] [LinearOrder Bidder] :
    SingleMindedAcceptedMechanism Bidder Item := by
  letI : DecidableEq Bidder := LinearOrder.toDecidableEq
  letI : DecidableEq Item := Classical.decEq Item
  exact {
    accepted := fun bids =>
      singleMindedGreedyAcceptedFromOrder bids
        (singleMindedAverageOrderOf bids)
    payment := averagePayment }

end SourceGreedy
end LOS02CombinatorialAuctions
