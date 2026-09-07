import EOS07GSP.Implementation

/-!
# Finite strict-surplus bridge for EOS Lemma 6

The Appendix construction for Lemma 6 is strict only when each assigned bidder
has positive surplus.  This module proves that strict-bid step on the explicit
one-extra-bidder ranked domain.  It is an amended-source bridge: the source's
archival weak stable-assignment predicate remains available separately.
-/

namespace EOS07GSP
namespace PaperInterface

open AppliedModelingLib.Auction

noncomputable section

/-- The Appendix Lemma 6 bid construction in zero-based finite rank notation:
the top bidder bids her value and each later bidder bids the preceding slot's
per-click price. -/
def lemma6ConstructedBids {n : ℕ}
    (value payment clickThroughRate : ℕ → ℝ) : Fin (n + 1) → ℝ :=
  fun bidder => Fin.cases (value 0)
    (fun rank => payment rank.val / clickThroughRate rank.val) bidder

/-- Equality of GSP outcomes at the source's level of observability: every
bidder has the same assigned slot (or is unassigned), and payments agree for
bidders who are assigned.  A GSP mechanism may retain an arbitrary next-bid
record for an unassigned bidder, but that bidder receives no clicks and the
source's outcome notation does not assign her a payment. -/
def lemma6AssignedOutcomeEq {Bidder Slot : Type*}
    (left right : PositionOutcome Bidder Slot) : Prop :=
  (∀ bidder, left.slotOf bidder = right.slotOf bidder) ∧
    ∀ bidder slot, left.slotOf bidder = some slot →
      left.paymentPerClick bidder = right.paymentPerClick bidder

/-- Assigned-outcome equality preserves realized utility, because an
unassigned bidder's utility is definitionally zero and an assigned bidder's
payment is included in the comparison. -/
theorem lemma6AssignedOutcomeEq_utility
    {Bidder Slot : Type*} (E : PositionEnvironment Slot)
    (values : Bidder → ℝ) (left right : PositionOutcome Bidder Slot)
    (heq : lemma6AssignedOutcomeEq left right) (bidder : Bidder) :
    left.utility E values bidder = right.utility E values bidder := by
  cases hslot : left.slotOf bidder with
  | none =>
      have hright : right.slotOf bidder = none := by
        simpa [hslot] using (heq.1 bidder).symm
      simp [PositionOutcome.utility, hslot, hright]
  | some slot =>
      have hright : right.slotOf bidder = some slot := by
        simpa [hslot] using (heq.1 bidder).symm
      have hpayment : left.paymentPerClick bidder = right.paymentPerClick bidder :=
        heq.2 bidder slot hslot
      simp [PositionOutcome.utility, hslot, hright, hpayment]

/-- The stable-assignment predicate only observes slots, assigned payments,
and resulting utilities, so it transfers across source-level outcome equality.
-/
theorem lemma6AssignedOutcomeEq_stableAssignment_left
    {Bidder Slot : Type*} (E : PositionEnvironment Slot)
    (values : Bidder → ℝ) (left right : PositionOutcome Bidder Slot)
    (heq : lemma6AssignedOutcomeEq left right)
    (hright : right.StableAssignment E values) :
    left.StableAssignment E values := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j slot his hjs
    have his_right : right.slotOf i = some slot := by
      simpa [his] using (heq.1 i).symm
    have hjs_right : right.slotOf j = some slot := by
      simpa [hjs] using (heq.1 j).symm
    exact hright.1 his_right hjs_right
  · intro i
    rw [lemma6AssignedOutcomeEq_utility E values left right heq i]
    exact hright.2.1 i
  · intro i j slot hjs
    have hjs_right : right.slotOf j = some slot := by
      simpa [hjs] using (heq.1 j).symm
    have hpayment : left.paymentPerClick j = right.paymentPerClick j :=
      heq.2 j slot hjs
    rw [hpayment, lemma6AssignedOutcomeEq_utility E values left right heq i]
    exact hright.2.2 i j slot hjs_right

/-- For `K>N`, retain the source bid construction through the first
unassigned bidder (which sets every winner's next price), then use a strictly
decreasing tail of reports.  Tail reports do not affect allocated bidders'
slots or payments. -/
def lemma6ConstructedBidsMoreBidders {m n : ℕ}
    (value payment clickThroughRate : ℕ → ℝ) : Fin m → ℝ :=
  fun bidder =>
    if bidder.val = 0 then
      value 0
    else if bidder.val ≤ n then
      payment (bidder.val - 1) / clickThroughRate (bidder.val - 1)
    else
      payment (n - 1) / clickThroughRate (n - 1) - (bidder.val - n)

/-- The generalized construction agrees with the Appendix construction on
the winner ranks and the first unassigned rank. -/
theorem lemma6ConstructedBidsMoreBidders_eq_source
    {m n : ℕ} {value payment clickThroughRate : ℕ → ℝ}
    (k : ℕ) (hk : k < n + 1) (hkm : k < m) :
    lemma6ConstructedBidsMoreBidders (m := m) (n := n)
        value payment clickThroughRate
        ⟨k, hkm⟩ =
      lemma6ConstructedBids value payment clickThroughRate ⟨k, hk⟩ := by
  by_cases hzero : k = 0
  · subst k
    simp [lemma6ConstructedBidsMoreBidders, lemma6ConstructedBids]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hsource : k + 1 ≤ n := Nat.le_of_lt_succ hk
    simp [lemma6ConstructedBidsMoreBidders, lemma6ConstructedBids, hsource]

/-- Strict positive outcome utility gives positive per-click surplus at an
assigned ranked slot when its CTR is positive. -/
theorem corrected_lemma6_ranked_net_surplus_positive
    {n : ℕ} {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin (n + 1)) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val) O)
    (hslots : ∀ i : Fin n, O.slotOf i.castSucc = some i)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick i.castSucc = payment i.val / clickThroughRate i.val)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (i : Fin n) :
    0 < value i.val - payment i.val / clickThroughRate i.val := by
  have hutility :
      0 < O.utility (paper_theorem7_ranked_environment clickThroughRate)
        (fun j : Fin (n + 1) => value j.val) i.castSucc :=
    hcorrected.2 i.castSucc i (hslots i)
  have hproduct :
      0 < clickThroughRate i.val *
        (value i.val - payment i.val / clickThroughRate i.val) := by
    simpa [PositionOutcome.utility, paper_theorem7_ranked_environment,
      hslots i, hpayment i] using hutility
  exact (mul_pos_iff_of_pos_left (hclick_pos i)).mp hproduct

/-- The strict-surplus implication used in the `K>N` route.  Only the
assigned ranks enter this calculation; the additional unassigned bidders do
not alter an assigned bidder's realized utility. -/
theorem corrected_lemma6_ranked_net_surplus_positive_more_bidders
    {m n : ℕ} (hnm : n < m) {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) O)
    (hslots : ∀ i : Fin n,
      O.slotOf ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ =
        payment i.val / clickThroughRate i.val)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (i : Fin n) :
    0 < value i.val - payment i.val / clickThroughRate i.val := by
  let bidder : Fin m := ⟨i.val, Nat.lt_trans i.isLt hnm⟩
  have hutility :
      0 < O.utility (paper_theorem7_ranked_environment clickThroughRate)
        (fun j : Fin m => value j.val) bidder :=
    hcorrected.2 bidder i (by simpa [bidder] using hslots i)
  have hproduct :
      0 < clickThroughRate i.val *
        (value i.val - payment i.val / clickThroughRate i.val) := by
    simpa [bidder, PositionOutcome.utility, paper_theorem7_ranked_environment,
      hslots i, hpayment i] using hutility
  exact (mul_pos_iff_of_pos_left (hclick_pos i)).mp hproduct

/-- On the ranks through the first unassigned bidder, the generalized
construction has the strict adjacent inequalities proved by the Appendix's
stable-assignment algebra. -/
theorem corrected_lemma6_constructed_bids_more_bidders_source_adjacent_strict
    {m n : ℕ} (hnm : n < m) {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) O)
    (hslots : ∀ i : Fin n,
      O.slotOf ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ =
        payment i.val / clickThroughRate i.val)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    ∀ (k : ℕ) (hk : k + 1 < n + 1),
      lemma6ConstructedBidsMoreBidders (m := m) (n := n)
          value payment clickThroughRate ⟨k + 1, by omega⟩ <
        lemma6ConstructedBidsMoreBidders (m := m) (n := n)
          value payment clickThroughRate ⟨k, by omega⟩ := by
  intro k hk
  cases k with
  | zero =>
      have hn : 0 < n := by omega
      let top : Fin n := ⟨0, hn⟩
      have hpositive :
          0 < value 0 - payment 0 / clickThroughRate 0 := by
        simpa [top] using
          corrected_lemma6_ranked_net_surplus_positive_more_bidders hnm O
            hcorrected hslots hpayment hclick_pos top
      have hfirst : 1 ≤ n := by omega
      simpa [lemma6ConstructedBidsMoreBidders, hfirst] using
        paper_lemma6_top_constructed_bid_gt_next_of_positive_net_utility
          hpositive
  | succ k =>
      have hk_next : k + 1 < n := by omega
      let lower : Fin n := ⟨k + 1, hk_next⟩
      let upper : Fin n :=
        ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk_next⟩
      have hpositive :
          0 < value (k + 1) -
            payment (k + 1) / clickThroughRate (k + 1) := by
        simpa [lower] using
          corrected_lemma6_ranked_net_surplus_positive_more_bidders hnm O
            hcorrected hslots hpayment hclick_pos lower
      have hno_rematch :
          clickThroughRate k *
              (value (k + 1) - payment k / clickThroughRate k) ≤
            clickThroughRate (k + 1) *
              (value (k + 1) -
                payment (k + 1) / clickThroughRate (k + 1)) := by
        have hpayment_lower :
            O.paymentPerClick (⟨k + 1, by omega⟩ : Fin m) =
              payment (k + 1) / clickThroughRate (k + 1) := by
          simpa [lower] using hpayment lower
        have hpayment_upper :
            O.paymentPerClick (⟨k, by omega⟩ : Fin m) =
              payment k / clickThroughRate k := by
          simpa [upper] using hpayment upper
        have hraw := hcorrected.1.2.2
          (⟨k + 1, by omega⟩ : Fin m) (⟨k, by omega⟩ : Fin m) upper
          (hslots upper)
        simp only [PositionOutcome.utility] at hraw
        rw [hslots lower] at hraw
        simp only [paper_theorem7_ranked_environment] at hraw
        rw [hpayment_lower, hpayment_upper] at hraw
        simpa [lower, upper] using hraw
      have hstrict :=
        paper_lemma6_adjacent_constructed_bid_gt_next_of_no_profitable_rematch
          k (hclick_pos lower) (hclick_strict k hk_next) hpositive hno_rematch
      have hlower : k + 2 ≤ n := by omega
      have hupper : k + 1 ≤ n := by omega
      simpa [lemma6ConstructedBidsMoreBidders, hlower, hupper] using hstrict

/-- The source-algebra strictness through the first losing bid extends to a
strictly decreasing finite profile by choosing successively lower tail
reports. -/
theorem corrected_lemma6_constructed_bids_more_bidders_adjacent_strict
    {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) O)
    (hslots : ∀ i : Fin n,
      O.slotOf ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ =
        payment i.val / clickThroughRate i.val)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    ∀ (k : ℕ) (hk : k + 1 < m),
      lemma6ConstructedBidsMoreBidders (m := m) (n := n)
          value payment clickThroughRate ⟨k + 1, hk⟩ <
        lemma6ConstructedBidsMoreBidders (m := m) (n := n)
          value payment clickThroughRate ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  intro k hk
  by_cases hsource : k + 1 < n + 1
  · exact
      corrected_lemma6_constructed_bids_more_bidders_source_adjacent_strict
        hnm O hcorrected hslots hpayment hclick_pos hclick_strict k hsource
  · have hn_le_k : n ≤ k := by omega
    by_cases hk_eq_n : k = n
    · subst k
      have hn_pos : n ≠ 0 := by omega
      have hnext_not_source : ¬ n + 1 ≤ n := by omega
      have hnext_ne_zero : n + 1 ≠ 0 := by omega
      simp [lemma6ConstructedBidsMoreBidders, hn_pos, hnext_not_source]
    · have hn_lt_k : n < k := lt_of_le_of_ne hn_le_k (Ne.symm hk_eq_n)
      have hk_ne_zero : k ≠ 0 := by omega
      have hk_not_source : ¬ k ≤ n := by omega
      have hnext_ne_zero : k + 1 ≠ 0 := by omega
      have hnext_not_source : ¬ k + 1 ≤ n := by omega
      simp only [lemma6ConstructedBidsMoreBidders, if_neg hk_ne_zero,
        if_neg hk_not_source, if_neg hnext_ne_zero, if_neg hnext_not_source]
      apply sub_lt_sub_left
      norm_num

/-- Direct amended Lemma 6 bridge on the paper's full `K>N` domain.  The
constructed profile agrees with the stable assignment on every allocation and
every payment attached to an allocated bidder; unassigned-bidder tail records
are intentionally outside the source-level outcome comparison. -/
theorem corrected_lemma6_ranked_more_bidders_constructs_tiebreak_equilibrium_bridge
    {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) O)
    (hslots : ∀ i : Fin n,
      O.slotOf ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i)
    (hunassigned : ∀ bidder : Fin m, n ≤ bidder.val → O.slotOf bidder = none)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ =
        payment i.val / clickThroughRate i.val)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    let bids := lemma6ConstructedBidsMoreBidders (m := m) (n := n)
      value payment clickThroughRate
    lemma6AssignedOutcomeEq
        (paper_ranked_gsp_tiebreak_mechanism m n bids) O ∧
      (paper_ranked_gsp_tiebreak_mechanism m n).LocallyEnvyFreeEquilibrium
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) bids := by
  dsimp
  let bids := lemma6ConstructedBidsMoreBidders (m := m) (n := n)
    value payment clickThroughRate
  have hadj : ∀ (k : ℕ) (hk : k + 1 < m),
      bids ⟨k + 1, hk⟩ < bids ⟨k, Nat.lt_of_succ_lt hk⟩ := by
    intro k hk
    exact
      corrected_lemma6_constructed_bids_more_bidders_adjacent_strict
        hn hnm O hcorrected hslots hpayment hclick_pos hclick_strict k hk
  have hstrict : ∀ {i j : Fin m}, i.val < j.val → bids j < bids i := by
    intro i j hij
    exact paper_ranked_gsp_strict_decreasing_of_adjacent hadj hij
  let M := paper_ranked_gsp_tiebreak_mechanism m n
  have hout : lemma6AssignedOutcomeEq (M bids) O := by
    constructor
    · intro bidder
      have hrank : paper_ranked_gsp_tiebreak_rank bids bidder = bidder.val := by
        simpa using
          paper_ranked_gsp_tiebreak_rank_eq_index_of_strict_decreasing
            hstrict bidder
      by_cases hallocated : bidder.val < n
      · let slot : Fin n := ⟨bidder.val, hallocated⟩
        have hMslot : (M bids).slotOf bidder = some slot := by
          have hrank_lt : paper_ranked_gsp_tiebreak_rank bids bidder < n := by
            simpa [hrank] using hallocated
          rw [show (M bids).slotOf bidder =
              if h : paper_ranked_gsp_tiebreak_rank bids bidder < n then
                some ⟨paper_ranked_gsp_tiebreak_rank bids bidder, h⟩ else none by
              rfl]
          rw [dif_pos hrank_lt]
          congr
        have hOslot : O.slotOf bidder = some slot := by
          simpa [slot] using hslots slot
        exact hMslot.trans hOslot.symm
      · have hMnone : (M bids).slotOf bidder = none := by
          simp [M, paper_ranked_gsp_tiebreak_mechanism, hrank, hallocated]
        exact hMnone.trans (hunassigned bidder (Nat.le_of_not_gt hallocated)).symm
    · intro bidder slot hMassigned
      have hrank : paper_ranked_gsp_tiebreak_rank bids bidder = bidder.val := by
        simpa using
          paper_ranked_gsp_tiebreak_rank_eq_index_of_strict_decreasing
            hstrict bidder
      have hallocated : bidder.val < n := by
        by_contra hnot
        have hMnone : (M bids).slotOf bidder = none := by
          simp [M, paper_ranked_gsp_tiebreak_mechanism, hrank, hnot]
        rw [hMnone] at hMassigned
        contradiction
      let rank : Fin n := ⟨bidder.val, hallocated⟩
      have hnext_lt : rank.val + 1 < m := by omega
      have hnext_bid :
          paper_ranked_gsp_tiebreak_bid_at_rank bids (rank.val + 1) =
            bids ⟨rank.val + 1, hnext_lt⟩ := by
        exact
          paper_ranked_gsp_tiebreak_bid_at_rank_eq_index_of_strict_decreasing
            hstrict hnext_lt
      have hnext_source : rank.val + 1 ≤ n := by omega
      have hbid_formula :
          bids ⟨rank.val + 1, hnext_lt⟩ =
            payment rank.val / clickThroughRate rank.val := by
        simp [bids, lemma6ConstructedBidsMoreBidders, hnext_source]
      have hOpayment :
          O.paymentPerClick bidder =
            payment rank.val / clickThroughRate rank.val := by
        simpa [rank] using hpayment rank
      calc
        (M bids).paymentPerClick bidder =
            paper_ranked_gsp_tiebreak_bid_at_rank bids (rank.val + 1) := by
              simp [M, paper_ranked_gsp_tiebreak_mechanism, hrank, rank]
        _ = bids ⟨rank.val + 1, hnext_lt⟩ := hnext_bid
        _ = payment rank.val / clickThroughRate rank.val := hbid_formula
        _ = O.paymentPerClick bidder := hOpayment.symm
  refine ⟨hout, ?_⟩
  have hstable_M :
      (M bids).StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) :=
    lemma6AssignedOutcomeEq_stableAssignment_left
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin m => value i.val) (M bids) O hout hcorrected.1
  exact
    paper_ranked_gsp_tiebreak_stable_assignment_locally_envy_free_equilibrium_more_bidders
      hnm (M bids) bids (by rfl) hstrict
      (fun s => (hclick_pos s).le) hstable_M

/-- Under the owner-approved strict-surplus domain, the Appendix Lemma 6 bid
construction is strictly decreasing in the source's finite one-extra-bidder
rank order. -/
theorem corrected_lemma6_constructed_bids_adjacent_strict
    {n : ℕ} {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin (n + 1)) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val) O)
    (hslots : ∀ i : Fin n, O.slotOf i.castSucc = some i)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick i.castSucc = payment i.val / clickThroughRate i.val)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    ∀ (k : ℕ) (hk : k + 1 < n + 1),
      lemma6ConstructedBids value payment clickThroughRate ⟨k + 1, hk⟩ <
        lemma6ConstructedBids value payment clickThroughRate
          ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  intro k hk
  cases k with
  | zero =>
      have hn : 0 < n := by omega
      let top : Fin n := ⟨0, hn⟩
      have hpositive :
          0 < value 0 - payment 0 / clickThroughRate 0 := by
        simpa [top] using
          corrected_lemma6_ranked_net_surplus_positive O hcorrected hslots
            hpayment hclick_pos top
      simpa [lemma6ConstructedBids] using
        paper_lemma6_top_constructed_bid_gt_next_of_positive_net_utility
          hpositive
  | succ k =>
      have hk_next : k + 1 < n := by omega
      let lower : Fin n := ⟨k + 1, hk_next⟩
      let upper : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk_next⟩
      have hpositive :
          0 < value (k + 1) -
            payment (k + 1) / clickThroughRate (k + 1) := by
        simpa [lower] using
          corrected_lemma6_ranked_net_surplus_positive O hcorrected hslots
            hpayment hclick_pos lower
      have hno_rematch :
          clickThroughRate k *
              (value (k + 1) - payment k / clickThroughRate k) ≤
            clickThroughRate (k + 1) *
              (value (k + 1) -
                payment (k + 1) / clickThroughRate (k + 1)) := by
        have hraw := hcorrected.1.2.2 lower.castSucc upper.castSucc upper
          (hslots upper)
        simp only [PositionOutcome.utility] at hraw
        rw [hslots lower] at hraw
        simp only [hpayment lower, hpayment upper,
          paper_theorem7_ranked_environment] at hraw
        simpa [lower, upper] using hraw
      have hstrict :=
        paper_lemma6_adjacent_constructed_bid_gt_next_of_no_profitable_rematch
          k (hclick_pos lower) (hclick_strict k hk_next) hpositive hno_rematch
      simpa [lemma6ConstructedBids] using hstrict

/-- The finite one-extra-bidder version of the owner-approved amended Lemma 6:
the Appendix bid construction strictly orders bids, realizes the given ranked
stable assignment (with the standard zero payment for the unassigned bidder),
and is a locally envy-free equilibrium of tie-broken GSP. -/
theorem corrected_lemma6_ranked_one_extra_constructs_tiebreak_equilibrium_bridge
    {n : ℕ} {value payment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin (n + 1)) (Fin n))
    (hcorrected :
      correctedLemma6StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val) O)
    (hslots : ∀ i : Fin n, O.slotOf i.castSucc = some i)
    (hunassigned : O.slotOf (Fin.last n) = none)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick i.castSucc = payment i.val / clickThroughRate i.val)
    (hunassigned_payment : O.paymentPerClick (Fin.last n) = 0)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    let bids := lemma6ConstructedBids (n := n) value payment clickThroughRate
    paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids = O ∧
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n).LocallyEnvyFreeEquilibrium
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val) bids := by
  dsimp
  let bids := lemma6ConstructedBids (n := n) value payment clickThroughRate
  have hadj : ∀ (k : ℕ) (hk : k + 1 < n + 1),
      bids ⟨k + 1, hk⟩ < bids ⟨k, Nat.lt_of_succ_lt hk⟩ := by
    intro k hk
    exact corrected_lemma6_constructed_bids_adjacent_strict O hcorrected hslots
      hpayment hclick_pos hclick_strict k hk
  have hstrict : ∀ {i j : Fin (n + 1)}, i.val < j.val → bids j < bids i := by
    intro i j hij
    exact paper_ranked_gsp_strict_decreasing_of_adjacent hadj hij
  have hrealize :=
    paper_ranked_gsp_tiebreak_mechanism_realizes_next_price_of_strict_decreasing
      hstrict
  have hout : paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids = O := by
    apply PositionOutcome.ext
    · intro bidder
      refine Fin.lastCases ?_ (fun i => ?_) bidder
      · exact hrealize.2.1.trans hunassigned.symm
      · exact (hrealize.1 i).trans (hslots i).symm
    · intro bidder
      refine Fin.lastCases ?_ (fun i => ?_) bidder
      · have hrank : paper_ranked_gsp_tiebreak_rank bids (Fin.last n) = n := by
          simpa using
            paper_ranked_gsp_tiebreak_rank_eq_index_of_strict_decreasing
              hstrict (Fin.last n)
        calc
          (paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids).paymentPerClick
              (Fin.last n) = 0 := by
                simp [paper_ranked_gsp_tiebreak_mechanism, hrank,
                  paper_ranked_gsp_tiebreak_bid_at_rank_eq_zero_of_rank_ge_card]
          _ = O.paymentPerClick (Fin.last n) := hunassigned_payment.symm
      · calc
          (paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids).paymentPerClick
              i.castSucc = bids i.succ := hrealize.2.2 i
          _ = payment i.val / clickThroughRate i.val := by
            simp [bids, lemma6ConstructedBids]
          _ = O.paymentPerClick i.castSucc := (hpayment i).symm
  refine ⟨hout, ?_⟩
  exact
    paper_ranked_gsp_tiebreak_stable_assignment_locally_envy_free_equilibrium_more_bidders
      (by omega) O bids hout hstrict (fun s => (hclick_pos s).le) hcorrected.1

end
end PaperInterface
end EOS07GSP
