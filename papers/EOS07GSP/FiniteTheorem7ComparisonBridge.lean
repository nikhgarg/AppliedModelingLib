import EOS07GSP.FiniteLemma5MoreBiddersBridge
import EOS07GSP.FiniteStaticBridge

/-!
# Direct finite seller-comparison bridge for EOS Theorem 7

The source's seller-minimal-revenue argument runs backward from the price
discipline imposed by the first unassigned bidder.  This file formalizes that
argument on the finite `K>N` sorted-GSP domain.  In particular, it does not
replace the terminal price by an artificial zero tail and it does not take a
revenue-comparison certificate as a premise.
-/

namespace EOS07GSP
namespace PaperInterface

open AppliedModelingLib.Auction

noncomputable section

/-- In a full finite `K>N` ranked market, stability plus the first losing
bidder's bottom-slot inequality lower-bounds every assigned click-weighted
payment by the source VCG total payment.  The proof is the appendix's direct
backward induction: the terminal VCG price is the bottom CTR times the first
unassigned bidder's value, and every preceding rank follows from the stable
no-rematching inequality. -/
theorem eos_finite_static_vcg_total_payment_le_of_stable_ranked_more_bidders
    {m n : ℕ} (hnm : n < m) (model : EOSFiniteStaticBStarOrder n)
    (O : PositionOutcome (Fin m) (Fin n))
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment model.clickThroughRate)
        (fun i : Fin m => model.value i.val))
    (hslots : ∀ i : Fin n,
      O.slotOf ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i)
    (hbottom :
      model.clickThroughRate (n - 1) *
        (model.value n - O.paymentPerClick
          ⟨n - 1, Nat.lt_of_sub_pos (by omega)⟩) ≤ 0)
    (i : Fin n) :
    model.vcgTotalPayment i.val ≤
      model.clickThroughRate i.val * O.paymentPerClick
        ⟨i.val, Nat.lt_trans i.isLt hnm⟩ := by
  have hn : 0 < n := model.slots_nonempty
  let total : ℕ → ℝ := fun k =>
    if hk : k < n then
      model.clickThroughRate k * O.paymentPerClick
        ⟨k, Nat.lt_trans hk hnm⟩
    else 0
  have hadj : ∀ k : ℕ, k + 1 < n →
      (model.clickThroughRate k - model.clickThroughRate (k + 1)) *
          model.value (k + 1) + total (k + 1) ≤ total k := by
    intro k hk
    let upper : Fin n := ⟨k, by omega⟩
    let lower : Fin n := ⟨k + 1, hk⟩
    let upperBidder : Fin m := ⟨k, Nat.lt_trans upper.isLt hnm⟩
    let lowerBidder : Fin m := ⟨k + 1, Nat.lt_trans lower.isLt hnm⟩
    have hno := hstable.2.2 lowerBidder upperBidder upper (hslots upper)
    have hlower_slot : O.slotOf lowerBidder = some lower := by
      simpa [lowerBidder] using hslots lower
    have hlower_utility :
        O.utility (paper_theorem7_ranked_environment model.clickThroughRate)
          (fun r : Fin m => model.value r.val) lowerBidder =
          model.clickThroughRate (k + 1) *
            (model.value (k + 1) - O.paymentPerClick lowerBidder) := by
      rw [PositionOutcome.utility, hlower_slot]
      rfl
    rw [hlower_utility] at hno
    have hno' :
        model.clickThroughRate k *
            (model.value (k + 1) - O.paymentPerClick upperBidder) ≤
          model.clickThroughRate (k + 1) *
            (model.value (k + 1) - O.paymentPerClick lowerBidder) := by
      simpa [paper_theorem7_ranked_environment, upper, lower,
        upperBidder, lowerBidder] using hno
    have hk0 : k < n := by omega
    simp only [total, dif_pos hk, dif_pos hk0]
    nlinarith [hno']
  have hterminal : model.vcgTotalPayment (n - 1) ≤ total (n - 1) := by
    have hlast : n - 1 + 1 = n := by omega
    have hvcg := model.terminal_payment (n - 1) hlast
    have hlast_lt : n - 1 < n := by omega
    simp only [total, dif_pos hlast_lt]
    rw [hvcg]
    nlinarith [hbottom]
  have hall : ∀ k : ℕ, k ≤ n - 1 → model.vcgTotalPayment k ≤ total k := by
    intro k hk
    refine Nat.decreasingInduction (n := n - 1) ?_ hterminal hk
    intro r hr hnext
    have hrec := model.vcg_rec r (by omega)
    have hstep := hadj r (by omega)
    rw [hrec]
    linarith
  simpa only [total, dif_pos i.isLt] using hall i.val (by omega)

/-- The actual total seller revenue of a strict finite sorted-GSP profile is
the sum of its assigned ranked click-weighted payments: all bidders at ranks
`n` and below are unassigned and make zero revenue contribution. -/
theorem paper_ranked_gsp_more_bidders_revenue_eq_assigned_sum
    {m n : ℕ} (hnm : n < m) {clickThroughRate : ℕ → ℝ}
    (bids : Fin m → ℝ)
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i) :
    (paper_ranked_gsp_mechanism m n bids).revenue
        (paper_theorem7_ranked_environment clickThroughRate) =
      ∑ i : Fin n, clickThroughRate i.val *
        (paper_ranked_gsp_mechanism m n bids).paymentPerClick
          ⟨i.val, Nat.lt_trans i.isLt hnm⟩ := by
  classical
  let M := paper_ranked_gsp_mechanism m n
  let E : PositionEnvironment (Fin n) :=
    paper_theorem7_ranked_environment clickThroughRate
  have hrealize :=
    paper_ranked_gsp_mechanism_realizes_next_price_of_strict_decreasing_more_bidders
      (bids := bids) hnm hstrict
  let contribution : ℕ → ℝ := fun k =>
    if hkm : k < m then PositionOutcome.revenueContribution E (M bids) ⟨k, hkm⟩
    else 0
  have htail : ∑ k ∈ Finset.Ico n m, contribution k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hslot : (M bids).slotOf ⟨k, hk.2⟩ = none := by
      simpa [M] using hrealize.2.1 ⟨k, hk.2⟩ hk.1
    simp [contribution, dif_pos hk.2,
      PositionOutcome.revenueContribution, hslot]
  calc
    (M bids).revenue E = ∑ k ∈ Finset.range m, contribution k := by
      rw [PositionOutcome.revenue, Finset.sum_fin_eq_sum_range]
    _ = ∑ k ∈ Finset.range n, contribution k := by
      have hsplit := Finset.sum_range_add_sum_Ico contribution (Nat.le_of_lt hnm)
      rw [htail, add_zero] at hsplit
      exact hsplit.symm
    _ = ∑ i : Fin n, clickThroughRate i.val *
        (M bids).paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hkm : k < m := Nat.lt_trans hkn hnm
      have hslot : (M bids).slotOf ⟨k, hkm⟩ = some ⟨k, hkn⟩ := by
        simpa [M] using hrealize.1 ⟨k, hkn⟩
      simp only [contribution, dif_pos hkm,
        PositionOutcome.revenueContribution, hslot,
        dif_pos hkn]
      rfl

/-- The constructed finite `B*` outcome earns exactly the sum of its VCG
total payments.  This uses the concrete on-path slot/payment ledger and the
unassigned first loser; it is not a separate revenue assumption. -/
theorem eos_finite_static_bstar_tiebreak_revenue_eq_vcg_sum
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
      (eosFiniteStaticBStarBids model)).revenue
        (paper_theorem7_ranked_environment model.clickThroughRate) =
      ∑ i : Fin n, model.vcgTotalPayment i.val := by
  let M := paper_ranked_gsp_tiebreak_mechanism (n + 1) n
  let E : PositionEnvironment (Fin n) :=
    paper_theorem7_ranked_environment model.clickThroughRate
  rcases eos_finite_static_bstar_tiebreak_source_conclusion model with
    ⟨_hlef, hslots, hunassigned, hpayments⟩
  have hslots' : ∀ i : Fin n,
      (M (eosFiniteStaticBStarBids model)).slotOf i.castSucc = some i := by
    simpa [M] using hslots
  have hunassigned' :
      (M (eosFiniteStaticBStarBids model)).slotOf (Fin.last n) = none := by
    simpa [M] using hunassigned
  calc
    (M (eosFiniteStaticBStarBids model)).revenue E =
        ∑ i : Fin n, model.clickThroughRate i.val *
          (M (eosFiniteStaticBStarBids model)).paymentPerClick i.castSucc := by
      rw [PositionOutcome.revenue, Fin.sum_univ_castSucc]
      have hsum :
          (∑ i : Fin n,
            PositionOutcome.revenueContribution E
              (M (eosFiniteStaticBStarBids model)) i.castSucc) =
            ∑ i : Fin n, model.clickThroughRate i.val *
              (M (eosFiniteStaticBStarBids model)).paymentPerClick i.castSucc := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [PositionOutcome.revenueContribution, hslots']
        rfl
      rw [hsum]
      simp only [PositionOutcome.revenueContribution, hunassigned']
      exact add_zero _
    _ = ∑ i : Fin n, model.vcgTotalPayment i.val := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [M] using hpayments i

/-- Direct corrected finite seller-minimal-revenue conclusion for EOS Theorem
7.  Against every strict ordinary sorted-GSP profile satisfying corrected
Definition 4, the finite `B*` outcome's seller revenue is weakly lower.  The
proof uses the corrected full-`K>N` Lemma 5 bridge, the source's first-loser
terminal inequality, and a backward stable-payment induction; no comparison
or revenue certificate is assumed. -/
theorem eos_finite_static_bstar_revenue_le_of_corrected_ranked_gsp
    {m n : ℕ} (hnm : n < m) (model : EOSFiniteStaticBStarOrder n)
    (bids : Fin m → ℝ)
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hcorrected :
      correctedDefinition4LocallyEnvyFree
        (paper_theorem7_ranked_environment model.clickThroughRate)
        (paper_ranked_gsp_mechanism m n)
        (fun i : Fin m => model.value i.val) bids n
        (fun rank => if h : rank < n then
          (⟨rank, Nat.lt_trans h hnm⟩ : Fin m)
          else ⟨0, Nat.lt_trans model.slots_nonempty hnm⟩)
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n)
          else ⟨0, model.slots_nonempty⟩)) :
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
      (eosFiniteStaticBStarBids model)).revenue
        (paper_theorem7_ranked_environment model.clickThroughRate) ≤
      (paper_ranked_gsp_mechanism m n bids).revenue
        (paper_theorem7_ranked_environment model.clickThroughRate) := by
  let M := paper_ranked_gsp_mechanism m n
  let E : PositionEnvironment (Fin n) :=
    paper_theorem7_ranked_environment model.clickThroughRate
  have hstable : (M bids).StableAssignment E
      (fun i : Fin m => model.value i.val) := by
    simpa [M, E] using
      corrected_lemma5_ranked_more_bidders_stable_bridge
        model.slots_nonempty hnm bids hstrict
        (fun i => model.click_pos i.val i.isLt)
        model.click_strict hcorrected
  have hrealize :=
    paper_ranked_gsp_mechanism_realizes_next_price_of_strict_decreasing_more_bidders
      (bids := bids) hnm hstrict
  have hslots : ∀ i : Fin n,
      (M bids).slotOf ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i := by
    simpa [M] using hrealize.1
  have hn : 0 < n := model.slots_nonempty
  have hlast : n - 1 + 1 = n := by omega
  have hlast_lt : n - 1 < n := by omega
  have hloser_slot : (M bids).slotOf ⟨n, hnm⟩ = none := by
    simpa [M] using hrealize.2.1 ⟨n, hnm⟩ (Nat.le_refl n)
  have hbottom_raw := hcorrected.2 ⟨n, hnm⟩ hloser_slot (n - 1) hlast
  have hbottom :
      model.clickThroughRate (n - 1) *
        (model.value n - (M bids).paymentPerClick
          ⟨n - 1, by omega⟩) ≤ 0 := by
    simpa [M, E, paper_theorem7_ranked_environment,
      dif_pos hn] using hbottom_raw
  have hpointwise : ∀ i : Fin n, model.vcgTotalPayment i.val ≤
      model.clickThroughRate i.val *
        (M bids).paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ := by
    intro i
    exact eos_finite_static_vcg_total_payment_le_of_stable_ranked_more_bidders
      hnm model (M bids) hstable hslots hbottom i
  calc
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model)).revenue
          (paper_theorem7_ranked_environment model.clickThroughRate) =
        ∑ i : Fin n, model.vcgTotalPayment i.val :=
      eos_finite_static_bstar_tiebreak_revenue_eq_vcg_sum model
    _ ≤ ∑ i : Fin n, model.clickThroughRate i.val *
        (M bids).paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ := by
      exact Finset.sum_le_sum fun i _ => hpointwise i
    _ = (M bids).revenue E := by
      symm
      exact paper_ranked_gsp_more_bidders_revenue_eq_assigned_sum
        hnm bids hstrict

end
end PaperInterface
end EOS07GSP
