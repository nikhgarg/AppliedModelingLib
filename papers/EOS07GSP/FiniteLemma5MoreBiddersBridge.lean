import EOS07GSP.Implementation

/-!
# Finite `K>N` bridge for EOS Lemma 5

This module extends the concrete sorted-GSP ledger used by the corrected
one-extra-bidder Lemma 5 bridge.  It retains the source mechanism rather than
replacing it with a tie-broken off-path implementation: strict on-path bids
give every assigned rank its ordinary next-price outcome.
-/

namespace EOS07GSP
namespace PaperInterface

open AppliedModelingLib.Auction

noncomputable section

/-- Under a strictly decreasing finite profile with more bidders than slots,
ordinary sorted GSP assigns the first `n` ranks to their indexed slots, leaves
every later rank unassigned, and charges each assigned rank its next bid. -/
theorem paper_ranked_gsp_mechanism_realizes_next_price_of_strict_decreasing_more_bidders
    {m n : ℕ} (hnm : n < m) {bids : Fin m → ℝ}
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i) :
    (∀ i : Fin n,
        (paper_ranked_gsp_mechanism m n bids).slotOf
            ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = some i) ∧
      (∀ bidder : Fin m, n ≤ bidder.val →
        (paper_ranked_gsp_mechanism m n bids).slotOf bidder = none) ∧
      ∀ i : Fin n,
        (paper_ranked_gsp_mechanism m n bids).paymentPerClick
            ⟨i.val, Nat.lt_trans i.isLt hnm⟩ =
          bids ⟨i.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hnm⟩ := by
  constructor
  · intro i
    let winner : Fin m := ⟨i.val, Nat.lt_trans i.isLt hnm⟩
    have hrank : paper_ranked_gsp_rank bids winner = i.val := by
      simpa [winner] using
        paper_ranked_gsp_rank_eq_index_of_strict_decreasing hstrict winner
    simp [paper_ranked_gsp_mechanism, winner, hrank]
  constructor
  · intro bidder hbidder
    have hrank : paper_ranked_gsp_rank bids bidder = bidder.val :=
      paper_ranked_gsp_rank_eq_index_of_strict_decreasing hstrict bidder
    simp [paper_ranked_gsp_mechanism, hrank, hbidder]
  · intro i
    let winner : Fin m := ⟨i.val, Nat.lt_trans i.isLt hnm⟩
    let next : Fin m :=
      ⟨i.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hnm⟩
    have hrank_winner : paper_ranked_gsp_rank bids winner = i.val := by
      simpa [winner] using
        paper_ranked_gsp_rank_eq_index_of_strict_decreasing hstrict winner
    have hrank_next : paper_ranked_gsp_rank bids next = i.val + 1 := by
      simpa [next] using
        paper_ranked_gsp_rank_eq_index_of_strict_decreasing hstrict next
    have hselected : paper_ranked_gsp_bid_at_rank bids (i.val + 1) = bids next := by
      exact paper_ranked_gsp_bid_at_rank_eq_of_unique hrank_next (by
        intro j hj
        have hjrank := paper_ranked_gsp_rank_eq_index_of_strict_decreasing hstrict j
        apply Fin.ext
        simpa [hjrank] using hj)
    change paper_ranked_gsp_bid_at_rank bids
        (paper_ranked_gsp_rank bids winner + 1) = bids next
    rw [hrank_winner]
    exact hselected

/-- In a strict finite profile with more bidders than slots, any bidder can
report below the current last bid.  Ordinary sorted GSP then gives that bidder
no slot, so Nash equilibrium implies individual rationality without a sign
condition on values or bids. -/
theorem paper_ranked_gsp_more_bidders_individually_rational_of_nash
    {m n : ℕ} (hnm : n < m) {value clickThroughRate : ℕ → ℝ}
    (bids : Fin m → ℝ)
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hnash :
      (paper_ranked_gsp_mechanism m n).IsNashEquilibrium
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) bids) :
    (paper_ranked_gsp_mechanism m n bids).IndividuallyRational
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin m => value i.val) := by
  classical
  intro i
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
  let last : Fin m := ⟨m - 1, Nat.pred_lt (Nat.ne_of_gt hmpos)⟩
  let report : ℝ := bids last - 1
  have hlast_le : ∀ j : Fin m, bids last ≤ bids j := by
    intro j
    by_cases hj : j = last
    · subst j
      exact le_rfl
    · have hj_lt : j.val < last.val := by
        by_contra hnot
        have hge : last.val ≤ j.val := Nat.le_of_not_gt hnot
        have hlast_val : last.val = m - 1 := rfl
        have hj_last : j = last := by
          apply Fin.ext
          omega
        exact hj hj_last
      exact le_of_lt (hstrict hj_lt)
  have hbelow : ∀ j : Fin m, j ≠ i → report < bids j := by
    intro j _
    dsimp [report]
    linarith [hlast_le j]
  let updated : Fin m → ℝ := Function.update bids i report
  have hrank : paper_ranked_gsp_rank updated i = m - 1 := by
    unfold paper_ranked_gsp_rank
    have hfilter :
        ((Finset.univ : Finset (Fin m)).filter fun j =>
          updated i < updated j) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase]
      constructor
      · intro hj
        constructor
        · intro hji
          subst j
          exact (lt_irrefl (updated i)) hj
        · trivial
      · intro hj
        rw [show updated i = report by simp [updated],
          show updated j = bids j by simp [updated, hj.1]]
        exact hbelow j hj.1
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hslot :
      (paper_ranked_gsp_mechanism m n updated).slotOf i = none := by
    have hnot : ¬ m - 1 < n := by omega
    simp [paper_ranked_gsp_mechanism, hrank, hnot]
  have hzero :
      PositionMechanism.utility
          (paper_theorem7_ranked_environment clickThroughRate)
          (paper_ranked_gsp_mechanism m n)
          (fun i : Fin m => value i.val) updated i = 0 := by
    simp [PositionMechanism.utility, PositionOutcome.utility, hslot]
  rw [← hzero]
  simpa [updated] using hnash i report

/-- A neighboring downward undercut has the same rank in a `K>N` sorted-GSP
market as in the one-extra market: only the bidder immediately below the
deviator joins the ranks above her, while every lower tail bid remains below
the report. -/
theorem paper_ranked_gsp_rank_after_adjacent_down_update_more_bidders
    {m n : ℕ} (hnm : n < m) {bids : Fin m → ℝ}
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (k : ℕ) (hk : k + 1 < n) (report : ℝ)
    (hnext_lt_report : bids ⟨k + 2, by omega⟩ < report)
    (hreport_lt_lower : report < bids ⟨k + 1, by omega⟩) :
    paper_ranked_gsp_rank
        (Function.update bids ⟨k, by omega⟩ report)
        ⟨k, by omega⟩ = k + 1 := by
  classical
  let upper : Fin m := ⟨k, by omega⟩
  let lower : Fin m := ⟨k + 1, by omega⟩
  let next : Fin m := ⟨k + 2, by omega⟩
  let updated : Fin m → ℝ := Function.update bids upper report
  have hfilter :
      ((Finset.univ : Finset (Fin m)).filter fun j =>
          updated upper < updated j) =
        insert lower (Finset.Iio upper) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_Iio]
    constructor
    · intro hj
      by_cases hju : j = upper
      · subst j
        simpa [updated] using hj
      · have hupdated_upper : updated upper = report := by
          simp [updated]
        have hupdated_j : updated j = bids j := by
          simp [updated, hju]
        have hj_bid : report < bids j := by
          simpa [hupdated_upper, hupdated_j] using hj
        by_cases hj_lt_upper : j.val < k
        · exact Or.inr (by simpa [upper] using hj_lt_upper)
        · have hk_le_j : k ≤ j.val := le_of_not_gt hj_lt_upper
          rcases Nat.eq_or_lt_of_le hk_le_j with hj_eq_k | hk_lt_j
          · have hj_eq_upper : j = upper := by
              apply Fin.ext
              simpa [upper] using hj_eq_k.symm
            exact False.elim (hju hj_eq_upper)
          · have hk1_le_j : k + 1 ≤ j.val := Nat.succ_le_of_lt hk_lt_j
            rcases Nat.eq_or_lt_of_le hk1_le_j with hj_eq_lower | hk1_lt_j
            · exact Or.inl (by
                apply Fin.ext
                simpa [lower] using hj_eq_lower.symm)
            · have hnext_le_j : next.val ≤ j.val := by
                simpa [next] using Nat.succ_le_of_lt hk1_lt_j
              have hj_le_next_bid : bids j ≤ bids next := by
                rcases Nat.eq_or_lt_of_le hnext_le_j with hj_eq_next | hnext_lt_j
                · have hj_eq_next_fin : j = next := by
                    apply Fin.ext
                    exact hj_eq_next.symm
                  subst j
                  exact le_rfl
                · exact le_of_lt (hstrict hnext_lt_j)
              have hj_lt_report : bids j < report :=
                lt_of_le_of_lt hj_le_next_bid (by simpa [next] using hnext_lt_report)
              exact False.elim ((not_lt_of_ge (le_of_lt hj_lt_report)) hj_bid)
    · intro hmem
      rcases hmem with h_lower | h_before
      · subst j
        have hupper_ne_lower : lower ≠ upper := by
          intro h
          have hval := congrArg Fin.val h
          simp [upper, lower] at hval
        simpa [updated, hupper_ne_lower, upper, lower]
          using hreport_lt_lower
      · have hju : j ≠ upper := by
          intro h
          have hval := congrArg Fin.val h
          have hjlt : j.val < upper.val := h_before
          rw [hval] at hjlt
          exact (lt_irrefl upper.val) hjlt
        have hupdated_upper : updated upper = report := by
          simp [updated]
        have hupdated_j : updated j = bids j := by
          simp [updated, hju]
        have hj_lower : j.val < lower.val := by
          have hj_upper : j.val < upper.val := h_before
          simpa [upper, lower] using
            Nat.lt_trans hj_upper (Nat.lt_succ_self k)
        have hlower_lt_j_bid : bids lower < bids j := hstrict hj_lower
        have hreport_lt_j : report < bids j :=
          lt_trans (by simpa [lower] using hreport_lt_lower) hlower_lt_j_bid
        simpa [hupdated_upper, hupdated_j] using hreport_lt_j
  unfold paper_ranked_gsp_rank
  rw [hfilter]
  have hlower_not_mem : lower ∉ Finset.Iio upper := by
    simp [upper, lower]
  rw [Finset.card_insert_of_notMem hlower_not_mem, Fin.card_Iio]

/-- The bidder immediately below a neighboring downward undercut keeps her
rank.  This identifies the next-price selector at the deviator's new slot. -/
theorem paper_ranked_gsp_next_rank_after_adjacent_down_update_more_bidders
    {m n : ℕ} (hnm : n < m) {bids : Fin m → ℝ}
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (k : ℕ) (hk : k + 1 < n) (report : ℝ)
    (hnext_lt_report : bids ⟨k + 2, by omega⟩ < report) :
    paper_ranked_gsp_rank
        (Function.update bids ⟨k, by omega⟩ report)
        ⟨k + 2, by omega⟩ = k + 2 := by
  classical
  let upper : Fin m := ⟨k, by omega⟩
  let next : Fin m := ⟨k + 2, by omega⟩
  let updated : Fin m → ℝ := Function.update bids upper report
  have hnext_ne_upper : next ≠ upper := by
    intro h
    have hval := congrArg Fin.val h
    simp [next, upper] at hval
  have hfilter :
      ((Finset.univ : Finset (Fin m)).filter fun j =>
          updated next < updated j) = Finset.Iio next := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · intro hj
      by_cases hju : j = upper
      · subst j
        simp [upper, next]
      · have hupdated_next : updated next = bids next := by
          simp [updated, hnext_ne_upper]
        have hupdated_j : updated j = bids j := by
          simp [updated, hju]
        have hj_bid : bids next < bids j := by
          simpa [hupdated_next, hupdated_j] using hj
        by_contra hnot
        have hnext_le_j : next.val ≤ j.val := le_of_not_gt hnot
        rcases Nat.eq_or_lt_of_le hnext_le_j with hnext_eq_j | hnext_lt_j
        · have hj_eq_next : j = next := by
            apply Fin.ext
            exact hnext_eq_j.symm
          subst j
          exact (lt_irrefl (bids next)) hj_bid
        · have hj_lt_next_bid : bids j < bids next := hstrict hnext_lt_j
          exact (not_lt_of_ge (le_of_lt hj_lt_next_bid)) hj_bid
    · intro hj_before
      by_cases hju : j = upper
      · subst j
        simpa [updated, hnext_ne_upper, upper, next] using hnext_lt_report
      · have hupdated_next : updated next = bids next := by
          simp [updated, hnext_ne_upper]
        have hupdated_j : updated j = bids j := by
          simp [updated, hju]
        have hbid : bids next < bids j := hstrict hj_before
        simpa [hupdated_next, hupdated_j] using hbid
  unfold paper_ranked_gsp_rank
  rw [hfilter, Fin.card_Iio]

/-- The adjacent-under-cut profile has no tied reports.  This is needed only
to make the ordinary (rather than tie-broken) next-bid selector unambiguous. -/
theorem paper_ranked_gsp_no_ties_after_adjacent_down_update_more_bidders
    {m n : ℕ} (hnm : n < m) {bids : Fin m → ℝ}
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (k : ℕ) (hk : k + 1 < n) (report : ℝ)
    (hnext_lt_report : bids ⟨k + 2, by omega⟩ < report)
    (hreport_lt_lower : report < bids ⟨k + 1, by omega⟩) :
    ∀ {i j : Fin m}, i ≠ j →
      Function.update bids ⟨k, by omega⟩ report i ≠
        Function.update bids ⟨k, by omega⟩ report j := by
  classical
  let upper : Fin m := ⟨k, by omega⟩
  let lower : Fin m := ⟨k + 1, by omega⟩
  let next : Fin m := ⟨k + 2, by omega⟩
  have hreport_ne_bid :
      ∀ j : Fin m, j ≠ upper → report ≠ bids j := by
    intro j hju
    by_cases hj_before_next : j.val < next.val
    · have hj_le_lower : j.val ≤ lower.val := by
        have hraw : j.val ≤ k + 1 := by
          exact Nat.lt_add_one_iff.mp (by simpa [next, Nat.add_assoc] using hj_before_next)
        simpa [lower] using hraw
      rcases Nat.eq_or_lt_of_le hj_le_lower with hj_eq_lower | hj_lt_lower
      · have hj_lower : j = lower := by
          apply Fin.ext
          exact hj_eq_lower
        subst j
        exact ne_of_lt (by simpa [lower] using hreport_lt_lower)
      · by_cases hj_eq_upper_val : j.val = upper.val
        · have hj_upper : j = upper := by
            apply Fin.ext
            exact hj_eq_upper_val
          exact False.elim (hju hj_upper)
        · have hlower_lt_j_bid : bids lower < bids j := by
            exact hstrict hj_lt_lower
          exact ne_of_lt
            (lt_trans (by simpa [lower] using hreport_lt_lower) hlower_lt_j_bid)
    · have hnext_le_j : next.val ≤ j.val := le_of_not_gt hj_before_next
      have hj_le_next_bid : bids j ≤ bids next := by
        rcases Nat.eq_or_lt_of_le hnext_le_j with hnext_eq_j | hnext_lt_j
        · have hj_next : j = next := by
            apply Fin.ext
            exact hnext_eq_j.symm
          subst j
          exact le_rfl
        · exact le_of_lt (hstrict hnext_lt_j)
      exact ne_of_gt
        (lt_of_le_of_lt hj_le_next_bid (by simpa [next] using hnext_lt_report))
  change ∀ {i j : Fin m},
    i ≠ j → Function.update bids upper report i ≠ Function.update bids upper report j
  intro i j hij
  by_cases hiu : i = upper
  · subst i
    by_cases hju : j = upper
    · exact False.elim (hij hju.symm)
    · simpa [Function.update, hju] using hreport_ne_bid j hju
  · by_cases hju : j = upper
    · subst j
      exact fun heq =>
        (hreport_ne_bid i hiu) (by simpa [Function.update, hiu] using heq.symm)
    · have horig_ne : bids i ≠ bids j := by
        intro hbid
        have hval_ne : i.val ≠ j.val := by
          intro hval
          exact hij (Fin.ext hval)
        rcases lt_or_gt_of_ne hval_ne with hij_val | hji_val
        · have hlt : bids j < bids i := hstrict hij_val
          exact (ne_of_gt hlt) hbid
        · have hlt : bids i < bids j := hstrict hji_val
          exact (ne_of_lt hlt) hbid
      exact fun heq =>
        horig_ne (by simpa [Function.update, hiu, hju] using heq)

/-- In the no-tie adjacent-under-cut profile, the next-bid selector for the
new lower slot is exactly the original next lower rank's bid. -/
theorem paper_ranked_gsp_next_bid_after_adjacent_down_update_more_bidders
    {m n : ℕ} (hnm : n < m) {bids : Fin m → ℝ}
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (k : ℕ) (hk : k + 1 < n) (report : ℝ)
    (hnext_lt_report : bids ⟨k + 2, by omega⟩ < report)
    (hreport_lt_lower : report < bids ⟨k + 1, by omega⟩) :
    paper_ranked_gsp_bid_at_rank
        (Function.update bids ⟨k, by omega⟩ report) (k + 2) =
      bids ⟨k + 2, by omega⟩ := by
  classical
  let upper : Fin m := ⟨k, by omega⟩
  let next : Fin m := ⟨k + 2, by omega⟩
  have hnext_ne_upper : next ≠ upper := by
    intro h
    have hval := congrArg Fin.val h
    simp [next, upper] at hval
  change
    paper_ranked_gsp_bid_at_rank (Function.update bids upper report) (k + 2) =
      bids next
  have hrank_next :
      paper_ranked_gsp_rank (Function.update bids upper report) next = k + 2 := by
    simpa [upper, next] using
      paper_ranked_gsp_next_rank_after_adjacent_down_update_more_bidders
        (bids := bids) hnm hstrict k hk report hnext_lt_report
  have hnotie : ∀ {i j : Fin m}, i ≠ j →
      Function.update bids upper report i ≠ Function.update bids upper report j := by
    intro i j hij
    simpa [upper] using
      (paper_ranked_gsp_no_ties_after_adjacent_down_update_more_bidders
        (bids := bids) hnm hstrict k hk report hnext_lt_report hreport_lt_lower
        (i := i) (j := j) hij)
  have hselected :
      paper_ranked_gsp_bid_at_rank (Function.update bids upper report) (k + 2) =
        Function.update bids upper report next := by
    exact paper_ranked_gsp_bid_at_rank_eq_of_unique
      (bids := Function.update bids upper report) (i := next) hrank_next (by
        intro j hj
        apply paper_ranked_gsp_rank_injective_of_no_ties hnotie
        rw [hj, hrank_next])
  simpa [Function.update, hnext_ne_upper] using hselected

/-- The concrete neighboring downward report exists in every finite `K>N`
ordinary sorted-GSP market and has the source's slot/payment behavior. -/
theorem paper_ranked_gsp_adjacent_down_slot_payment_shape_exists_more_bidders
    {m n : ℕ} (hnm : n < m) {bids : Fin m → ℝ}
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i) :
    ∀ (k : ℕ) (hk : k + 1 < n),
      ∃ report : ℝ,
        (paper_ranked_gsp_mechanism m n
            (Function.update bids ⟨k, by omega⟩ report)).slotOf
            ⟨k, by omega⟩ = some ⟨k + 1, hk⟩ ∧
        (paper_ranked_gsp_mechanism m n
            (Function.update bids ⟨k, by omega⟩ report)).paymentPerClick
            ⟨k, by omega⟩ = bids ⟨k + 2, by omega⟩ := by
  intro k hk
  let lower : Fin m := ⟨k + 1, by omega⟩
  let next : Fin m := ⟨k + 2, by omega⟩
  have hnext_lower : bids next < bids lower := by
    exact hstrict (by simp [lower, next])
  rcases exists_between hnext_lower with ⟨report, hnext_lt_report, hreport_lt_lower⟩
  have hrank :=
    paper_ranked_gsp_rank_after_adjacent_down_update_more_bidders
      (bids := bids) hnm hstrict k hk report
        (by simpa [next] using hnext_lt_report)
        (by simpa [lower] using hreport_lt_lower)
  have hnext_bid :=
    paper_ranked_gsp_next_bid_after_adjacent_down_update_more_bidders
      (bids := bids) hnm hstrict k hk report
        (by simpa [next] using hnext_lt_report)
        (by simpa [lower] using hreport_lt_lower)
  refine ⟨report, ?_, ?_⟩
  · simp [paper_ranked_gsp_mechanism, hrank, hk]
  · simp [paper_ranked_gsp_mechanism, hrank, hnext_bid, Nat.add_assoc]

/-- Nash equilibrium and the concrete `K>N` undercut report imply the
downward adjacent no-envy inequality for each assigned rank. -/
theorem paper_ranked_adjacent_down_no_envy_of_nash_slot_payment_shape_more_bidders
    {m n : ℕ} {value payment clickThroughRate : ℕ → ℝ}
    (hnm : n < m)
    (M : PositionMechanism (Fin m) (Fin n))
    (O : PositionOutcome (Fin m) (Fin n)) (bids : Fin m → ℝ)
    (hout : M bids = O)
    (hslots : ∀ i : Fin n,
      O.slotOf ⟨i.val, by omega⟩ = some i)
    (hpayment : ∀ i : Fin n,
      O.paymentPerClick ⟨i.val, by omega⟩ = payment i.val)
    (hnash :
      M.IsNashEquilibrium
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val) bids)
    (hshape :
      ∀ (k : ℕ) (hk : k + 1 < n),
        ∃ report : ℝ,
          (M (Function.update bids ⟨k, by omega⟩ report)).slotOf
            ⟨k, by omega⟩ = some ⟨k + 1, hk⟩ ∧
          (M (Function.update bids ⟨k, by omega⟩ report)).paymentPerClick
            ⟨k, by omega⟩ = payment (k + 1)) :
    ∀ k : ℕ, k + 1 < n →
      clickThroughRate (k + 1) * (value k - payment (k + 1)) ≤
        clickThroughRate k * (value k - payment k) := by
  intro k hk
  let upperSlot : Fin n := ⟨k, Nat.lt_of_succ_lt hk⟩
  let upperBidder : Fin m := ⟨k, by omega⟩
  rcases hshape k hk with ⟨report, hslot, hpay⟩
  have hnash_report := hnash upperBidder report
  have hslot_upper : O.slotOf upperBidder = some upperSlot := by
    simpa [upperSlot, upperBidder] using hslots upperSlot
  have hpay_upper : O.paymentPerClick upperBidder = payment k := by
    simpa [upperSlot, upperBidder] using hpayment upperSlot
  have hcurrent :
      PositionMechanism.utility
          (paper_theorem7_ranked_environment clickThroughRate)
          M (fun i : Fin m => value i.val) bids upperBidder =
        clickThroughRate k * (value k - payment k) := by
    rw [PositionMechanism.utility, hout, PositionOutcome.utility, hslot_upper]
    simp [paper_theorem7_ranked_environment, hpay_upper, upperSlot, upperBidder]
  calc
    clickThroughRate (k + 1) * (value k - payment (k + 1)) =
        PositionMechanism.utility
          (paper_theorem7_ranked_environment clickThroughRate)
          M (fun i : Fin m => value i.val)
          (Function.update bids upperBidder report) upperBidder := by
            rw [PositionMechanism.utility, PositionOutcome.utility, hslot]
            simp [paper_theorem7_ranked_environment, hpay, upperBidder]
    _ ≤ PositionMechanism.utility
          (paper_theorem7_ranked_environment clickThroughRate)
          M (fun i : Fin m => value i.val) bids upperBidder := hnash_report
    _ = clickThroughRate k * (value k - payment k) := hcurrent

/-- The bottom-slot condition for any particular unassigned bidder telescopes
to every assigned slot.  The proof reuses the finite adjacent algebra with a
temporary rank-`n` value equal to that bidder's value; no ordering among
unassigned bidders is assumed. -/
theorem paper_ranked_unassigned_no_envy_of_bounded_adjacent_rank_no_envy_more_bidders
    {n : ℕ} {value payment clickThroughRate : ℕ → ℝ} (loserValue : ℝ)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k)
    (hup_adj :
      ∀ k : ℕ, k + 1 < n →
        clickThroughRate k * (value (k + 1) - payment k) ≤
          clickThroughRate (k + 1) * (value (k + 1) - payment (k + 1)))
    (hdown_adj :
      ∀ k : ℕ, k + 1 < n →
        clickThroughRate (k + 1) * (value k - payment (k + 1)) ≤
          clickThroughRate k * (value k - payment k))
    (hbottom_click_pos :
      ∀ k : ℕ, k + 1 = n → 0 < clickThroughRate k)
    (hbottom_ir :
      ∀ k : ℕ, k + 1 = n →
        0 ≤ clickThroughRate k * (value k - payment k))
    (hbottom_no_envy :
      ∀ k : ℕ, k + 1 = n →
        clickThroughRate k * (loserValue - payment k) ≤ 0)
    (target : Fin n) :
    clickThroughRate target.val * (loserValue - payment target.val) ≤ 0 := by
  let extendedValue : ℕ → ℝ := fun rank =>
    if rank < n then value rank else loserValue
  have hup : ∀ k : ℕ, k + 1 < n →
      clickThroughRate k * (extendedValue (k + 1) - payment k) ≤
        clickThroughRate (k + 1) *
          (extendedValue (k + 1) - payment (k + 1)) := by
    intro k hk
    simpa [extendedValue, if_pos (Nat.lt_of_succ_lt hk), if_pos hk] using
      hup_adj k hk
  have hdown : ∀ k : ℕ, k + 1 < n →
      clickThroughRate (k + 1) * (extendedValue k - payment (k + 1)) ≤
        clickThroughRate k * (extendedValue k - payment k) := by
    intro k hk
    have hk_lt : k < n := Nat.lt_of_succ_lt hk
    simpa [extendedValue, if_pos hk_lt] using hdown_adj k hk
  have hbottom_ir' : ∀ k : ℕ, k + 1 = n →
      0 ≤ clickThroughRate k * (extendedValue k - payment k) := by
    intro k hk
    have hk_lt : k < n := by omega
    simpa [extendedValue, if_pos hk_lt] using hbottom_ir k hk
  have hbottom_no_envy' : ∀ k : ℕ, k + 1 = n →
      clickThroughRate k * (extendedValue n - payment k) ≤ 0 := by
    intro k hk
    have hn_not_lt : ¬ n < n := lt_irrefl n
    simpa [extendedValue, if_neg hn_not_lt] using hbottom_no_envy k hk
  simpa [extendedValue, if_neg (lt_irrefl n)] using
    paper_ranked_unassigned_no_envy_of_bounded_adjacent_rank_no_envy
      hclick_strict hup hdown hbottom_click_pos hbottom_ir' hbottom_no_envy'
      target

/-- Corrected EOS Lemma 5 on the full finite `K>N` ranked-GSP domain.  The
printed adjacent conditions control assigned ranks; the approved definition
also supplies the bottom-slot inequality separately for every unassigned
bidder, which is exactly what extends stability across an arbitrary tail. -/
theorem corrected_lemma5_ranked_more_bidders_stable_bridge
    {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    {value clickThroughRate : ℕ → ℝ} (bids : Fin m → ℝ)
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n -> clickThroughRate (k + 1) < clickThroughRate k)
    (hcorrected :
      correctedDefinition4LocallyEnvyFree
        (paper_theorem7_ranked_environment clickThroughRate)
        (paper_ranked_gsp_mechanism m n)
        (fun i : Fin m => value i.val) bids n
        (fun rank => if h : rank < n then (⟨rank, Nat.lt_trans h hnm⟩ : Fin m)
          else ⟨0, Nat.lt_trans hn hnm⟩)
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n) else ⟨0, hn⟩)) :
    (paper_ranked_gsp_mechanism m n bids).StableAssignment
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin m => value i.val) := by
  let M := paper_ranked_gsp_mechanism m n
  let E : PositionEnvironment (Fin n) :=
    paper_theorem7_ranked_environment clickThroughRate
  let values : Fin m → ℝ := fun i => value i.val
  let payment : ℕ → ℝ := fun k =>
    if hk : k < n then bids ⟨k + 1, by omega⟩ else 0
  rcases hcorrected with ⟨⟨hnash, _hslots, hup_source⟩, hbottom_source⟩
  have hrealize :=
    paper_ranked_gsp_mechanism_realizes_next_price_of_strict_decreasing_more_bidders
      (bids := bids) hnm hstrict
  have hnotie : ∀ {i j : Fin m}, i ≠ j → bids i ≠ bids j := by
    intro i j hij
    have hval_ne : i.val ≠ j.val := by
      intro hval
      exact hij (Fin.ext hval)
    rcases lt_or_gt_of_ne hval_ne with hij_val | hji_val
    · exact ne_of_gt (hstrict hij_val)
    · exact ne_of_lt (hstrict hji_val)
  have hfeasible : (M bids).FeasibleAssignment := by
    intro i j s hslot_i hslot_j
    have hrank_i : paper_ranked_gsp_rank bids i = s.val := by
      by_cases hi : paper_ranked_gsp_rank bids i < n
      · have hsome : some ⟨paper_ranked_gsp_rank bids i, hi⟩ = some s := by
          simpa [M, paper_ranked_gsp_mechanism, hi] using hslot_i
        exact congrArg Fin.val (Option.some.inj hsome)
      · simp [M, paper_ranked_gsp_mechanism, hi] at hslot_i
    have hrank_j : paper_ranked_gsp_rank bids j = s.val := by
      by_cases hj : paper_ranked_gsp_rank bids j < n
      · have hsome : some ⟨paper_ranked_gsp_rank bids j, hj⟩ = some s := by
          simpa [M, paper_ranked_gsp_mechanism, hj] using hslot_j
        exact congrArg Fin.val (Option.some.inj hsome)
      · simp [M, paper_ranked_gsp_mechanism, hj] at hslot_j
    apply paper_ranked_gsp_rank_injective_of_no_ties hnotie
    exact hrank_i.trans hrank_j.symm
  have hpayment : ∀ i : Fin n,
      (M bids).paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ = payment i.val := by
    intro i
    calc
      (M bids).paymentPerClick ⟨i.val, Nat.lt_trans i.isLt hnm⟩ =
          bids ⟨i.val + 1, by omega⟩ := by
            simpa [M] using hrealize.2.2 i
      _ = payment i.val := by
        simp only [payment, dif_pos i.isLt]
  have hup : ∀ k : ℕ, k + 1 < n ->
      clickThroughRate k * (value (k + 1) - payment k) ≤
        clickThroughRate (k + 1) *
          (value (k + 1) - payment (k + 1)) := by
    intro k hk
    have hk0 : k < n := Nat.lt_of_succ_lt hk
    let upper : Fin n := ⟨k, hk0⟩
    let lower : Fin n := ⟨k + 1, hk⟩
    have hupper : (M bids).paymentPerClick
        ⟨upper.val, Nat.lt_trans upper.isLt hnm⟩ = payment k := by
      simpa [upper] using hpayment upper
    have hlower : (M bids).paymentPerClick
        ⟨lower.val, Nat.lt_trans lower.isLt hnm⟩ = payment (k + 1) := by
      simpa [lower] using hpayment lower
    have hsource := hup_source k hk
    simp only [dif_pos hk0, dif_pos hk] at hsource
    rw [hupper, hlower] at hsource
    simpa [E, values, upper, lower] using hsource
  have hnext_payment : ∀ (k : ℕ) (hk : k + 1 < n),
      bids ⟨k + 2, by omega⟩ = payment (k + 1) := by
    intro k hk
    simp [payment, hk]
  have hshape : ∀ (k : ℕ) (hk : k + 1 < n),
      ∃ report : ℝ,
        (M (Function.update bids ⟨k, by omega⟩ report)).slotOf
          ⟨k, by omega⟩ = some ⟨k + 1, hk⟩ ∧
        (M (Function.update bids ⟨k, by omega⟩ report)).paymentPerClick
          ⟨k, by omega⟩ = payment (k + 1) := by
    intro k hk
    rcases paper_ranked_gsp_adjacent_down_slot_payment_shape_exists_more_bidders
        (bids := bids) hnm hstrict k hk with ⟨report, hslot, hpay⟩
    refine ⟨report, ?_, ?_⟩
    · simpa [M] using hslot
    · rw [show M = paper_ranked_gsp_mechanism m n by rfl, hpay,
        hnext_payment k hk]
  have hdown : ∀ k : ℕ, k + 1 < n ->
      clickThroughRate (k + 1) * (value k - payment (k + 1)) ≤
        clickThroughRate k * (value k - payment k) := by
    exact
      paper_ranked_adjacent_down_no_envy_of_nash_slot_payment_shape_more_bidders
        hnm M (M bids) bids rfl hrealize.1 hpayment
        (by simpa [M, E, values] using hnash) hshape
  have hbottom_ir : ∀ k : ℕ, k + 1 = n ->
      0 ≤ clickThroughRate k * (value k - payment k) := by
    intro k hk
    let bottom : Fin n := ⟨k, by omega⟩
    have hslot : (M bids).slotOf
        ⟨bottom.val, Nat.lt_trans bottom.isLt hnm⟩ = some bottom :=
      hrealize.1 bottom
    have hpay : (M bids).paymentPerClick
        ⟨bottom.val, Nat.lt_trans bottom.isLt hnm⟩ = payment k := by
      simpa [bottom] using hpayment bottom
    have hir : 0 ≤ (M bids).utility E values
        ⟨bottom.val, Nat.lt_trans bottom.isLt hnm⟩ := by
      simpa [M, E, values] using
        paper_ranked_gsp_more_bidders_individually_rational_of_nash
          hnm bids hstrict hnash
          ⟨bottom.val, Nat.lt_trans bottom.isLt hnm⟩
    rw [PositionOutcome.utility, hslot, hpay] at hir
    simpa [E, values, bottom] using hir
  have hbottom_no_envy : ∀ (loser : Fin m), n ≤ loser.val ->
      ∀ k : ℕ, k + 1 = n ->
        clickThroughRate k * (value loser.val - payment k) ≤ 0 := by
    intro loser hloser k hk
    let bottom : Fin n := ⟨k, by omega⟩
    have hpay : (M bids).paymentPerClick
        ⟨bottom.val, Nat.lt_trans bottom.isLt hnm⟩ = payment k := by
      simpa [bottom] using hpayment bottom
    have hsource := hbottom_source loser (hrealize.2.1 loser hloser) k hk
    have hk_lt : k < n := by omega
    simp only [dif_pos hk_lt] at hsource
    rw [hpay] at hsource
    simpa [E, values, bottom] using hsource
  have hIR : (M bids).IndividuallyRational E values := by
    simpa [M, E, values] using
      paper_ranked_gsp_more_bidders_individually_rational_of_nash
        hnm bids hstrict hnash
  refine ⟨hfeasible, hIR, ?_⟩
  intro i j s hslot_j
  by_cases hj_alloc : j.val < n
  · let target : Fin n := ⟨j.val, hj_alloc⟩
    have hj_eq : j = ⟨target.val, Nat.lt_trans target.isLt hnm⟩ := by
      apply Fin.ext
      rfl
    rw [hj_eq] at hslot_j ⊢
    have hs : s = target := by
      have htarget : target = s := by
        simpa [hrealize.1 target] using hslot_j
      exact htarget.symm
    rw [hs]
    by_cases hi_alloc : i.val < n
    · let bidder : Fin n := ⟨i.val, hi_alloc⟩
      have hi_eq : i = ⟨bidder.val, Nat.lt_trans bidder.isLt hnm⟩ := by
        apply Fin.ext
        rfl
      rw [hi_eq]
      have horiented :=
        paper_ranked_bounded_oriented_adjacent_no_envy_of_adjacent_rank_no_envy
          hclick_strict hup hdown
      have hpair :=
        paper_ranked_pairwise_no_envy_of_bounded_oriented_adjacent_no_envy
          horiented.1 horiented.2 bidder target
      have hown :
          (M bids).utility E values
              ⟨bidder.val, Nat.lt_trans bidder.isLt hnm⟩ =
            clickThroughRate bidder.val *
              (value bidder.val - payment bidder.val) := by
        have hslot_bidder : (M bids).slotOf
            ⟨bidder.val, Nat.lt_trans bidder.isLt hnm⟩ = some bidder := by
          simpa [M] using hrealize.1 bidder
        rw [PositionOutcome.utility, hslot_bidder, hpayment bidder]
        rfl
      calc
        E.clickThroughRate target *
            (values ⟨bidder.val, Nat.lt_trans bidder.isLt hnm⟩ -
              (M bids).paymentPerClick
                ⟨target.val, Nat.lt_trans target.isLt hnm⟩) =
            clickThroughRate target.val *
              (value bidder.val - payment target.val) := by
                change clickThroughRate target.val *
                  (value bidder.val - (M bids).paymentPerClick
                    ⟨target.val, Nat.lt_trans target.isLt hnm⟩) = _
                rw [hpayment target]
        _ ≤ clickThroughRate bidder.val *
              (value bidder.val - payment bidder.val) := hpair
        _ = (M bids).utility E values
              ⟨bidder.val, Nat.lt_trans bidder.isLt hnm⟩ := hown.symm
    · have hloser : n ≤ i.val := Nat.le_of_not_gt hi_alloc
      have hnone : (M bids).slotOf i = none := hrealize.2.1 i hloser
      have hnoenvy :=
        paper_ranked_unassigned_no_envy_of_bounded_adjacent_rank_no_envy_more_bidders
          (value i.val) hclick_strict hup hdown
          (by
            intro k hk
            exact hclick_pos ⟨k, by omega⟩)
          hbottom_ir (hbottom_no_envy i hloser) target
      calc
        E.clickThroughRate target *
            (values i - (M bids).paymentPerClick
              ⟨target.val, Nat.lt_trans target.isLt hnm⟩) =
            clickThroughRate target.val * (value i.val - payment target.val) := by
              change clickThroughRate target.val *
                (value i.val - (M bids).paymentPerClick
                  ⟨target.val, Nat.lt_trans target.isLt hnm⟩) = _
              rw [hpayment target]
        _ ≤ 0 := hnoenvy
        _ = (M bids).utility E values i := by
          simp [PositionOutcome.utility, hnone]
  · have hnone : (M bids).slotOf j = none :=
      hrealize.2.1 j (Nat.le_of_not_gt hj_alloc)
    rw [hnone] at hslot_j
    cases hslot_j

end
end PaperInterface
end EOS07GSP
