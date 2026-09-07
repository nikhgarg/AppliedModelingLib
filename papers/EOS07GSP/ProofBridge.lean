import EOS07GSP.Implementation
import EOS07GSP.PostPaperAudit
import EOS07GSP.Assumptions
import EOS07GSP.ContinuousHistory
import EOS07GSP.OrderedExPost
import EOS07GSP.FullHistoryFiniteBridge
import EOS07GSP.FiniteStaticBridge
import EOS07GSP.FiniteLemma6Bridge
import EOS07GSP.FiniteLemma5MoreBiddersBridge
import EOS07GSP.FiniteTheorem7ComparisonBridge
import EOS07GSP.SourceRemark3Bridge

/-!
# Paper Interface: Internet Advertising and the Generalized Second-Price Auction

This is the compact human-review surface for Edelman, Ostrovsky, and Schwarz,
*Internet Advertising and the Generalized Second-Price Auction*.  It exposes the
paper-facing definitions and named results; implementation and audit ledgers
remain in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

namespace EOS07GSP
namespace ProofBridge

open AppliedModelingLib.Auction
open EOS07GSP.PaperInterface

/-- Direct corrected finite seller-minimal-revenue endpoint for EOS Theorem 7.
The proof is the source's backward stable-payment induction, including its
first-unassigned-bidder terminal price, rather than a comparison certificate. -/
theorem theorem7_finite_static_bstar_revenue_minimal_corrected
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
  exact eos_finite_static_bstar_revenue_le_of_corrected_ranked_gsp
    hnm model bids hstrict hcorrected

/-- Complete corrected finite Theorem 7 endpoint, joining the direct B-star
equilibrium/VCG ledger to the direct seller-minimal-revenue comparison. -/
theorem theorem7_finite_static_bstar_full_corrected
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
    (((paper_ranked_gsp_tiebreak_mechanism (n + 1) n).LocallyEnvyFreeEquilibrium
        (paper_theorem7_ranked_environment model.clickThroughRate)
        (fun i : Fin (n + 1) => model.value i.val)
        (eosFiniteStaticBStarBids model) ∧
      (∀ i : Fin n,
        (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
          (eosFiniteStaticBStarBids model)).slotOf i.castSucc = some i) ∧
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model)).slotOf (Fin.last n) = none ∧
      (∀ i : Fin n,
        model.clickThroughRate i.val *
          (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
            (eosFiniteStaticBStarBids model)).paymentPerClick i.castSucc =
          model.vcgTotalPayment i.val)) ∧
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model)).revenue
          (paper_theorem7_ranked_environment model.clickThroughRate) ≤
        (paper_ranked_gsp_mechanism m n bids).revenue
          (paper_theorem7_ranked_environment model.clickThroughRate)) := by
  exact ⟨eos_finite_static_bstar_tiebreak_source_conclusion model,
    theorem7_finite_static_bstar_revenue_minimal_corrected
      hnm model bids hstrict hcorrected⟩

/-- Definition 4: a static GSP equilibrium is locally envy-free exactly when
each allocated bidder weakly prefers her current rank to exchanging with the
bidder one rank above.  This theorem exposes the paper's displayed inequality
directly rather than counting a proposition-valued abbreviation as proof.

Source status: direct proved unfolding of Definition 4 in the pinned NBER text. -/
theorem definition4_locally_envy_free
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) :
    sourceDefinition4LocallyEnvyFree E M values bids allocatedPositions
        bidderAtRank slotAtRank ↔
      M.IsNashEquilibrium E values bids ∧
        (∀ rank : ℕ, rank < allocatedPositions →
          (M bids).slotOf (bidderAtRank rank) = some (slotAtRank rank)) ∧
        ∀ rank : ℕ, rank + 1 < allocatedPositions →
          E.clickThroughRate (slotAtRank rank) *
              (values (bidderAtRank (rank + 1)) -
                (M bids).paymentPerClick (bidderAtRank rank)) ≤
            E.clickThroughRate (slotAtRank (rank + 1)) *
              (values (bidderAtRank (rank + 1)) -
                (M bids).paymentPerClick (bidderAtRank (rank + 1))) := by
  rfl

/--
Project-approved Definition 4 correction: in addition to the printed
allocated-rank adjacent inequalities, every unassigned bidder must not prefer
the bottom allocated slot at its recorded payment.  The target deliberately
does not relabel this as a direct unfolding of the archival source.
-/
theorem corrected_definition4_locally_envy_free
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) :
    correctedDefinition4LocallyEnvyFree E M values bids allocatedPositions
        bidderAtRank slotAtRank ↔
      sourceDefinition4LocallyEnvyFree E M values bids allocatedPositions
          bidderAtRank slotAtRank ∧
        ∀ bidder : Bidder, (M bids).slotOf bidder = none →
          ∀ rank : ℕ, rank + 1 = allocatedPositions →
            E.clickThroughRate (slotAtRank rank) *
                (values bidder -
                  (M bids).paymentPerClick (bidderAtRank rank)) ≤ 0 := by
  rfl

/--
Project-approved Lemma 6 domain clarification.  The strengthened domain keeps
the source stable-assignment condition but rules out zero-surplus assigned
bidders, which are precisely the boundary at which the Appendix construction
can produce an equilibrium bid tie.
-/
theorem corrected_lemma6_stable_assignment
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) :
    correctedLemma6StableAssignment E values O ↔
      O.StableAssignment E values ∧
        ∀ (bidder : Bidder) (slot : Slot), O.slotOf bidder = some slot →
          0 < O.utility E values bidder := by
  rfl

/-- Direct finite amended Lemma 6 endpoint.  The owner-approved strict-surplus
domain is sufficient to make the Appendix construction strict, and the
constructed profile then realizes the ranked assignment as a locally envy-free
tie-broken GSP equilibrium. -/
theorem corrected_lemma6_ranked_one_extra_constructs_tiebreak_equilibrium
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
  exact
    EOS07GSP.PaperInterface.corrected_lemma6_ranked_one_extra_constructs_tiebreak_equilibrium_bridge
      O hcorrected hslots hunassigned hpayment hunassigned_payment hclick_pos
      hclick_strict

/-- Direct full-`K>N` endpoint for the owner-approved strict-surplus Lemma 6
amendment.  It makes the source's outcome convention explicit by comparing
only payments of bidders who actually receive a position. -/
theorem corrected_lemma6_ranked_more_bidders_constructs_tiebreak_equilibrium
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
  exact
    EOS07GSP.PaperInterface.corrected_lemma6_ranked_more_bidders_constructs_tiebreak_equilibrium_bridge
      hn hnm O hcorrected hslots hunassigned hpayment hclick_pos hclick_strict

/-- A finite strictly ordered GSP Nash profile is individually rational: every
bidder can report below the current last bid and receive no position. -/
theorem ranked_gsp_one_extra_individually_rational_of_nash
    {n : ℕ} {value clickThroughRate : ℕ → ℝ}
    (bids : Fin (n + 1) → ℝ)
    (hstrict :
      ∀ {i j : Fin (n + 1)}, i.val < j.val → bids j < bids i)
    (hnash :
      (paper_ranked_gsp_mechanism (n + 1) n).IsNashEquilibrium
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val) bids) :
    (paper_ranked_gsp_mechanism (n + 1) n bids).IndividuallyRational
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin (n + 1) => value i.val) := by
  classical
  intro i
  let report : ℝ := bids (Fin.last n) - 1
  have hlast_le : ∀ j : Fin (n + 1), bids (Fin.last n) ≤ bids j := by
    intro j
    by_cases hj : j = Fin.last n
    · subst j
      exact le_rfl
    · have hj_lt : j.val < n := by
        by_contra hnot
        apply hj
        apply Fin.ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.le_of_not_gt hnot)
      exact le_of_lt (hstrict hj_lt)
  have hbelow : ∀ j : Fin (n + 1), j ≠ i → report < bids j := by
    intro j _
    dsimp [report]
    linarith [hlast_le j]
  let updated : Fin (n + 1) → ℝ := Function.update bids i report
  have hrank : paper_ranked_gsp_rank updated i = n := by
    unfold paper_ranked_gsp_rank
    have hfilter :
        ((Finset.univ : Finset (Fin (n + 1))).filter fun j =>
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
      (paper_ranked_gsp_mechanism (n + 1) n updated).slotOf i = none := by
    simp [paper_ranked_gsp_mechanism, hrank]
  have hzero :
      PositionMechanism.utility
          (paper_theorem7_ranked_environment clickThroughRate)
          (paper_ranked_gsp_mechanism (n + 1) n)
          (fun i : Fin (n + 1) => value i.val) updated i = 0 := by
    simp [PositionMechanism.utility, PositionOutcome.utility, hslot]
  rw [← hzero]
  simpa [updated] using hnash i report

/--
Finite corrected Lemma 5 algebra for the source's one-extra-bidder market.
The printed adjacent inequalities and the approved bottom-slot condition are
used directly; strict no-tie bids make the ranked GSP allocation/payment
ledger concrete.  Individual rationality is kept explicit here while the
separate finite low-report argument is connected to the static-game endpoint.
-/
theorem corrected_lemma5_ranked_one_extra_stable_of_individually_rational
    {n : ℕ} {value clickThroughRate : ℕ → ℝ}
    (bids : Fin (n + 1) → ℝ)
    (hstrict :
      ∀ {i j : Fin (n + 1)}, i.val < j.val → bids j < bids i)
    (hn : 0 < n)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k)
    (hIR :
      (paper_ranked_gsp_mechanism (n + 1) n bids).IndividuallyRational
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val))
    (hcorrected :
      correctedDefinition4LocallyEnvyFree
        (paper_theorem7_ranked_environment clickThroughRate)
        (paper_ranked_gsp_mechanism (n + 1) n)
        (fun i : Fin (n + 1) => value i.val) bids n
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n).castSucc else 0)
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n) else ⟨0, hn⟩)) :
    (paper_ranked_gsp_mechanism (n + 1) n bids).StableAssignment
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin (n + 1) => value i.val) := by
  let M := paper_ranked_gsp_mechanism (n + 1) n
  let E : PositionEnvironment (Fin n) :=
    paper_theorem7_ranked_environment clickThroughRate
  let values : Fin (n + 1) → ℝ := fun i => value i.val
  let payment : ℕ → ℝ := fun k =>
    if hk : k < n then bids ⟨k + 1, Nat.succ_lt_succ hk⟩ else 0
  rcases hcorrected with ⟨⟨hnash, _hslots, hup_source⟩, hbottom_source⟩
  have hrealize :=
    paper_ranked_gsp_mechanism_realizes_next_price_of_strict_decreasing
      (bids := bids) hstrict
  have hfeasible : (M bids).FeasibleAssignment := by
    intro i j s hslot_i hslot_j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · have hi : (some i : Option (Fin n)) = some s := by
          rw [← hrealize.1 i]
          exact hslot_i
        have hj : (some j : Option (Fin n)) = some s := by
          rw [← hrealize.1 j]
          exact hslot_j
        have hij : i = j := Option.some.inj (hi.trans hj.symm)
        subst j
        rfl
      · rw [hrealize.2.1] at hslot_j
        cases hslot_j
    · rw [hrealize.2.1] at hslot_i
      cases hslot_i
  have hpayment : ∀ i : Fin n,
      (M bids).paymentPerClick i.castSucc = payment i.val := by
    intro i
    calc
      (M bids).paymentPerClick i.castSucc = bids i.succ := by
        simpa [M] using hrealize.2.2 i
      _ = payment i.val := by
        simp only [payment, dif_pos i.isLt]
        congr 1
  have hup : ∀ k : ℕ, k + 1 < n →
      clickThroughRate k * (value (k + 1) - payment k) ≤
        clickThroughRate (k + 1) * (value (k + 1) - payment (k + 1)) := by
    intro k hk
    have hk0 : k < n := by omega
    have hupper : (M bids).paymentPerClick
        (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n).castSucc = payment k :=
      hpayment ⟨k, Nat.lt_of_succ_lt hk⟩
    have hlower : (M bids).paymentPerClick
        (⟨k + 1, hk⟩ : Fin n).castSucc = payment (k + 1) :=
      hpayment ⟨k + 1, hk⟩
    have hsource := hup_source k hk
    simp only [dif_pos hk0, dif_pos hk] at hsource
    have hupper' :
        (paper_ranked_gsp_mechanism (n + 1) n bids).paymentPerClick
            (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n).castSucc = payment k := by
      simpa [M] using hupper
    have hlower' :
        (paper_ranked_gsp_mechanism (n + 1) n bids).paymentPerClick
            (⟨k + 1, hk⟩ : Fin n).castSucc = payment (k + 1) := by
      simpa [M] using hlower
    rw [hupper', hlower'] at hsource
    simpa [paper_theorem7_ranked_environment] using hsource
  have hnext_payment : ∀ (k : ℕ) (hk : k + 1 < n),
      bids ⟨k + 2, Nat.succ_lt_succ hk⟩ = payment (k + 1) := by
    intro k hk
    simp [payment, hk]
  have hshape : ∀ (k : ℕ) (hk : k + 1 < n),
      ∃ report : ℝ,
        (M (Function.update bids
            ⟨k, Nat.lt_trans (Nat.lt_succ_self k)
              (Nat.lt_trans hk (Nat.lt_succ_self n))⟩ report)).slotOf
            ⟨k, Nat.lt_trans (Nat.lt_succ_self k)
              (Nat.lt_trans hk (Nat.lt_succ_self n))⟩ =
            some ⟨k + 1, hk⟩ ∧
        (M (Function.update bids
            ⟨k, Nat.lt_trans (Nat.lt_succ_self k)
              (Nat.lt_trans hk (Nat.lt_succ_self n))⟩ report)).paymentPerClick
            ⟨k, Nat.lt_trans (Nat.lt_succ_self k)
              (Nat.lt_trans hk (Nat.lt_succ_self n))⟩ = payment (k + 1) := by
    intro k hk
    rcases paper_ranked_gsp_adjacent_down_slot_payment_shape_exists
        (bids := bids) hstrict k hk with ⟨report, hslot, hpay⟩
    refine ⟨report, ?_, ?_⟩
    · simpa [M] using hslot
    · rw [show M = paper_ranked_gsp_mechanism (n + 1) n by rfl]
      rw [hpay, hnext_payment k hk]
  have hdown : ∀ k : ℕ, k + 1 < n →
      clickThroughRate (k + 1) * (value k - payment (k + 1)) ≤
        clickThroughRate k * (value k - payment k) := by
    exact
      paper_ranked_adjacent_down_no_envy_of_nash_slot_payment_shape_one_extra
        M (M bids) bids rfl hrealize.1 hpayment
        (by simpa [M, E, values] using hnash) hshape
  have hbottom_ir : ∀ k : ℕ, k + 1 = n →
      0 ≤ clickThroughRate k * (value k - payment k) := by
    intro k hk
    let bottom : Fin n := ⟨k, by omega⟩
    have hslot : (M bids).slotOf bottom.castSucc = some bottom := hrealize.1 bottom
    have hpay : (M bids).paymentPerClick bottom.castSucc = payment k := by
      simpa [bottom] using hpayment bottom
    have hir : 0 ≤ (M bids).utility E values bottom.castSucc := by
      simpa [M, E, values] using hIR bottom.castSucc
    rw [PositionOutcome.utility, hslot, hpay] at hir
    simpa [E, values, bottom] using hir
  have hbottom_no_envy : ∀ k : ℕ, k + 1 = n →
      clickThroughRate k * (value n - payment k) ≤ 0 := by
    intro k hk
    let bottom : Fin n := ⟨k, by omega⟩
    have hpay : (M bids).paymentPerClick bottom.castSucc = payment k := by
      simpa [bottom] using hpayment bottom
    have hbottom := hbottom_source (Fin.last n) hrealize.2.1 k hk
    have hk_lt : k < n := by omega
    simp only [dif_pos hk_lt] at hbottom
    have hpay' :
        (paper_ranked_gsp_mechanism (n + 1) n bids).paymentPerClick
            bottom.castSucc = payment k := by
      simpa [M] using hpay
    rw [hpay'] at hbottom
    simpa [paper_theorem7_ranked_environment, bottom] using hbottom
  exact
    paper_ranked_one_extra_bidder_stable_assignment_of_bounded_adjacent_rank_no_envy
      (M bids) hfeasible (by simpa [M, E, values] using hIR)
      hrealize.1 hrealize.2.1 hpayment hclick_strict hup hdown
      (by
        intro k hk
        exact hclick_pos ⟨k, by omega⟩)
      hbottom_ir hbottom_no_envy

/--
Corrected finite Lemma 5 for the source's `K = N + 1` market. Strict no-tie
bids instantiate the source's random-tie convention on path; Nash yields
individual rationality through a strictly lower report. The proof then uses
the printed adjacent inequalities together with the approved all-unassigned
bottom-slot condition to establish stable assignment.
-/
theorem corrected_lemma5_ranked_one_extra_stable
    {n : ℕ} {value clickThroughRate : ℕ → ℝ}
    (bids : Fin (n + 1) → ℝ)
    (hstrict :
      ∀ {i j : Fin (n + 1)}, i.val < j.val → bids j < bids i)
    (hn : 0 < n)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k)
    (hcorrected :
      correctedDefinition4LocallyEnvyFree
        (paper_theorem7_ranked_environment clickThroughRate)
        (paper_ranked_gsp_mechanism (n + 1) n)
        (fun i : Fin (n + 1) => value i.val) bids n
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n).castSucc else 0)
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n) else ⟨0, hn⟩)) :
    (paper_ranked_gsp_mechanism (n + 1) n bids).StableAssignment
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin (n + 1) => value i.val) := by
  apply
    corrected_lemma5_ranked_one_extra_stable_of_individually_rational
      bids hstrict hn hclick_pos hclick_strict
  · exact ranked_gsp_one_extra_individually_rational_of_nash bids hstrict
      hcorrected.1.1
  · exact hcorrected

/-- Corrected EOS Lemma 5 on the full finite source domain `K>N`.  The
ordinary sorted-GSP mechanism is used directly; strict bids make the
next-price and adjacent-under-cut ledger unambiguous, while the corrected
Definition 4 bottom condition applies separately to every unassigned bidder. -/
theorem corrected_lemma5_ranked_more_bidders_stable
    {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    {value clickThroughRate : ℕ → ℝ} (bids : Fin m → ℝ)
    (hstrict :
      ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k)
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
  exact
    EOS07GSP.PaperInterface.corrected_lemma5_ranked_more_bidders_stable_bridge
      hn hnm bids hstrict hclick_pos hclick_strict hcorrected

/-- The source assignment-game price convention: `paymentPerClick` is a
per-click price, so the source's total payment `p_ik` is click-through rate
times that price. Stability itself is used by Lemmas 5--6 through the standard
no-profitable-rematch predicate, rather than asserted to be a verbatim
definition in the short source passage. -/
theorem stable_assignment
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) :
    ∀ (i : Bidder) (s : Slot), O.slotOf i = some s →
      O.utility E values i =
        E.clickThroughRate s * values i -
          E.clickThroughRate s * O.paymentPerClick i := by
  intro i s hslot
  simp [PositionOutcome.utility, hslot, mul_sub]

/-- Section 2.2 first-price example: successive bid revisions are profitable. -/
abbrev first_price_running_example_profitable_revision_chain :=
  @EOS07GSP.audit_first_price_running_example_profitable_revision_chain

/-- Remark 1: the source's total GSP payment weakly dominates the VCG total
payment at a rank under a common ranked bid profile. -/
abbrev remark1_gsp_payments_weakly_dominate_vcg :=
  @EOS07GSP.paper_remark1_ranked_vcg_tail_payment_le_truthful_gsp_total_payment

/-- Remark 2: VCG position mechanism is truthful. -/
abbrev remark2_vcg_truthful :=
  @EOS07GSP.audit_remark2_finite_position_vcg_truthful

/-- Remark 3: the exact printed `(10,4,2)`, `(200,199)`, bid-`3` witness
shows GSP is not dominant-strategy truthful. -/
abbrev remark3_gsp_not_truthful :=
  EOS07GSP.remark3_source_not_truthful

/-- Running example: truthful GSP bids are a Nash equilibrium. -/
abbrev running_example_truthful_gsp_nash :=
  @EOS07GSP.audit_running_example_truthful_gsp_is_nash

/-- Running example: truthful GSP revenue exceeds VCG revenue. -/
abbrev running_example_truthful_gsp_revenue_comparison :=
  @EOS07GSP.audit_running_example_truthful_gsp_revenue_gt_vcg_revenue

/-- Lemma 5: locally envy-free equilibrium gives a stable assignment. -/
theorem lemma5_locally_envy_free_stable
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) :
    (M bids).StableAssignment E values := by
  exact
    EOS07GSP.audit_lemma5_locally_envy_free_equilibrium_stable_assignment
      E M values bids hfeasible hIR h

/-- Lemma 6: stable assignment gives LEF equilibrium when bidders exceed slots. -/
theorem lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free
    {m n : ℕ} (hnm : n < m) {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n)) (bids : Fin m → ℝ)
    (hout : paper_ranked_gsp_tiebreak_mechanism m n bids = O)
    (hstrict : ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val)) :
    (paper_ranked_gsp_tiebreak_mechanism m n).LocallyEnvyFreeEquilibrium
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin m => value i.val) bids := by
  exact
    EOS07GSP.audit_lemma6_more_bidders_tiebreak_ranked_gsp_stable_assignment_locally_envy_free
      hnm O bids hout hstrict hclick_nonneg hstable

/-- Theorem 7: ranked GSP realizes the constructed `B*` next-price outcome. -/
theorem theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_pos : ∀ i, 0 < clickThroughRate i)
    (hclick_strict_mono : ∀ i, clickThroughRate (i + 1) < clickThroughRate i)
    (hrec :
      ∀ i : ℕ,
        vcgTotalPayment i =
          (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
            vcgTotalPayment (i + 1))
    (hpayment_lt_value :
      ∀ i : ℕ, vcgTotalPayment i < clickThroughRate i * value i) :
    (∀ i : Fin n,
        (paper_ranked_gsp_mechanism (n + 1) n
            (fun bidder : Fin (n + 1) =>
              paper_theorem7_bstar_bid
                value vcgTotalPayment clickThroughRate bidder.val)).slotOf
            i.castSucc =
          some i) ∧
      (paper_ranked_gsp_mechanism (n + 1) n
          (fun bidder : Fin (n + 1) =>
            paper_theorem7_bstar_bid
              value vcgTotalPayment clickThroughRate bidder.val)).slotOf
          (Fin.last n) =
        none ∧
      ∀ i : Fin n,
        (paper_ranked_gsp_mechanism (n + 1) n
            (fun bidder : Fin (n + 1) =>
              paper_theorem7_bstar_bid
                value vcgTotalPayment clickThroughRate bidder.val)).paymentPerClick
            i.castSucc =
          (paper_theorem7_ranked_bstar_outcome (n := n)
            value vcgTotalPayment clickThroughRate).paymentPerClick i := by
  exact
    EOS07GSP.audit_theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome
      hclick_pos hclick_strict_mono hrec hpayment_lt_value

/-- Theorem 7: ranked `B*` payment identity.
Source status: formalizes the paper's recursive VCG-payment and `B*` bid
identity in the ranked finite model. -/
theorem theorem7_bstar_payment_identity
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : ℕ)
    (hclick_ne : clickThroughRate i ≠ 0) :
    clickThroughRate i *
      paper_theorem7_bstar_bid value vcgTotalPayment clickThroughRate (i + 1) =
      vcgTotalPayment i := by
  exact
    EOS07GSP.audit_theorem7_bstar_payment_identity
      value vcgTotalPayment clickThroughRate i hclick_ne

/-- Theorem 7: the ranked `B*` outcome is locally envy-free.
Source status: direct row for the source subclaim that `B*` is locally
envy-free; the strict tie-broken GSP comparison row below carries the
mechanism-level equilibrium comparison. -/
theorem theorem7_bstar_locally_envy_free
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1)) :
    ∀ (i j : Fin n) (s : Fin n),
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate).slotOf j = some s →
        (paper_theorem7_ranked_environment clickThroughRate).clickThroughRate s *
            (value i.val -
              (paper_theorem7_ranked_bstar_outcome
                value vcgTotalPayment clickThroughRate).paymentPerClick j) ≤
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).utility
              (paper_theorem7_ranked_environment clickThroughRate)
              (fun i : Fin n => value i.val) i := by
  exact
    EOS07GSP.audit_theorem7_slot_envy_free_of_ordered_values
      hclick_ne hclick_mono hvalue_mono hrec

/-- Theorem 7: canonical tail conclusion with no positive transfers.
Source status: direct primitive-binder statement for the source's `B*`
construction and VCG-payment comparison. -/
theorem theorem7_no_positive_transfer_conclusion
    {n : ℕ}
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hclick_pos : ∀ s : Fin n, 0 < clickThroughRate s.val)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hvcg_rec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
            vcgTotalPayment (k + 1))
    (hpayment_le_value :
      ∀ i : Fin n, vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val)
    (hvcg_tail_eq :
      ∀ i : Fin n,
        vcgTotalPayment i.val =
          paper_theorem7_ranked_vcg_tail_payment value clickThroughRate i.val
            (paper_theorem7_ranked_canonical_tail_remaining i))
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    ∃ O : PositionOutcome (Fin n) (Fin n),
      paper_position_no_positive_transfers O ∧
        O.SlotEnvyFree
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        O.StableAssignment
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        (∀ i,
          O.slotOf i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).slotOf i) ∧
        (∀ i,
          O.paymentPerClick i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).paymentPerClick i) ∧
        ∀ other : PositionOutcome (Fin n) (Fin n),
          other.FeasibleAssignment →
          other.IndividuallyRational
            (paper_theorem7_ranked_environment clickThroughRate)
            (fun i : Fin n => value i.val) →
          other.SlotEnvyFree
            (paper_theorem7_ranked_environment clickThroughRate)
            (fun i : Fin n => value i.val) →
          (∀ i, O.slotOf i = other.slotOf i) →
          paper_position_no_positive_transfers other →
          O.revenue (paper_theorem7_ranked_environment clickThroughRate) ≤
            other.revenue (paper_theorem7_ranked_environment clickThroughRate) := by
  exact
    theorem7_ranked_bstar_no_positive_transfer_conclusion_from_primitives
      value vcgTotalPayment clickThroughRate hclick_nonneg hclick_pos
      hclick_mono hvalue_mono hvcg_rec hpayment_le_value hvcg_tail_eq
      hvalue_nonneg

/-- Theorem 7: strict source ordering derives sorted GSP comparison slots.
Source status: direct primitive-binder statement for the source's tie-broken
ranking and GSP/VCG comparison. -/
theorem theorem7_strict_tiebreak_gsp_comparison_conclusion
    {n : ℕ}
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hclick_pos : ∀ s : Fin n, 0 < clickThroughRate s.val)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hvcg_rec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
            vcgTotalPayment (k + 1))
    (hpayment_le_value :
      ∀ i : Fin n, vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val)
    (hvcg_tail_eq :
      ∀ i : Fin n,
        vcgTotalPayment i.val =
          paper_theorem7_ranked_vcg_tail_payment value clickThroughRate i.val
            (paper_theorem7_ranked_canonical_tail_remaining i))
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_strict : ∀ k : ℕ, k + 1 < n → value (k + 1) < value k)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    ∃ O : PositionOutcome (Fin n) (Fin n),
      paper_position_no_positive_transfers O ∧
        O.SlotEnvyFree
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        O.StableAssignment
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        (∀ i,
          O.slotOf i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).slotOf i) ∧
        (∀ i,
          O.paymentPerClick i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).paymentPerClick i) ∧
        ∀ bids : Fin n → ℝ,
          (paper_ranked_gsp_tiebreak_mechanism n n).LocallyEnvyFreeEquilibrium
            (paper_theorem7_ranked_environment clickThroughRate)
            (fun i : Fin n => value i.val) bids →
          (∀ i, 0 ≤ bids i) →
            O.revenue (paper_theorem7_ranked_environment clickThroughRate) ≤
              (paper_ranked_gsp_tiebreak_mechanism n n bids).revenue
                (paper_theorem7_ranked_environment clickThroughRate) := by
  exact
    EOS07GSP.PaperInterface.theorem7_ranked_bstar_strict_tiebreak_gsp_comparison_from_primitives
      value vcgTotalPayment clickThroughRate hclick_nonneg hclick_pos
      hclick_mono hvalue_mono hvcg_rec hpayment_le_value hvcg_tail_eq
      hvalue_nonneg hvalue_strict hclick_strict

/-- Theorem 8: the displayed dropout-price formula equals the finite `B*` threshold.
Source status: algebraic bridge from the paper's `q` formula to finite `B*`
continuation prices. -/
abbrev theorem8_dropout_formula_eq_bstar_threshold :=
  @EOS07GSP.PaperInterface.theorem8_ranked_dropout_formula_eq_bstar_threshold

/-- Theorem 8 Step 2: waiting below `q` is strictly better. -/
theorem theorem8_q_step2_waiting_before_q_review
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hclock_lt :
      state.clockPrice <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank) :
    clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) <
      clickThroughRate rank * (value (rank + 1) - state.clockPrice) := by
  exact
    EOS07GSP.PaperInterface.theorem8_source_step2_waiting_before_q_strictly_better
      hclick_pos hclock_lt

/-- Theorem 8 Step 1: dropping above `q` is strictly better. -/
theorem theorem8_q_step1_dropping_after_q_review
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hthreshold_lt :
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank <
        state.clockPrice) :
    clickThroughRate rank * (value (rank + 1) - state.clockPrice) <
      clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) := by
  exact
    EOS07GSP.PaperInterface.theorem8_source_step1_dropping_after_q_strictly_better
      hclick_pos hthreshold_lt

/-- Theorem 8: `q` lies in the weak source interval. -/
abbrev theorem8_q_mem_interval_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_mem_interval

/-- Theorem 8: `q` lies in the strict source interval. -/
abbrev theorem8_q_strict_mem_interval_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_strict_mem_interval

/-- Theorem 8: `q` is continuous in value. -/
theorem theorem8_q_continuous_value_review
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) :
    Continuous
      (fun bidderValue : ℝ =>
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout
          (Function.update value (rank + 1) bidderValue)
          rank) := by
  exact
    EOS07GSP.PaperInterface.theorem8_source_q_continuous_value
      clickThroughRate lastDropout value rank

/-- Theorem 8: continuous one-step best responses agree with the formula on support.
Source status: the Step 1/Step 2 payoff comparison implied by the source's
ex-post PBE proof identifies the displayed dropout formula on the support. -/
theorem theorem8_continuous_source_local_best_response_support_unique_review
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    let namedStrategy := theorem8ContinuousSourceStrategy clickThroughRate
    namedStrategy.ContinuousInValuation ∧
      Theorem8ContinuousSourceOneStepBestResponse namedStrategy clickThroughRate ∧
        ∀ strategy : Theorem8ContinuousSourceStrategy,
          strategy.ContinuousInValuation →
            Theorem8ContinuousSourceOneStepBestResponse
              strategy clickThroughRate →
              strategy.SupportEq namedStrategy boundary := by
  exact
    EOS07GSP.audit_theorem8_continuous_source_local_best_response_support_unique
      clickThroughRate boundary hclick_pos

/-- Theorem 8: full-history continuous local best responses agree with the
displayed formula on source support.
Source status: closes the source strategy-domain shape `p_i(k,h,s_i)` for the
local payoff theorem; the legal-history PBE endpoint below supplies the
arbitrary-continuation and Bayes-consistency layer. -/
abbrev theorem8_continuous_full_history_local_best_response_support_unique_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_history_local_best_response_support_unique

/-- Theorem 8: belief-explicit full-history strategy, arbitrary-continuation
ex-post optimality, and operational uniqueness.

Source status: legal-history ex-post PBE, the source-intended refinement.  The
continuous value law and full-history survival events induce an actual Bayes-
consistent conditional belief system.  Sequential rationality compares every
full history-dependent continuation plan for every realized ordered opponent
profile and therefore under every supported posterior.  Every other legal-
history ex-post PBE has the same clock-clamped dropout action at every feasible
history. -/
theorem theorem8_continuous_full_history_bayes_ex_post_review
    {Bidder : Type*} (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate
        (theorem8NamedContinuationPlan clickThroughRate) ∧
      ∀ plan : Theorem8ContinuationPlan,
        Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate plan →
          ∀ rank history ownValue,
            theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
              max (theorem8SourcePriceHistoryLastDropout history)
                  (plan rank history ownValue) =
                paper_theorem8_generalized_english_indifference_price
                  (clickThroughRate rank) (clickThroughRate (rank + 1))
                  (theorem8SourcePriceHistoryLastDropout history)
                  ownValue := by
  exact theorem8_legal_history_ex_post_pbe_exists_unique
    Bidder law clickThroughRate hclick_pos hclick_strict

/-- The literal displayed threshold is not a legal future clock price for all
types at all histories; below-clock thresholds must be read operationally as
immediate dropout. -/
abbrev theorem8_named_history_strategy_not_globally_clock_legal_review :=
  @EOS07GSP.PaperInterface.theorem8_named_history_strategy_not_globally_clock_legal

/-- Theorem 8: reduced continuous local PBE is unique on source support.
Source status: auxiliary payoff-local form; the compact source endpoint below
uses the source theorem's ex-post payoff-game semantics. -/
theorem theorem8_continuous_source_local_pbe_support_unique_review
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    let namedStrategy := theorem8ContinuousSourceStrategy clickThroughRate
    Theorem8ContinuousSourceLocalPBE clickThroughRate namedStrategy ∧
      ∀ strategy : Theorem8ContinuousSourceStrategy,
        Theorem8ContinuousSourceLocalPBE clickThroughRate strategy →
          strategy.SupportEq namedStrategy boundary := by
  exact
    EOS07GSP.audit_theorem8_continuous_source_local_pbe_support_unique
      clickThroughRate boundary hclick_pos

/-- Theorem 8: continuous generalized-English payoff-PBE is unique on nonnegative support.
Source status: ex-post payoff-level source game; PBE unfolds to the paper's
drop/continue payoff comparison plus continuity. -/
abbrev theorem8_continuous_generalized_english_payoff_game_support_unique_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_generalized_english_payoff_game_support_unique

/-- Theorem 8: source-event conclusion from strict ranked source values. -/
abbrev theorem8_price_sorted_finite_schedule_source_event_strict_values_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_boundary_threshold_event_ordered_displayed_conclusion

/-- Theorem 8: source-event conclusion with the paper's dropout-price formula.
Source status: finite strict-values source-event specialization of the
continuous dropout-price formula. -/
abbrev theorem8_source_event_strict_values_payment_formula :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_payment_formula

/-- Theorem 8: unique source-event PBE with dropout-price formula and VCG payoff.
Source status: finite strict-values source-event specialization with formula
and VCG conclusion. -/
abbrev theorem8_source_event_strict_values_unique_pbe_formula_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_unique_pbe_formula_conclusion

/-- Theorem 8: price-sorted finite source-event trace gives the full VCG state-game conclusion.
Source status: finite strict-values source-event specialization retaining the source-event trace, exact dropout history, unique PBE, VCG outcome equality, and rankwise slot/payment/utility equalities. -/
abbrev theorem8_source_event_strict_values_trace_full_vcg_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_threshold_event_trace_full_vcg_conclusion

/-- Theorem 8: continuous formula is profile-unique in the finite source checker.
Source status: auxiliary finite source-sequential specialization of the
continuous formula. -/
theorem theorem8_continuous_source_profile_unique_source_sequential_pbe
    (model : theorem8StrictOrderedValueCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
    let continuation :=
      fun k =>
        theorem7BStarBid localModel.value
          (fun j =>
            paper_theorem7_ranked_vcg_tail_payment
              localModel.value localModel.clickThroughRate j
              localModel.remaining)
          localModel.clickThroughRate (k + 2)
    let namedStrategy :=
      theorem8ContinuousSourceStrategy localModel.clickThroughRate
    namedStrategy.ContinuousInValuation ∧
      (sourceSequentialGame localModel initialState).PerfectBayesianEquilibrium
        (namedStrategy.inducedActionStrategy continuation localModel.value) ∧
      ∀ otherStrategy : Theorem8ContinuousSourceStrategy,
        (sourceSequentialGame localModel initialState).PerfectBayesianEquilibrium
          (otherStrategy.inducedActionStrategy continuation localModel.value) →
        otherStrategy.ProfileEq namedStrategy continuation localModel.value := by
  exact
    EOS07GSP.audit_theorem8_continuous_source_strategy_profile_unique_source_sequential_pbe_of_strict_values
      model initialState

/-- Theorem 8: source-event unique PBE stated via the induced continuous action rule.
Source status: finite source-event specialization of the continuous formula's
induced action rule. -/
abbrev theorem8_source_event_strict_values_unique_pbe_continuous_action_formula :=
  @EOS07GSP.audit_theorem8_price_sorted_finite_schedule_source_event_strict_values_unique_pbe_continuous_action_formula_conclusion

/-- Theorem 8: source-event PBE continuous strategies agree on the finite profile.
Source status: finite source-event profile uniqueness for continuous
dropout-price strategies. -/
abbrev theorem8_source_event_strict_values_continuous_profile_unique_source_extensive_pbe :=
  @EOS07GSP.audit_theorem8_price_sorted_finite_schedule_source_event_strict_values_continuous_profile_unique_source_extensive_pbe_conclusion

/-- Theorem 8: payoff-PBE continuous strategies give the finite VCG source-event outcome.
Source status: continuous payoff-PBE semantics with nonnegative support,
specialized to the strict finite source event and the paper's dropout formula. -/
abbrev theorem8_source_event_strict_values_payoff_pbe_nonnegative_support_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_payoff_pbe_nonnegative_support_conclusion

/-- Theorem 8: continuous payoff-game PBE gives the strict source-event VCG outcome.
Source status: top-down ex-post payoff-game statement linked to the finite
source-event VCG route. -/
abbrev theorem8_continuous_generalized_english_payoff_game_strict_values_source_event_conclusion_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_generalized_english_payoff_game_strict_values_source_event_conclusion

end ProofBridge
end EOS07GSP
