import EOS07GSP.ProofBridge

namespace EOS07GSP

namespace PaperInterface

open AppliedModelingLib.Auction
noncomputable section

/-- Source-facing semantic target for `definition4_locally_envy_free`. -/
def definition4_locally_envy_freeSpec
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) : Prop :=
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
                (M bids).paymentPerClick (bidderAtRank (rank + 1)))

/--
Source-correction target for Definition 4.  It preserves the printed
allocated-rank condition and additionally rules out every unassigned bidder's
profitable rematch to the bottom allocated slot.  This is explicitly a
project-approved repair, not an archival-source equivalence claim.
-/
def corrected_definition4_locally_envy_freeSpec
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) : Prop :=
  correctedDefinition4LocallyEnvyFree E M values bids allocatedPositions
    bidderAtRank slotAtRank ↔
    sourceDefinition4LocallyEnvyFree E M values bids allocatedPositions
        bidderAtRank slotAtRank ∧
      ∀ bidder : Bidder, (M bids).slotOf bidder = none →
        ∀ rank : ℕ, rank + 1 = allocatedPositions →
          E.clickThroughRate (slotAtRank rank) *
              (values bidder -
                (M bids).paymentPerClick (bidderAtRank rank)) ≤ 0

/--
Corrected finite Lemma 5 target in the source's one-extra-bidder market. This
is an amended-source theorem: its scope is `K = N + 1`, and it retains strict
on-path bids to represent the source's no-equilibrium-tie argument.
-/
def corrected_lemma5_ranked_one_extra_stableSpec
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
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n) else ⟨0, hn⟩)) : Prop :=
  (paper_ranked_gsp_mechanism (n + 1) n bids).StableAssignment
    (paper_theorem7_ranked_environment clickThroughRate)
    (fun i : Fin (n + 1) => value i.val)

/--
Corrected Lemma 5 on the full finite source domain `K>N`.  Strict on-path
bids fix the ranked next-price outcome, while the corrected Definition 4
requires the bottom-slot comparison for every unassigned bidder rather than
assuming a value ordering within the lower tail.
-/
def corrected_lemma5_ranked_more_bidders_stableSpec
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
        (fun rank => if h : rank < n then (⟨rank, h⟩ : Fin n) else ⟨0, hn⟩)) : Prop :=
  (paper_ranked_gsp_mechanism m n bids).StableAssignment
    (paper_theorem7_ranked_environment clickThroughRate)
    (fun i : Fin m => value i.val)

/-- Source-facing assignment-game price convention. The source's `p_ik` is
the total payment for a matched advertiser-position pair, represented here as
click-through rate times `paymentPerClick`; the standard stability predicate is
used separately by Lemmas 5--6. -/
def stable_assignmentSpec
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) : Prop :=
  ∀ (i : Bidder) (s : Slot), O.slotOf i = some s →
    O.utility E values i =
      E.clickThroughRate s * values i -
        E.clickThroughRate s * O.paymentPerClick i

/--
Amended Lemma 6 domain.  It preserves the archival stable-assignment predicate
and additionally requires strictly positive utility for every bidder who is
assigned a slot.  Under the source's positive CTR convention, this is exactly
the nondegeneracy used to derive strict adjacent constructed bids.
-/
def corrected_lemma6_stable_assignmentSpec
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) : Prop :=
  correctedLemma6StableAssignment E values O ↔
    O.StableAssignment E values ∧
      ∀ (bidder : Bidder) (slot : Slot), O.slotOf bidder = some slot →
        0 < O.utility E values bidder

/--
Direct finite amended Lemma 6 target on the source's one-extra-bidder ranked
domain. The stable assignment is indexed by its efficient ranks, uses the
source's per-click price normalization, and records zero payment for the sole
unassigned bidder. The conclusion is the Appendix bid construction's exact
tie-broken GSP realization and locally envy-free equilibrium.
-/
def corrected_lemma6_ranked_one_extra_constructs_tiebreak_equilibriumSpec
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
    Prop :=
  let bids := lemma6ConstructedBids (n := n) value payment clickThroughRate
  paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids = O ∧
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n).LocallyEnvyFreeEquilibrium
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin (n + 1) => value i.val) bids

/-- Direct amended Lemma 6 target on the full source `K>N` domain.  The
comparison deliberately preserves every bidder's assignment but compares
payments only for assigned bidders: GSP's tail reports create irrelevant
next-bid records for unassigned bidders, whereas the source outcome specifies
payments only for allocated bidders. -/
def corrected_lemma6_ranked_more_bidders_constructs_tiebreak_equilibriumSpec
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
    Prop :=
  let bids := lemma6ConstructedBidsMoreBidders (m := m) (n := n)
    value payment clickThroughRate
  lemma6AssignedOutcomeEq
      (paper_ranked_gsp_tiebreak_mechanism m n bids) O ∧
    (paper_ranked_gsp_tiebreak_mechanism m n).LocallyEnvyFreeEquilibrium
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin m => value i.val) bids

/-- Source-facing semantic target for `first_price_running_example_profitable_revision_chain`. -/
def first_price_running_example_profitable_revision_chainSpec : Prop :=
  (200 * (10 - (203 / 100 : ℝ)) <
    200 * (10 - (202 / 100 : ℝ))) ∧
  (100 * (4 - (201 / 100 : ℝ)) <
    200 * (4 - (203 / 100 : ℝ))) ∧
  (100 * (10 - (202 / 100 : ℝ)) <
    200 * (10 - (204 / 100 : ℝ)))

/-- Source-facing semantic target for `remark1_gsp_payments_weakly_dominate_vcg`. -/
def remark1_gsp_payments_weakly_dominate_vcgSpec
    {value clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_mono : ∀ i, value (i + 1) ≤ value i)
    (hclick_nonneg : ∀ i, 0 ≤ clickThroughRate i)
    (rank remaining : ℕ) : Prop :=
  paper_theorem7_ranked_vcg_tail_payment
      value clickThroughRate rank remaining ≤
    clickThroughRate rank * value (rank + 1)

/-- Source-facing semantic target for `remark2_vcg_truthful`. -/
def remark2_vcg_truthfulSpec
    {Bidder Slot : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [Fintype Slot] [DecidableEq Slot]
    {E : PositionEnvironment Slot}
    (hclick_pos : ∀ s, 0 < E.clickThroughRate s) : Prop :=
  PositionMechanism.TruthfulDominantStrategy E
    (PositionMechanism.positionVCGMechanism
      (Bidder := Bidder) (Slot := Slot) E)

/-- Source-facing semantic target for `remark3_gsp_not_truthful`. -/
def remark3_gsp_not_truthfulSpec : Prop :=
  PositionMechanism.utility remark3SourceEnvironment gsp3TwoSlotMechanism
      remark3SourceValues remark3SourceValues (0 : Fin 3) = 1200 ∧
    PositionMechanism.utility remark3SourceEnvironment gsp3TwoSlotMechanism
      remark3SourceValues remark3SourceShadedBids (0 : Fin 3) = 1592 ∧
      ¬ PositionMechanism.TruthfulDominantStrategy
        remark3SourceEnvironment gsp3TwoSlotMechanism

/-- Source-facing semantic target for `running_example_truthful_gsp_nash`. -/
def running_example_truthful_gsp_nashSpec : Prop :=
  PositionMechanism.IsNashEquilibrium
    paper_eos_running_example_environment
    gsp3TwoSlotMechanism
    paper_eos_running_example_values3
    paper_eos_running_example_values3

/-- Source-facing semantic target for `running_example_truthful_gsp_revenue_comparison`. -/
def running_example_truthful_gsp_revenue_comparisonSpec : Prop :=
  -- The paper first gives the two GSP per-click prices ($4 and $2), then
  -- the corresponding total payments ($800 and $200), before computing the
  -- two VCG total payments ($600 and $200) and comparing revenue.
  paper_eos_running_example_value 1 = 4 ∧
    paper_eos_running_example_value 2 = 2 ∧
    paper_eos_running_example_clickThroughRate 0 *
        paper_eos_running_example_value 1 = 800 ∧
      paper_eos_running_example_clickThroughRate 1 *
        paper_eos_running_example_value 2 = 200 ∧
      paper_theorem7_ranked_vcg_tail_payment
          paper_eos_running_example_value
          paper_eos_running_example_clickThroughRate 0 2 = 600 ∧
        paper_theorem7_ranked_vcg_tail_payment
          paper_eos_running_example_value
          paper_eos_running_example_clickThroughRate 1 1 = 200 ∧
    paper_eos_running_example_clickThroughRate 0 *
        paper_eos_running_example_value 1 +
      paper_eos_running_example_clickThroughRate 1 *
        paper_eos_running_example_value 2 >
    paper_theorem7_ranked_vcg_tail_payment
        paper_eos_running_example_value
        paper_eos_running_example_clickThroughRate 0 2 +
      paper_theorem7_ranked_vcg_tail_payment
        paper_eos_running_example_value
        paper_eos_running_example_clickThroughRate 1 1

/-- Source-facing semantic target for `lemma5_locally_envy_free_stable`. -/
def lemma5_locally_envy_free_stableSpec
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) : Prop :=
  (M bids).StableAssignment E values

/-- Source-facing semantic target for `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free`. -/
def lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_freeSpec
    {m n : ℕ} (hnm : n < m) {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n)) (bids : Fin m → ℝ)
    (hout : paper_ranked_gsp_tiebreak_mechanism m n bids = O)
    (hstrict : ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val)) : Prop :=
  (paper_ranked_gsp_tiebreak_mechanism m n).LocallyEnvyFreeEquilibrium
    (paper_theorem7_ranked_environment clickThroughRate)
    (fun i : Fin m => value i.val) bids

/-- Source-facing semantic target for `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome`. -/
def theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcomeSpec
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_pos : ∀ i, 0 < clickThroughRate i)
    (hclick_strict_mono : ∀ i, clickThroughRate (i + 1) < clickThroughRate i)
    (hrec :
      ∀ i : ℕ,
        vcgTotalPayment i =
          (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
            vcgTotalPayment (i + 1))
    (hpayment_lt_value :
      ∀ i : ℕ, vcgTotalPayment i < clickThroughRate i * value i) : Prop :=
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
          value vcgTotalPayment clickThroughRate).paymentPerClick i

/-- Source-facing semantic target for `theorem7_bstar_payment_identity`. -/
def theorem7_bstar_payment_identitySpec
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : ℕ)
    (hclick_ne : clickThroughRate i ≠ 0) : Prop :=
  clickThroughRate i *
    paper_theorem7_bstar_bid value vcgTotalPayment clickThroughRate (i + 1) =
    vcgTotalPayment i

/-- Source-facing semantic target for `theorem7_bstar_locally_envy_free`. -/
def theorem7_bstar_locally_envy_freeSpec
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1)) : Prop :=
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
            (fun i : Fin n => value i.val) i

/-- Source-facing semantic target for `theorem7_no_positive_transfer_conclusion`. -/
def theorem7_no_positive_transfer_conclusionSpec
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
    (hvalue_nonneg : ∀ i, 0 ≤ value i) : Prop :=
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
          other.revenue (paper_theorem7_ranked_environment clickThroughRate)

/-- Source-facing semantic target for `theorem7_strict_tiebreak_gsp_comparison_conclusion`. -/
def theorem7_strict_tiebreak_gsp_comparison_conclusionSpec
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
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) : Prop :=
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
              (paper_theorem7_ranked_environment clickThroughRate)

/--
Source-facing finite one-extra-bidder endpoint for EOS Theorem 7.  The
formalized source market has `n` displayed positions and one next bidder.  Its
bounded VCG and CTR conditions live in `EOSFiniteStaticBStarOrder`; the
conclusion proves the actual B-star GSP profile is locally envy-free and has
the ranked VCG allocation and total payments.
-/
def theorem7_finite_static_bstar_tiebreak_conclusionSpec
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) : Prop :=
  (paper_ranked_gsp_tiebreak_mechanism (n + 1) n).LocallyEnvyFreeEquilibrium
      (paper_theorem7_ranked_environment model.clickThroughRate)
      (fun i : Fin (n + 1) => model.value i.val)
      (eosFiniteStaticBStarBids model) ∧
    (∀ i : Fin n,
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model)).slotOf i.castSucc = some i) ∧
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
      (eosFiniteStaticBStarBids model)).slotOf (Fin.last n) = none ∧
    ∀ i : Fin n,
      model.clickThroughRate i.val *
        (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
          (eosFiniteStaticBStarBids model)).paymentPerClick i.castSucc =
        model.vcgTotalPayment i.val

/-- Corrected finite source-facing seller comparison for EOS Theorem 7.  The
comparison profile is ordinary sorted GSP with a strict on-path bid order,
which makes the ranked source ledger unambiguous.  Its corrected Definition 4
premise includes the separately disclosed bottom-slot condition for every
unassigned bidder. -/
def theorem7_finite_static_bstar_revenue_minimal_correctedSpec
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
          else ⟨0, model.slots_nonempty⟩)) : Prop :=
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
      (eosFiniteStaticBStarBids model)).revenue
        (paper_theorem7_ranked_environment model.clickThroughRate) ≤
      (paper_ranked_gsp_mechanism m n bids).revenue
        (paper_theorem7_ranked_environment model.clickThroughRate)

/-- Complete corrected finite Theorem 7 endpoint: the B-star profile is a
locally-envy-free GSP equilibrium with the VCG position/payment ledger, and
its actual seller revenue is no greater than that of every comparison profile
in the corrected strict ranked-GSP class. -/
def theorem7_finite_static_bstar_full_correctedSpec
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
          else ⟨0, model.slots_nonempty⟩)) : Prop :=
    theorem7_finite_static_bstar_tiebreak_conclusionSpec model ∧
      theorem7_finite_static_bstar_revenue_minimal_correctedSpec
        hnm model bids hstrict hcorrected

/-- Source-facing semantic target for `theorem8_dropout_formula_eq_bstar_threshold`. -/
def theorem8_dropout_formula_eq_bstar_thresholdSpec
    (value clickThroughRate : ℕ → ℝ) (remaining rank : ℕ)
    (hclick_pos : ∀ i, 0 < clickThroughRate i) : Prop :=
  theorem8RankedGeneralizedEnglishDropoutPrice
      clickThroughRate
      (fun k =>
        theorem7BStarBid value
          (fun j =>
            paper_theorem7_ranked_vcg_tail_payment
              value clickThroughRate j remaining)
          clickThroughRate (k + 2))
      value rank =
    theorem8BStarThresholdBid value clickThroughRate (remaining + 1)
      (rank + 1)

/-- Source-facing semantic target for `theorem8_q_step2_waiting_before_q_review`. -/
def theorem8_q_step2_waiting_before_q_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hclock_lt :
      state.clockPrice <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank) : Prop :=
  clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) <
    clickThroughRate rank * (value (rank + 1) - state.clockPrice)

/-- Source-facing semantic target for `theorem8_q_step1_dropping_after_q_review`. -/
def theorem8_q_step1_dropping_after_q_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hthreshold_lt :
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank <
        state.clockPrice) : Prop :=
  clickThroughRate rank * (value (rank + 1) - state.clockPrice) <
    clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank)

/-- Source-facing semantic target for `theorem8_q_mem_interval_review`. -/
def theorem8_q_mem_interval_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_nonneg : 0 ≤ clickThroughRate (rank + 1))
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hlastDropout_le : lastDropout rank ≤ value (rank + 1)) : Prop :=
  lastDropout rank ≤
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ∧
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ≤ value (rank + 1)

/-- Source-facing semantic target for `theorem8_q_strict_mem_interval_review`. -/
def theorem8_q_strict_mem_interval_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_pos : 0 < clickThroughRate (rank + 1))
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hlastDropout_lt : lastDropout rank < value (rank + 1)) : Prop :=
  lastDropout rank <
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ∧
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank < value (rank + 1)

/-- Source-facing semantic target for `theorem8_q_continuous_value_review`. -/
def theorem8_q_continuous_value_reviewSpec
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) : Prop :=
  Continuous
    (fun bidderValue : ℝ =>
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout
        (Function.update value (rank + 1) bidderValue)
        rank)

def theorem8_continuous_source_local_best_response_support_unique_reviewSpec
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) : Prop :=
  let namedStrategy := theorem8ContinuousSourceStrategy clickThroughRate
  namedStrategy.ContinuousInValuation ∧
    Theorem8ContinuousSourceOneStepBestResponse namedStrategy clickThroughRate ∧
      ∀ strategy : Theorem8ContinuousSourceStrategy,
        strategy.ContinuousInValuation →
          Theorem8ContinuousSourceOneStepBestResponse
            strategy clickThroughRate →
            strategy.SupportEq namedStrategy boundary

/-- Source-facing semantic target for `theorem8_strict_values_ex_post_local_deviation`. -/
def theorem8_strict_values_ex_post_local_deviationSpec
    (model : theorem8StrictOrderedValueCertificate) : Prop :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
  paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
    localModel.clickThroughRate localModel.value localModel.remaining
    (paper_theorem8_bstar_ranked_threshold_strategy
      localModel.value localModel.clickThroughRate localModel.remaining)

/-- Source-facing semantic target for `theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review`. -/
def theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_reviewSpec
    (model : theorem8StrictOrderedValueCertificate) (n : ℕ) : Prop :=
  let game :=
    Theorem8ContinuousGeneralizedEnglishPayoffGame.ofStrictValues model
  let scheduledRanks :=
    paper_theorem8_bstar_ranked_threshold_price_sorted_fin_schedule
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model) n
  let rankSchedule :=
    paper_theorem8_bstar_ranked_threshold_fin_schedule_ranks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
      localModel initialState finalState
  let continuation :=
    fun k =>
      theorem7BStarBid localModel.value
        (fun j =>
          paper_theorem7_ranked_vcg_tail_payment
            localModel.value localModel.clickThroughRate j
            localModel.remaining)
        localModel.clickThroughRate (k + 2)
  let namedContinuousStrategy :=
    theorem8ContinuousSourceStrategy localModel.clickThroughRate
  game.PerfectBayesianEquilibrium namedContinuousStrategy ∧
    (∀ strategy : Theorem8ContinuousSourceStrategy,
      game.PerfectBayesianEquilibrium strategy →
        strategy.SupportEq namedContinuousStrategy
          Theorem8ContinuousGeneralizedEnglishPayoffGame.nonnegativeSupport) ∧
      ∀ strategy : Theorem8ContinuousSourceStrategy,
        game.PerfectBayesianEquilibrium strategy →
          G.PerfectBayesianEquilibrium
              (strategy.inducedActionStrategy continuation localModel.value) ∧
            G.outcomeOf
                (strategy.inducedActionStrategy continuation localModel.value) =
              G.vcgOutcome ∧
              strategy.ProfileEq
                namedContinuousStrategy continuation localModel.value

/-- Owner-approved corrected finite Theorem 8 endpoint. It retains the
paper's finite `K = N + 1` market, zero CTR below the final advertised slot,
full histories, bidder-indexed beliefs, ex-post PBE, observable-action
uniqueness, and the terminal GSP-to-VCG ledger. Its continuation-plan binder is
explicitly symmetric across bidder identities, so it does not assert the
archival theorem's uniqueness over arbitrary bidder-indexed profiles. -/
def theorem8_finite_legal_history_pbe_terminal_vcg_ledgerSpec
    {Bidder : Type*} [Fintype Bidder] [DecidableEq Bidder] [Nonempty Bidder]
    (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ) (values : Bidder → ℝ)
    (htwo : 1 < Fintype.card Bidder)
    (hvalue_nonneg : ∀ bidder, 0 ≤ values bidder)
    (hclick_pos : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 < clickThroughRate rank)
    (hcurrent_nonneg : ∀ rank, rank < Fintype.card Bidder - 1 →
      0 ≤ clickThroughRate (rank + 1))
    (hclick_strict : ∀ rank, rank < Fintype.card Bidder - 1 →
      clickThroughRate (rank + 1) < clickThroughRate rank)
    (hbottom_zero : clickThroughRate (Fintype.card Bidder - 1) = 0)
    (defaultBidder : Bidder) : Prop :=
  let plan := theorem8NamedContinuationPlan clickThroughRate
  let strategy := theorem8ContinuousHistoryStrategy Bidder clickThroughRate
  let finalState := theorem8StoppedSourceFinalState strategy values
  let initialState := theorem8StoppedSourceInitialState Bidder
  let hremaining : initialState.remaining.Nonempty := Finset.univ_nonempty
  let rankedValue := theorem8StoppedSourceTerminalRankedValue strategy values
    initialState hremaining defaultBidder
  Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate
      (Fintype.card Bidder - 1) plan ∧
    (∀ otherPlan : Theorem8ContinuationPlan,
      Theorem8FiniteLegalHistoryExPostPBE Bidder law clickThroughRate
        (Fintype.card Bidder - 1) otherPlan →
        ∀ rank history ownValue,
          rank < Fintype.card Bidder - 1 →
          theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
            max (theorem8SourcePriceHistoryLastDropout history)
                (otherPlan rank history ownValue) =
              paper_theorem8_generalized_english_indifference_price
                (clickThroughRate rank) (clickThroughRate (rank + 1))
                (theorem8SourcePriceHistoryLastDropout history)
                ownValue) ∧
    plan.historyStrategy Bidder = strategy ∧
    (theorem8StoppedSourceFinalRankedBidders strategy values).toFinset =
      Finset.univ ∧
    (theorem8StoppedSourceFinalRankedBidders strategy values).Pairwise
      (fun earlier later => values later ≤ values earlier) ∧
    (∀ bidder, bidder ∈ finalState.remaining →
      finalState.terminalGSPOutcome.slotOf bidder = some 0 ∧
        finalState.terminalGSPOutcome.paymentPerClick bidder =
          finalState.history.getD 0 0) ∧
    (∀ bidder, bidder ∉ finalState.remaining →
      bidder ∈ finalState.dropped.dropLast →
        finalState.terminalGSPOutcome.slotOf bidder =
            some (finalState.dropped.idxOf bidder + 1) ∧
          finalState.terminalGSPOutcome.paymentPerClick bidder =
            finalState.history.getD (finalState.dropped.idxOf bidder + 1) 0) ∧
    (∀ bidder, bidder ∉ finalState.remaining →
      bidder ∉ finalState.dropped.dropLast →
        finalState.terminalGSPOutcome.slotOf bidder = none) ∧
    ∀ index, index < finalState.history.length →
      clickThroughRate index * finalState.history.getD index 0 =
        paper_theorem7_ranked_vcg_tail_payment rankedValue clickThroughRate
          index (finalState.dropped.length - index)

end

end PaperInterface
end EOS07GSP
