import EOS07GSP.PaperInterface

import EOS07GSP.ProofBridge



namespace EOS07GSP

namespace PaperInterface

open AppliedModelingLib.Auction
noncomputable section

theorem definition4_locally_envy_free
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) : definition4_locally_envy_freeSpec (Bidder := Bidder) (Slot := Slot) (E := E) (M := M) (values := values) (bids := bids) (allocatedPositions := allocatedPositions) (bidderAtRank := bidderAtRank) (slotAtRank := slotAtRank) := by
  exact EOS07GSP.ProofBridge.definition4_locally_envy_free (Bidder := Bidder) (Slot := Slot) (E := E) (M := M) (values := values) (bids := bids) (allocatedPositions := allocatedPositions) (bidderAtRank := bidderAtRank) (slotAtRank := slotAtRank)

/-- Project-approved correction of the printed Definition 4 boundary. -/
theorem corrected_definition4_locally_envy_free
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) : corrected_definition4_locally_envy_freeSpec (Bidder := Bidder) (Slot := Slot) (E := E) (M := M) (values := values) (bids := bids) (allocatedPositions := allocatedPositions) (bidderAtRank := bidderAtRank) (slotAtRank := slotAtRank) := by
  exact EOS07GSP.ProofBridge.corrected_definition4_locally_envy_free (Bidder := Bidder) (Slot := Slot) (E := E) (M := M) (values := values) (bids := bids) (allocatedPositions := allocatedPositions) (bidderAtRank := bidderAtRank) (slotAtRank := slotAtRank)

/-- Project-approved strict-surplus domain clarification for amended Lemma 6. -/
theorem corrected_lemma6_stable_assignment
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) :
    corrected_lemma6_stable_assignmentSpec
      (Bidder := Bidder) (Slot := Slot) (E := E) (O := O) (values := values) := by
  exact EOS07GSP.ProofBridge.corrected_lemma6_stable_assignment
    (Bidder := Bidder) (Slot := Slot) (E := E) (O := O) (values := values)

/-- Direct finite endpoint for the owner-approved strict-surplus Lemma 6
amendment. -/
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
    corrected_lemma6_ranked_one_extra_constructs_tiebreak_equilibriumSpec
      O hcorrected hslots hunassigned hpayment hunassigned_payment hclick_pos
      hclick_strict := by
  exact EOS07GSP.ProofBridge.corrected_lemma6_ranked_one_extra_constructs_tiebreak_equilibrium
    O hcorrected hslots hunassigned hpayment hunassigned_payment hclick_pos
    hclick_strict

/-- Direct full-`K>N` endpoint for the owner-approved strict-surplus Lemma 6
amendment. -/
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
    corrected_lemma6_ranked_more_bidders_constructs_tiebreak_equilibriumSpec
      hn hnm O hcorrected hslots hunassigned hpayment hclick_pos hclick_strict := by
  exact
    EOS07GSP.ProofBridge.corrected_lemma6_ranked_more_bidders_constructs_tiebreak_equilibrium
      hn hnm O hcorrected hslots hunassigned hpayment hclick_pos hclick_strict

/-- Direct amended-source Lemma 5 endpoint for `K = N + 1`. -/
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
    corrected_lemma5_ranked_one_extra_stableSpec bids hstrict hn hclick_pos
      hclick_strict hcorrected := by
  exact EOS07GSP.ProofBridge.corrected_lemma5_ranked_one_extra_stable
    bids hstrict hn hclick_pos hclick_strict hcorrected

/-- Direct corrected Lemma 5 endpoint for the full finite `K>N` source
domain.  Its separate bottom condition for every unassigned bidder is the
project-approved repair recorded in the validation report. -/
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
    corrected_lemma5_ranked_more_bidders_stableSpec
      hn hnm bids hstrict hclick_pos hclick_strict hcorrected := by
  exact EOS07GSP.ProofBridge.corrected_lemma5_ranked_more_bidders_stable
    hn hnm bids hstrict hclick_pos hclick_strict hcorrected

theorem stable_assignment
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) : stable_assignmentSpec (Bidder := Bidder) (Slot := Slot) (E := E) (O := O) (values := values) := by
  exact EOS07GSP.ProofBridge.stable_assignment (Bidder := Bidder) (Slot := Slot) (E := E) (O := O) (values := values)

theorem first_price_running_example_profitable_revision_chain : first_price_running_example_profitable_revision_chainSpec := by
  exact EOS07GSP.audit_first_price_running_example_profitable_revision_chain

theorem remark1_gsp_payments_weakly_dominate_vcg
    {value clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_mono : ∀ i, value (i + 1) ≤ value i)
    (hclick_nonneg : ∀ i, 0 ≤ clickThroughRate i)
    (rank remaining : ℕ) : remark1_gsp_payments_weakly_dominate_vcgSpec (value := value) (clickThroughRate := clickThroughRate) hvalue_nonneg hvalue_mono hclick_nonneg rank remaining := by
  exact EOS07GSP.ProofBridge.remark1_gsp_payments_weakly_dominate_vcg hvalue_nonneg hvalue_mono hclick_nonneg rank remaining

theorem remark2_vcg_truthful
    {Bidder Slot : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [Fintype Slot] [DecidableEq Slot]
    {E : PositionEnvironment Slot}
    (hclick_pos : ∀ s, 0 < E.clickThroughRate s) : remark2_vcg_truthfulSpec (Bidder := Bidder) (Slot := Slot) (E := E) (hclick_pos := hclick_pos) := by
  exact EOS07GSP.audit_remark2_finite_position_vcg_truthful (Bidder := Bidder) (Slot := Slot) (E := E) (hclick_pos := hclick_pos)

theorem remark3_gsp_not_truthful : remark3_gsp_not_truthfulSpec := by
  exact ⟨EOS07GSP.remark3_source_truthful_utility,
    EOS07GSP.remark3_source_shaded_utility,
    EOS07GSP.ProofBridge.remark3_gsp_not_truthful⟩

theorem running_example_truthful_gsp_nash : running_example_truthful_gsp_nashSpec := by
  exact EOS07GSP.audit_running_example_truthful_gsp_is_nash

theorem running_example_truthful_gsp_revenue_comparison : running_example_truthful_gsp_revenue_comparisonSpec := by
  refine ⟨by norm_num [EOS07GSP.paper_eos_running_example_value],
    by norm_num [EOS07GSP.paper_eos_running_example_value], ?_, ?_, ?_, ?_,
    EOS07GSP.audit_running_example_truthful_gsp_revenue_gt_vcg_revenue⟩
  · exact EOS07GSP.audit_running_example_truthful_gsp_total_payments.1
  · exact EOS07GSP.audit_running_example_truthful_gsp_total_payments.2
  · exact EOS07GSP.audit_running_example_vcg_total_payments.1
  · exact EOS07GSP.audit_running_example_vcg_total_payments.2

theorem lemma5_locally_envy_free_stable
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) : lemma5_locally_envy_free_stableSpec (Bidder := Bidder) (Slot := Slot) (E := E) (M := M) (values := values) (bids := bids) (hfeasible := hfeasible) (hIR := hIR) (h := h) := by
  exact EOS07GSP.ProofBridge.lemma5_locally_envy_free_stable (Bidder := Bidder) (Slot := Slot) (E := E) (M := M) (values := values) (bids := bids) (hfeasible := hfeasible) (hIR := hIR) (h := h)

theorem lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free
    {m n : ℕ} (hnm : n < m) {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n)) (bids : Fin m → ℝ)
    (hout : paper_ranked_gsp_tiebreak_mechanism m n bids = O)
    (hstrict : ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val)) : lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_freeSpec (m := m) (n := n) (hnm := hnm) (value := value) (clickThroughRate := clickThroughRate) (O := O) (bids := bids) (hout := hout) (hstrict := hstrict) (hclick_nonneg := hclick_nonneg) (hstable := hstable) := by
  exact EOS07GSP.ProofBridge.lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free (m := m) (n := n) (hnm := hnm) (value := value) (clickThroughRate := clickThroughRate) (O := O) (bids := bids) (hout := hout) (hstrict := hstrict) (hclick_nonneg := hclick_nonneg) (hstable := hstable)

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
      ∀ i : ℕ, vcgTotalPayment i < clickThroughRate i * value i) : theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcomeSpec (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_pos := hclick_pos) (hclick_strict_mono := hclick_strict_mono) (hrec := hrec) (hpayment_lt_value := hpayment_lt_value) := by
  exact EOS07GSP.ProofBridge.theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_pos := hclick_pos) (hclick_strict_mono := hclick_strict_mono) (hrec := hrec) (hpayment_lt_value := hpayment_lt_value)

theorem theorem7_bstar_payment_identity
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : ℕ)
    (hclick_ne : clickThroughRate i ≠ 0) : theorem7_bstar_payment_identitySpec (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (i := i) (hclick_ne := hclick_ne) := by
  exact EOS07GSP.ProofBridge.theorem7_bstar_payment_identity (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (i := i) (hclick_ne := hclick_ne)

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
            vcgTotalPayment (k + 1)) : theorem7_bstar_locally_envy_freeSpec (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_ne := hclick_ne) (hclick_mono := hclick_mono) (hvalue_mono := hvalue_mono) (hrec := hrec) := by
  exact EOS07GSP.ProofBridge.theorem7_bstar_locally_envy_free (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_ne := hclick_ne) (hclick_mono := hclick_mono) (hvalue_mono := hvalue_mono) (hrec := hrec)

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
    (hvalue_nonneg : ∀ i, 0 ≤ value i) : theorem7_no_positive_transfer_conclusionSpec (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_nonneg := hclick_nonneg) (hclick_pos := hclick_pos) (hclick_mono := hclick_mono) (hvalue_mono := hvalue_mono) (hvcg_rec := hvcg_rec) (hpayment_le_value := hpayment_le_value) (hvcg_tail_eq := hvcg_tail_eq) (hvalue_nonneg := hvalue_nonneg) := by
  exact EOS07GSP.ProofBridge.theorem7_no_positive_transfer_conclusion (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_nonneg := hclick_nonneg) (hclick_pos := hclick_pos) (hclick_mono := hclick_mono) (hvalue_mono := hvalue_mono) (hvcg_rec := hvcg_rec) (hpayment_le_value := hpayment_le_value) (hvcg_tail_eq := hvcg_tail_eq) (hvalue_nonneg := hvalue_nonneg)

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
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) : theorem7_strict_tiebreak_gsp_comparison_conclusionSpec (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_nonneg := hclick_nonneg) (hclick_pos := hclick_pos) (hclick_mono := hclick_mono) (hvalue_mono := hvalue_mono) (hvcg_rec := hvcg_rec) (hpayment_le_value := hpayment_le_value) (hvcg_tail_eq := hvcg_tail_eq) (hvalue_nonneg := hvalue_nonneg) (hvalue_strict := hvalue_strict) (hclick_strict := hclick_strict) := by
  exact EOS07GSP.ProofBridge.theorem7_strict_tiebreak_gsp_comparison_conclusion (n := n) (value := value) (vcgTotalPayment := vcgTotalPayment) (clickThroughRate := clickThroughRate) (hclick_nonneg := hclick_nonneg) (hclick_pos := hclick_pos) (hclick_mono := hclick_mono) (hvalue_mono := hvalue_mono) (hvcg_rec := hvcg_rec) (hpayment_le_value := hpayment_le_value) (hvcg_tail_eq := hvcg_tail_eq) (hvalue_nonneg := hvalue_nonneg) (hvalue_strict := hvalue_strict) (hclick_strict := hclick_strict)

theorem theorem7_finite_static_bstar_tiebreak_conclusion
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
    theorem7_finite_static_bstar_tiebreak_conclusionSpec model := by
  exact eos_finite_static_bstar_tiebreak_source_conclusion model

/-- Direct corrected finite seller-minimal-revenue endpoint for EOS Theorem
7.  This exposes the actual revenue inequality proved from the first-loser
terminal condition and backward stable-payment induction. -/
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
    theorem7_finite_static_bstar_revenue_minimal_correctedSpec
      hnm model bids hstrict hcorrected := by
  exact EOS07GSP.ProofBridge.theorem7_finite_static_bstar_revenue_minimal_corrected
    hnm model bids hstrict hcorrected

/-- Complete corrected finite Theorem 7 endpoint, joining the actual B-star
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
    theorem7_finite_static_bstar_full_correctedSpec
      hnm model bids hstrict hcorrected := by
  exact EOS07GSP.ProofBridge.theorem7_finite_static_bstar_full_corrected
    hnm model bids hstrict hcorrected

theorem theorem8_dropout_formula_eq_bstar_threshold
    (value clickThroughRate : ℕ → ℝ) (remaining rank : ℕ)
    (hclick_pos : ∀ i, 0 < clickThroughRate i) : theorem8_dropout_formula_eq_bstar_thresholdSpec (value := value) (clickThroughRate := clickThroughRate) (remaining := remaining) (rank := rank) (hclick_pos := hclick_pos) := by
  exact EOS07GSP.PaperInterface.theorem8_ranked_dropout_formula_eq_bstar_threshold (value := value) (clickThroughRate := clickThroughRate) (remaining := remaining) (rank := rank) (hclick_pos := hclick_pos)

theorem theorem8_q_step2_waiting_before_q_review
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hclock_lt :
      state.clockPrice <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank) : theorem8_q_step2_waiting_before_q_reviewSpec (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (state := state) (rank := rank) (hclick_pos := hclick_pos) (hclock_lt := hclock_lt) := by
  exact EOS07GSP.ProofBridge.theorem8_q_step2_waiting_before_q_review (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (state := state) (rank := rank) (hclick_pos := hclick_pos) (hclock_lt := hclock_lt)

theorem theorem8_q_step1_dropping_after_q_review
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hthreshold_lt :
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank <
        state.clockPrice) : theorem8_q_step1_dropping_after_q_reviewSpec (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (state := state) (rank := rank) (hclick_pos := hclick_pos) (hthreshold_lt := hthreshold_lt) := by
  exact EOS07GSP.ProofBridge.theorem8_q_step1_dropping_after_q_review (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (state := state) (rank := rank) (hclick_pos := hclick_pos) (hthreshold_lt := hthreshold_lt)

theorem theorem8_q_mem_interval_review
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_nonneg : 0 ≤ clickThroughRate (rank + 1))
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hlastDropout_le : lastDropout rank ≤ value (rank + 1)) : theorem8_q_mem_interval_reviewSpec (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (rank := rank) (hclick_pos := hclick_pos) (hcurrent_nonneg := hcurrent_nonneg) (hcurrent_le := hcurrent_le) (hlastDropout_le := hlastDropout_le) := by
  exact EOS07GSP.PaperInterface.theorem8_source_q_mem_interval (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (rank := rank) (hclick_pos := hclick_pos) (hcurrent_nonneg := hcurrent_nonneg) (hcurrent_le := hcurrent_le) (hlastDropout_le := hlastDropout_le)

theorem theorem8_q_strict_mem_interval_review
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_pos : 0 < clickThroughRate (rank + 1))
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hlastDropout_lt : lastDropout rank < value (rank + 1)) : theorem8_q_strict_mem_interval_reviewSpec (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (rank := rank) (hclick_pos := hclick_pos) (hcurrent_pos := hcurrent_pos) (hcurrent_lt := hcurrent_lt) (hlastDropout_lt := hlastDropout_lt) := by
  exact EOS07GSP.PaperInterface.theorem8_source_q_strict_mem_interval (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (rank := rank) (hclick_pos := hclick_pos) (hcurrent_pos := hcurrent_pos) (hcurrent_lt := hcurrent_lt) (hlastDropout_lt := hlastDropout_lt)

theorem theorem8_q_continuous_value_review
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) : theorem8_q_continuous_value_reviewSpec (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (rank := rank) := by
  exact EOS07GSP.ProofBridge.theorem8_q_continuous_value_review (clickThroughRate := clickThroughRate) (lastDropout := lastDropout) (value := value) (rank := rank)

theorem theorem8_continuous_source_local_best_response_support_unique_review
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    theorem8_continuous_source_local_best_response_support_unique_reviewSpec
      clickThroughRate boundary hclick_pos := by
  exact ProofBridge.theorem8_continuous_source_local_best_response_support_unique_review
    clickThroughRate boundary hclick_pos

theorem theorem8_strict_values_ex_post_local_deviation
    (model : theorem8StrictOrderedValueCertificate) : theorem8_strict_values_ex_post_local_deviationSpec (model := model) := by
  exact EOS07GSP.PaperInterface.theorem8_strict_values_named_strategy_ex_post_local_deviation (model := model)

theorem theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review
    (model : theorem8StrictOrderedValueCertificate) (n : ℕ) : theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_reviewSpec (model := model) (n := n) := by
  exact EOS07GSP.PaperInterface.theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion (model := model) (n := n)

theorem theorem8_finite_legal_history_pbe_terminal_vcg_ledger
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
    (defaultBidder : Bidder) :
    theorem8_finite_legal_history_pbe_terminal_vcg_ledgerSpec law
      clickThroughRate values htwo hvalue_nonneg hclick_pos hcurrent_nonneg
      hclick_strict hbottom_zero defaultBidder := by
  exact theorem8_named_finite_legal_history_pbe_terminal_vcg_ledger law
    clickThroughRate values htwo hvalue_nonneg hclick_pos hcurrent_nonneg
    hclick_strict hbottom_zero defaultBidder

end

end PaperInterface
end EOS07GSP
