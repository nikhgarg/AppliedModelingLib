import EOS07GSP.AuctionMainTheorems

/-!
# Finite static GSP bridge for EOS

This file records the finite source-facing part of the Section 4 `B*`
construction.  The paper has finitely many displayed positions and uses the
next (unassigned) bidder to price the last position.  Earlier review routes
quantified over an artificial all-natural-rank continuation in order to obtain
strict bid order.  Here the required bid order is derived only over the
advertised finite ranks.
-/

namespace EOS07GSP

open AppliedModelingLib.Auction

noncomputable section

/--
Finite source data needed to establish that the paper's `B*` bids are strictly
ordered.  There are `n` displayed positions and one next bidder.  The fields
are deliberately bounded by `n`; no conditions are imposed on fictitious
positions after the displayed market.
-/
structure EOSFiniteStaticBStarOrder (n : ℕ) where
  value : ℕ → ℝ
  vcgTotalPayment : ℕ → ℝ
  clickThroughRate : ℕ → ℝ
  slots_nonempty : 0 < n
  click_pos : ∀ k : ℕ, k < n → 0 < clickThroughRate k
  click_strict : ∀ k : ℕ, k + 1 < n →
    clickThroughRate (k + 1) < clickThroughRate k
  vcg_rec : ∀ k : ℕ, k + 1 < n →
    vcgTotalPayment k =
      (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
        vcgTotalPayment (k + 1)
  payment_lt_value : ∀ k : ℕ, k < n →
    vcgTotalPayment k < clickThroughRate k * value k
  payment_le_value : ∀ k : ℕ, k < n →
    vcgTotalPayment k ≤ clickThroughRate k * value k
  value_mono : ∀ a b : ℕ, a ≤ b → b ≤ n → value b ≤ value a
  terminal_payment : ∀ k : ℕ, k + 1 = n →
    vcgTotalPayment k = clickThroughRate k * value n

/-- The paper's finite `B*` profile: rank zero bids its value and every later
rank bids the previous rank's VCG payment per click. -/
noncomputable def eosFiniteStaticBStarBids
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) : Fin (n + 1) → ℝ :=
  fun bidder =>
    paper_theorem7_bstar_bid model.value model.vcgTotalPayment
      model.clickThroughRate bidder.val

/-- Adjacent bids in the finite `B*` profile are strictly decreasing. -/
theorem eos_finite_static_bstar_adjacent_strict
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n)
    (k : ℕ) (hk : k + 1 < n + 1) :
    eosFiniteStaticBStarBids model ⟨k + 1, hk⟩ <
      eosFiniteStaticBStarBids model ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  have hk_lt_n : k < n := by omega
  cases k with
  | zero =>
      simpa [eosFiniteStaticBStarBids] using
        paper_theorem7_bstar_top_bid_gt_next
          (model.click_pos 0 model.slots_nonempty)
          (model.payment_lt_value 0 model.slots_nonempty)
  | succ k =>
      have hk_succ_lt_n : k + 1 < n := by omega
      simpa [eosFiniteStaticBStarBids, Nat.succ_eq_add_one, Nat.add_assoc] using
        paper_theorem7_bstar_adjacent_bid_gt_next
          (model.click_pos k (by omega))
          (model.click_pos (k + 1) hk_succ_lt_n)
          (model.click_strict k hk_succ_lt_n)
          (model.vcg_rec k hk_succ_lt_n)
          (model.payment_lt_value (k + 1) hk_succ_lt_n)

/-- The finite source conditions yield a globally strict ordering over the
actual `n + 1` bidders. -/
theorem eos_finite_static_bstar_strict
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n)
    {i j : Fin (n + 1)} (hij : i.val < j.val) :
    eosFiniteStaticBStarBids model j < eosFiniteStaticBStarBids model i := by
  exact paper_ranked_gsp_strict_decreasing_of_adjacent
    (eos_finite_static_bstar_adjacent_strict model) hij

/--
The finite B-star GSP profile realizes the source allocation and next-price
payment rule: displayed rank `i` is held by bidder `i`, the next bidder is
unassigned, and rank `i` pays the next B-star bid.  This is the direct finite
replacement for the prior all-natural-rank realization hypothesis.
-/
theorem eos_finite_static_bstar_gsp_realization
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
    (∀ i : Fin n,
        (paper_ranked_gsp_mechanism (n + 1) n
          (eosFiniteStaticBStarBids model)).slotOf i.castSucc = some i) ∧
      (paper_ranked_gsp_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model)).slotOf (Fin.last n) = none ∧
      ∀ i : Fin n,
        (paper_ranked_gsp_mechanism (n + 1) n
          (eosFiniteStaticBStarBids model)).paymentPerClick i.castSucc =
          paper_theorem7_bstar_bid model.value model.vcgTotalPayment
            model.clickThroughRate (i.val + 1) := by
  rcases paper_ranked_gsp_mechanism_realizes_next_price_of_strict_decreasing
      (bids := eosFiniteStaticBStarBids model)
      (fun {i j} hij => eos_finite_static_bstar_strict model hij) with
    ⟨hslots, hunassigned, hpayments⟩
  refine ⟨hslots, hunassigned, ?_⟩
  intro i
  simpa [eosFiniteStaticBStarBids] using hpayments i

/-- The same finite source ledger for the deterministic tie-broken GSP
implementation used for off-path deviations.  Strict B-star order makes the
tie rule immaterial on the equilibrium path. -/
theorem eos_finite_static_bstar_tiebreak_gsp_realization
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
    (∀ i : Fin n,
        (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
          (eosFiniteStaticBStarBids model)).slotOf i.castSucc = some i) ∧
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model)).slotOf (Fin.last n) = none ∧
      ∀ i : Fin n,
        (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
          (eosFiniteStaticBStarBids model)).paymentPerClick i.castSucc =
          paper_theorem7_bstar_bid model.value model.vcgTotalPayment
            model.clickThroughRate (i.val + 1) := by
  rcases
      paper_ranked_gsp_tiebreak_mechanism_realizes_next_price_of_strict_decreasing
        (bids := eosFiniteStaticBStarBids model)
        (fun {i j} hij => eos_finite_static_bstar_strict model hij) with
    ⟨hslots, hunassigned, hpayments⟩
  refine ⟨hslots, hunassigned, ?_⟩
  intro i
  simpa [eosFiniteStaticBStarBids] using hpayments i

/--
With more bidders than slots, any Nash profile of the deterministic tie-broken
GSP has individually rational realized utilities: a bidder can submit a report
strictly below every other bid and thereby obtain no slot and utility zero.
This discharges the individual-rationality premise that the prior generic
Lemma 5 route exposed as an unexplained assumption.
-/
theorem eos_one_extra_tiebreak_gsp_individually_rational_of_nash
    {n : ℕ} {value clickThroughRate : ℕ → ℝ} {bids : Fin (n + 1) → ℝ}
    (hnash :
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n).IsNashEquilibrium
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin (n + 1) => value i.val) bids) :
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids).IndividuallyRational
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin (n + 1) => value i.val) := by
  intro i
  rcases paper_ranked_gsp_tiebreak_exists_strictly_low_report bids i with
    ⟨report, hreport_low⟩
  have hbelow : ∀ j : Fin (n + 1), j ≠ i → report < bids j := by
    intro j _
    exact hreport_low j
  have hrank :
      paper_ranked_gsp_tiebreak_rank (Function.update bids i report) i = n := by
    simpa using
      paper_ranked_gsp_tiebreak_rank_eq_last_of_strictly_low_report
        (bids := bids) (i := i) (report := report) hbelow
  have hslot :
      (paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (Function.update bids i report)).slotOf i = none := by
    simp [paper_ranked_gsp_tiebreak_mechanism, hrank]
  have hzero :
      PositionMechanism.utility
          (paper_theorem7_ranked_environment clickThroughRate)
          (paper_ranked_gsp_tiebreak_mechanism (n + 1) n)
          (fun i : Fin (n + 1) => value i.val)
          (Function.update bids i report) i = 0 := by
    simp [PositionMechanism.utility, PositionOutcome.utility, hslot]
  rw [← hzero]
  exact hnash i report

/--
The finite source B-star profile induces a stable assignment in the one-extra
bidder market.  This is the static algebra beneath the source's B-star
equilibrium construction: all terms are bounded by the advertised market and
the terminal VCG payment is the next bidder's value times the last CTR.
-/
theorem eos_finite_static_bstar_tiebreak_outcome_stable
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
    let bids := eosFiniteStaticBStarBids model
    let O := paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids
    O.StableAssignment
      (paper_theorem7_ranked_environment model.clickThroughRate)
      (fun i : Fin (n + 1) => model.value i.val) := by
  dsimp
  let bids := eosFiniteStaticBStarBids model
  let O := paper_ranked_gsp_tiebreak_mechanism (n + 1) n bids
  rcases eos_finite_static_bstar_tiebreak_gsp_realization model with
    ⟨hslots, hunassigned, hpayments⟩
  have hfeasible : O.FeasibleAssignment := by
    simpa [O] using
      paper_ranked_gsp_tiebreak_mechanism_feasible (n + 1) n bids
  have hpayment : ∀ i : Fin n,
      O.paymentPerClick i.castSucc =
        model.vcgTotalPayment i.val / model.clickThroughRate i.val := by
    intro i
    simpa [O, bids, eosFiniteStaticBStarBids, paper_theorem7_bstar_bid] using
      hpayments i
  have hIR : O.IndividuallyRational
      (paper_theorem7_ranked_environment model.clickThroughRate)
      (fun i : Fin (n + 1) => model.value i.val) := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨winner, hi⟩ | hi
    · subst i
      have hpos := model.click_pos winner.val winner.isLt
      have hpay_le := model.payment_le_value winner.val winner.isLt
      have hper_click :
          model.vcgTotalPayment winner.val / model.clickThroughRate winner.val ≤
            model.value winner.val :=
        (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hpay_le)
      have hnonneg :
          0 ≤ model.clickThroughRate winner.val *
            (model.value winner.val -
              model.vcgTotalPayment winner.val /
                model.clickThroughRate winner.val) :=
        mul_nonneg (le_of_lt hpos) (sub_nonneg.mpr hper_click)
      have hslot : O.slotOf winner.castSucc = some winner := by
        simpa [O, bids] using hslots winner
      have hpay : O.paymentPerClick winner.castSucc =
          model.vcgTotalPayment winner.val /
            model.clickThroughRate winner.val := hpayment winner
      simpa [PositionOutcome.utility, paper_theorem7_ranked_environment,
        hslot, hpay] using hnonneg
    · subst i
      have hslot : O.slotOf (Fin.last n) = none := by
        simpa [O, bids] using hunassigned
      simp [PositionOutcome.utility, hslot]
  let payment : ℕ → ℝ := fun k =>
    model.vcgTotalPayment k / model.clickThroughRate k
  have hpayment_eq : ∀ i : Fin n, O.paymentPerClick i.castSucc = payment i.val := by
    intro i
    exact hpayment i
  have hup : ∀ k : ℕ, k + 1 < n →
      model.clickThroughRate k * (model.value (k + 1) - payment k) ≤
        model.clickThroughRate (k + 1) *
          (model.value (k + 1) - payment (k + 1)) := by
    intro k hk
    have hkpos := model.click_pos k (by omega)
    have hk1pos := model.click_pos (k + 1) hk
    have hrec := model.vcg_rec k hk
    dsimp [payment]
    rw [hrec]
    field_simp [ne_of_gt hkpos, ne_of_gt hk1pos] <;> nlinarith
  have hdown : ∀ k : ℕ, k + 1 < n →
      model.clickThroughRate (k + 1) *
          (model.value k - payment (k + 1)) ≤
        model.clickThroughRate k * (model.value k - payment k) := by
    intro k hk
    have hkpos := model.click_pos k (by omega)
    have hk1pos := model.click_pos (k + 1) hk
    have hraw :=
      paper_theorem7_ranked_vcg_adjacent_no_envy_lower_of_value_ge
        (le_of_lt (model.click_strict k hk))
        (model.value_mono k (k + 1) (Nat.le_succ k) (by omega))
        (model.vcg_rec k hk)
    dsimp [payment]
    calc
      model.clickThroughRate (k + 1) *
          (model.value k -
            model.vcgTotalPayment (k + 1) /
              model.clickThroughRate (k + 1)) =
          model.clickThroughRate (k + 1) * model.value k -
            model.vcgTotalPayment (k + 1) := by
              field_simp [ne_of_gt hk1pos]
      _ ≤ model.clickThroughRate k * model.value k -
            model.vcgTotalPayment k := hraw
      _ = model.clickThroughRate k *
          (model.value k -
            model.vcgTotalPayment k / model.clickThroughRate k) := by
              field_simp [ne_of_gt hkpos]
  refine
    paper_ranked_one_extra_bidder_stable_assignment_of_bounded_adjacent_rank_no_envy
      O hfeasible hIR hslots hunassigned hpayment_eq model.click_strict hup hdown
      ?_ ?_ ?_
  · intro k hk
    exact model.click_pos k (by omega)
  · intro k hk
    have hkpos := model.click_pos k (by omega)
    have hper_click :
        model.vcgTotalPayment k / model.clickThroughRate k ≤ model.value k :=
      (div_le_iff₀ hkpos).mpr (by
        simpa [mul_comm] using model.payment_le_value k (by omega))
    exact mul_nonneg (le_of_lt hkpos) (sub_nonneg.mpr hper_click)
  · intro k hk
    have hkpos := model.click_pos k (by omega)
    dsimp [payment]
    rw [model.terminal_payment k hk]
    field_simp [ne_of_gt hkpos] <;> norm_num

/--
The constructed finite B-star GSP profile is a locally envy-free equilibrium.
The proof first establishes its stable assignment directly from the finite VCG
recursion, then applies the concrete GSP deviation theorem; it does not take a
Nash, outcome-realization, or equilibrium certificate as a premise.
-/
theorem eos_finite_static_bstar_tiebreak_locally_envy_free
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
    (paper_ranked_gsp_tiebreak_mechanism (n + 1) n).LocallyEnvyFreeEquilibrium
      (paper_theorem7_ranked_environment model.clickThroughRate)
      (fun i : Fin (n + 1) => model.value i.val)
      (eosFiniteStaticBStarBids model) := by
  exact
    paper_ranked_gsp_tiebreak_stable_assignment_locally_envy_free_equilibrium
      (O := paper_ranked_gsp_tiebreak_mechanism (n + 1) n
        (eosFiniteStaticBStarBids model))
      (bids := eosFiniteStaticBStarBids model)
      rfl
      (fun {i j} hij => eos_finite_static_bstar_strict model hij)
      (fun s => le_of_lt (model.click_pos s.val s.isLt))
      (eos_finite_static_bstar_tiebreak_outcome_stable model)

/-- Direct finite source conclusion for EOS Theorem 7's constructed profile. -/
theorem eos_finite_static_bstar_tiebreak_source_conclusion
    {n : ℕ} (model : EOSFiniteStaticBStarOrder n) :
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
          model.vcgTotalPayment i.val := by
  rcases eos_finite_static_bstar_tiebreak_gsp_realization model with
    ⟨hslots, hunassigned, hpayments⟩
  refine ⟨eos_finite_static_bstar_tiebreak_locally_envy_free model,
    hslots, hunassigned, ?_⟩
  intro i
  rw [hpayments i]
  exact paper_theorem7_bstar_next_bid_payment_eq_vcg
    model.value model.vcgTotalPayment model.clickThroughRate i.val
    (ne_of_gt (model.click_pos i.val i.isLt))


end

end EOS07GSP
