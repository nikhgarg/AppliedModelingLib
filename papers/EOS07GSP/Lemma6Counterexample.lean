import EOS07GSP.Implementation

/-!
# EOS Lemma 6 zero-surplus counterexample

This module records a finite stable assignment that cannot be the exact
outcome of a strictly ordered GSP profile.  It isolates the zero-surplus
boundary in the Appendix proof of Lemma 6; it does not alter the pinned source
statement or its Definition 4 correction.
-/

namespace EOS07GSP

open AppliedModelingLib.Auction

noncomputable section

/-- Two displayed positions with CTRs 2 and 1. -/
def lemma6ZeroSurplusEnvironment : PositionEnvironment (Fin 2) where
  clickThroughRate := fun slot => if slot = 0 then 2 else 1

/-- Strict bidder values 10, 9, and 8. -/
def lemma6ZeroSurplusValues : Fin 3 → ℝ :=
  fun bidder => if bidder = 0 then 10 else if bidder = 1 then 9 else 8

/-- The top two bidders receive the two slots, each at per-click price 9. -/
def lemma6ZeroSurplusStableOutcome : PositionOutcome (Fin 3) (Fin 2) where
  slotOf := fun bidder =>
    if bidder = 0 then some 0 else if bidder = 1 then some 1 else none
  paymentPerClick := fun _ => 9

/-- The zero-surplus outcome is a stable assignment: every bidder is
individually rational, and no bidder gains by rematching to either slot at its
recorded price. -/
theorem lemma6_zero_surplus_outcome_stable :
    lemma6ZeroSurplusStableOutcome.StableAssignment
      lemma6ZeroSurplusEnvironment lemma6ZeroSurplusValues := by
  constructor
  · intro i j s hi hj
    fin_cases i <;> fin_cases j <;> fin_cases s <;>
      simp [lemma6ZeroSurplusStableOutcome] at hi hj ⊢
  constructor
  · intro i
    fin_cases i <;>
      norm_num [PositionOutcome.utility, lemma6ZeroSurplusStableOutcome,
        lemma6ZeroSurplusEnvironment, lemma6ZeroSurplusValues]
  · intro i j s hslot
    fin_cases i <;> fin_cases j <;> fin_cases s <;>
      (norm_num [PositionOutcome.utility, lemma6ZeroSurplusStableOutcome,
        lemma6ZeroSurplusEnvironment, lemma6ZeroSurplusValues] at hslot <;>
        norm_num [PositionOutcome.utility, lemma6ZeroSurplusStableOutcome,
          lemma6ZeroSurplusEnvironment, lemma6ZeroSurplusValues])

/-- The owner-approved strict-surplus Lemma 6 domain excludes this witness:
bidder 2 is assigned but has exactly zero utility. -/
theorem lemma6_zero_surplus_outcome_not_corrected_lemma6_stable :
    ¬ PaperInterface.correctedLemma6StableAssignment
      lemma6ZeroSurplusEnvironment lemma6ZeroSurplusValues
      lemma6ZeroSurplusStableOutcome := by
  intro hcorrected
  have hpositive := hcorrected.2 (1 : Fin 3) (1 : Fin 2) (by
    simp [lemma6ZeroSurplusStableOutcome])
  norm_num [PositionOutcome.utility, lemma6ZeroSurplusStableOutcome,
    lemma6ZeroSurplusEnvironment, lemma6ZeroSurplusValues] at hpositive

/-- No strictly decreasing deterministic-tie-broken GSP profile can realize
this exact stable outcome: the first and second GSP next-price payments force
the second and third bids both to equal 9.  This is the finite obstruction to
the Appendix Lemma 6 claim that the displayed construction is always strict. -/
theorem lemma6_zero_surplus_outcome_not_realizable_by_strict_tiebreak_gsp
    (bids : Fin 3 → ℝ)
    (hstrict :
      ∀ {i j : Fin 3}, i.val < j.val → bids j < bids i)
    (hout :
      paper_ranked_gsp_tiebreak_mechanism 3 2 bids =
        lemma6ZeroSurplusStableOutcome) : False := by
  rcases
      paper_ranked_gsp_tiebreak_mechanism_realizes_next_price_of_strict_decreasing
        hstrict with
    ⟨_hslots, _hunassigned, hpayments⟩
  have hbid_one : bids (1 : Fin 3) = 9 := by
    calc
      bids (1 : Fin 3) =
          (paper_ranked_gsp_tiebreak_mechanism 3 2 bids).paymentPerClick
            (0 : Fin 3) := by
              simpa using (hpayments (0 : Fin 2)).symm
      _ = 9 := by simp [hout, lemma6ZeroSurplusStableOutcome]
  have hbid_two : bids (2 : Fin 3) = 9 := by
    calc
      bids (2 : Fin 3) =
          (paper_ranked_gsp_tiebreak_mechanism 3 2 bids).paymentPerClick
            (1 : Fin 3) := by
              simpa using (hpayments (1 : Fin 2)).symm
      _ = 9 := by simp [hout, lemma6ZeroSurplusStableOutcome]
  have hlt : bids (2 : Fin 3) < bids (1 : Fin 3) :=
    hstrict (by decide)
  linarith

end

end EOS07GSP
