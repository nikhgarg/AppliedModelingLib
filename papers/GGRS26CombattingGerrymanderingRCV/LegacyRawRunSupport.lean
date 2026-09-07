import GGRS26CombattingGerrymanderingRCV.PaperInterface

/-!
# Quarantined Legacy Raw-Run Support

This module preserves historical theorem names for downstream compatibility.
Each declaration below takes a raw global run and/or a global-to-party
refinement as an input. Those records contain proof-relevant structure that
the source paper does not expose, so this module is not a source-facing proof
surface and must not receive Proposition 1 audit credit.

The source-facing Proposition 1 route is
`paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav`
in `PaperInterface.lean`, which derives its terminal execution and party
accounting from the ballot-routed STV semantics.
-/

namespace GGRS26CombattingGerrymanderingRCV

open AppliedModelingLib.SocialChoice.Voting

/--
Legacy raw-run bridge retained only for compatibility. It is not eligible for
source-facing Proposition 1 credit.
-/
theorem paper_exact_global_transition_serializes_and_conserves
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (refinement :
      SourceTwoPartyGlobalSurplusPreservingRefinement globalRule quota
        partyRule otherPartyRule seats)
    {before after : SourceSTVState Candidate TransferState}
    (htransition :
      paper_source_stv_batched_transition globalRule quota seats before after)
    (hpartyActive :
      (before.active ∩ refinement.partyCandidates).Nonempty)
    (hotherPartyActive :
      (before.active ∩ refinement.otherPartyCandidates).Nonempty) :
    Relation.ReflTransGen partyRule.step
        (refinement.partyProjection before)
        (refinement.partyProjection after) ∧
      Relation.ReflTransGen otherPartyRule.step
        (refinement.otherPartyProjection before)
        (refinement.otherPartyProjection after) ∧
      (((refinement.partyProjection before).quotaWinners : ℝ) * quota +
          (refinement.partyProjection before).voteMass =
        ((refinement.partyProjection after).quotaWinners : ℝ) * quota +
          (refinement.partyProjection after).voteMass) ∧
      (((refinement.otherPartyProjection before).quotaWinners : ℝ) * quota +
          (refinement.otherPartyProjection before).voteMass =
        ((refinement.otherPartyProjection after).quotaWinners : ℝ) * quota +
          (refinement.otherPartyProjection after).voteMass) := by
  have hsource :
      SourceSTVBatchedTransition globalRule quota seats before after := by
    simpa [paper_source_stv_batched_transition] using htransition
  exact ⟨refinement.party_serialization hsource hpartyActive hotherPartyActive,
    refinement.otherParty_serialization hsource hpartyActive hotherPartyActive,
    refinement.partyTransferConserved hsource hpartyActive hotherPartyActive,
    refinement.otherPartyTransferConserved hsource hpartyActive
      hotherPartyActive⟩

/--
Legacy raw-run coherence theorem retained only for compatibility. It is not
eligible for source-facing Proposition 1 credit.
-/
theorem paper_exact_global_transition_uses_actual_party_candidates_and_tallies
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (refinement :
      SourceTwoPartyGlobalSurplusPreservingRefinement globalRule quota
        partyRule otherPartyRule seats)
    {before after : SourceSTVState Candidate TransferState}
    (htransition :
      paper_source_stv_batched_transition globalRule quota seats before after)
    (hpartyActive :
      (before.active ∩ refinement.partyCandidates).Nonempty)
    (hotherPartyActive :
      (before.active ∩ refinement.otherPartyCandidates).Nonempty) :
    (((refinement.partyProjection before).remainingCandidates =
          (before.active ∩ refinement.partyCandidates).card ∧
        (refinement.otherPartyProjection before).remainingCandidates =
          (before.active ∩ refinement.otherPartyCandidates).card) ∧
      ((refinement.partyProjection after).remainingCandidates =
          (after.active ∩ refinement.partyCandidates).card ∧
        (refinement.otherPartyProjection after).remainingCandidates =
          (after.active ∩ refinement.otherPartyCandidates).card)) ∧
    ((((refinement.partyProjection before).voteMass =
          (∑ candidate ∈ before.active ∩ refinement.partyCandidates,
            globalRule.tally before.active before.transferState candidate)) ∧
        ((refinement.otherPartyProjection before).voteMass =
          (∑ candidate ∈ before.active ∩ refinement.otherPartyCandidates,
            globalRule.tally before.active before.transferState candidate))) ∧
      (((after.active ∩ refinement.partyCandidates).Nonempty ∧
          (after.active ∩ refinement.otherPartyCandidates).Nonempty) →
        ((refinement.partyProjection after).voteMass =
            (∑ candidate ∈ after.active ∩ refinement.partyCandidates,
              globalRule.tally after.active after.transferState candidate)) ∧
          ((refinement.otherPartyProjection after).voteMass =
            (∑ candidate ∈ after.active ∩ refinement.otherPartyCandidates,
              globalRule.tally after.active after.transferState candidate)))) ∧
    ((∃ winners,
        SourceSTVElectBatchTransition globalRule quota seats winners before after ∧
        (refinement.partyProjection after).quotaWinners =
          (refinement.partyProjection before).quotaWinners +
            (winners ∩ refinement.partyCandidates).card ∧
        (refinement.otherPartyProjection after).quotaWinners =
          (refinement.otherPartyProjection before).quotaWinners +
            (winners ∩ refinement.otherPartyCandidates).card) ∨
      (∃ loser,
        SourceSTVEliminateTransition globalRule quota seats loser before after ∧
        (refinement.partyProjection after).quotaWinners =
          (refinement.partyProjection before).quotaWinners ∧
        (refinement.otherPartyProjection after).quotaWinners =
          (refinement.otherPartyProjection before).quotaWinners)) := by
  have hsource :
      SourceSTVBatchedTransition globalRule quota seats before after := by
    simpa [paper_source_stv_batched_transition] using htransition
  refine ⟨
    ⟨
      ⟨refinement.party_remaining_coherent before,
        refinement.otherParty_remaining_coherent before⟩,
      ⟨refinement.party_remaining_coherent after,
        refinement.otherParty_remaining_coherent after⟩⟩,
    ⟨
      ⟨
        ⟨refinement.party_voteMass_coherent_before_cutoff before
            hpartyActive hotherPartyActive,
          refinement.otherParty_voteMass_coherent_before_cutoff before
            hpartyActive hotherPartyActive⟩,
        (by
          rintro ⟨hpartyAfter, hotherPartyAfter⟩
          exact ⟨refinement.party_voteMass_coherent_before_cutoff after
              hpartyAfter hotherPartyAfter,
            refinement.otherParty_voteMass_coherent_before_cutoff after
              hpartyAfter hotherPartyAfter⟩)⟩,
      ?_⟩⟩
  cases hsource with
  | electBatch winners hnotTerminal hnonempty hactive hroom hquota
      hafterActive hafterElected htransfer =>
      left
      have helect :
          SourceSTVElectBatchTransition globalRule quota seats winners
            before after :=
        ⟨hnotTerminal, hnonempty, hactive, hroom, hquota,
          hafterActive, hafterElected, htransfer⟩
      exact ⟨winners, helect,
        refinement.party_winner_update_elect winners helect,
        refinement.otherParty_winner_update_elect winners helect⟩
  | eliminate loser hnotTerminal hactive hnoQuota hminimum
      hafterActive hafterElected htransfer =>
      right
      have heliminate :
          SourceSTVEliminateTransition globalRule quota seats loser
            before after :=
        ⟨hnotTerminal, hactive, hnoQuota, hminimum,
          hafterActive, hafterElected, htransfer⟩
      exact ⟨loser, heliminate,
        refinement.party_winner_update_eliminate loser heliminate,
        refinement.otherParty_winner_update_eliminate loser heliminate⟩

/--
Legacy raw-run cutoff theorem retained only for compatibility. It is not
eligible for source-facing Proposition 1 credit.
-/
theorem paper_common_cutoff_has_connected_local_prefixes
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota partyInitialVotes otherPartyInitialVotes : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (rawRun :
      SourceTwoPartyExactTerminalGlobalRun globalRule partyRule
        otherPartyRule partyInitialVotes otherPartyInitialVotes seats) :
    ∃ cutoffState,
      Relation.ReflTransGen partyRule.step
          (PartyQuotaStartState rawRun.partyInitialCandidates partyInitialVotes)
          (rawRun.refinement.partyProjection cutoffState) ∧
        Relation.ReflTransGen otherPartyRule.step
          (PartyQuotaStartState rawRun.otherPartyInitialCandidates
            otherPartyInitialVotes)
          (rawRun.refinement.otherPartyProjection cutoffState) ∧
        (SourceSTVTerminal seats cutoffState ∨
          (cutoffState.active ∩
            rawRun.refinement.partyCandidates).card = 0 ∨
          (cutoffState.active ∩
            rawRun.refinement.otherPartyCandidates).card = 0) := by
  let globalRun := rawRun.toCommonCutoffRun
  refine ⟨globalRun.cutoffState, ?_, ?_, ?_⟩
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun] using
      globalRun.partyPath
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun] using
      globalRun.otherPartyPath
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun] using
      globalRun.cutoff_condition

/--
Legacy raw-run suffix theorem retained only for compatibility. It is not
eligible for source-facing Proposition 1 credit.
-/
theorem paper_common_cutoff_has_unrestricted_exact_suffix
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota partyInitialVotes otherPartyInitialVotes : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (rawRun :
      SourceTwoPartyExactTerminalGlobalRun globalRule partyRule
        otherPartyRule partyInitialVotes otherPartyInitialVotes seats) :
    ∃ cutoffState,
      Relation.ReflTransGen
        (paper_source_stv_batched_transition globalRule quota seats)
          cutoffState rawRun.terminalState ∧
        (SourceSTVTerminal seats cutoffState ∨
          (cutoffState.active ∩
            rawRun.refinement.partyCandidates).card = 0 ∨
          (cutoffState.active ∩
            rawRun.refinement.otherPartyCandidates).card = 0) := by
  let globalRun := rawRun.toCommonCutoffRun
  refine ⟨globalRun.cutoffState, ?_, ?_⟩
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun,
      paper_source_stv_batched_transition] using globalRun.suffix
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun] using
      globalRun.cutoff_condition

/--
Legacy raw-run terminal-output theorem retained only for compatibility. It is
not eligible for source-facing Proposition 1 credit.
-/
theorem paper_common_cutoff_terminal_outputs_fill_all_seats
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota partyInitialVotes otherPartyInitialVotes : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (rawRun :
      SourceTwoPartyExactTerminalGlobalRun globalRule partyRule
        otherPartyRule partyInitialVotes otherPartyInitialVotes seats) :
    ((rawRun.refinement.partyProjection
          rawRun.terminalState).quotaWinners +
        if rawRun.terminalState.elected < seats then
          (rawRun.terminalState.active ∩
            rawRun.refinement.partyCandidates).card
        else 0) +
      ((rawRun.refinement.otherPartyProjection
          rawRun.terminalState).quotaWinners +
        if rawRun.terminalState.elected < seats then
          (rawRun.terminalState.active ∩
            rawRun.refinement.otherPartyCandidates).card
        else 0) = seats := by
  let globalRun := rawRun.toCommonCutoffRun
  simpa [globalRun,
    SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun,
    SourceTwoPartyExactTerminalGlobalRun.actualPartyFinalSeats,
    SourceTwoPartyExactTerminalGlobalRun.actualOtherPartyFinalSeats,
    SourceTwoPartySurplusPreservingGlobalRun.actualPartyFinalSeats,
    SourceTwoPartySurplusPreservingGlobalRun.actualOtherPartyFinalSeats] using
    globalRun.actualFinalSeats_add

/--
Legacy raw-run exhausted-party suffix theorem retained only for compatibility.
It is not eligible for source-facing Proposition 1 credit.
-/
theorem paper_cross_party_transfer_suffix_freezes_exhausted_party_output
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota partyInitialVotes otherPartyInitialVotes : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (rawRun :
      SourceTwoPartyExactTerminalGlobalRun globalRule partyRule
        otherPartyRule partyInitialVotes otherPartyInitialVotes seats) :
    ∃ cutoffState,
      Relation.ReflTransGen
          (paper_source_stv_batched_transition globalRule quota seats)
          cutoffState rawRun.terminalState ∧
        (SourceSTVTerminal seats cutoffState ∨
          (cutoffState.active ∩
            rawRun.refinement.partyCandidates).card = 0 ∨
          (cutoffState.active ∩
            rawRun.refinement.otherPartyCandidates).card = 0) ∧
        ((cutoffState.active ∩
              rawRun.refinement.partyCandidates).card = 0 →
          (rawRun.refinement.partyProjection
                rawRun.terminalState).quotaWinners +
              (if rawRun.terminalState.elected < seats then
                (rawRun.terminalState.active ∩
                  rawRun.refinement.partyCandidates).card
              else 0) =
            (rawRun.refinement.partyProjection cutoffState).quotaWinners) := by
  let globalRun := rawRun.toCommonCutoffRun
  refine ⟨globalRun.cutoffState, ?_, ?_, ?_⟩
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun,
      paper_source_stv_batched_transition] using globalRun.suffix
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun] using
      globalRun.cutoff_condition
  · intro hexhausted
    simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun,
      SourceTwoPartyExactTerminalGlobalRun.actualPartyFinalSeats,
      SourceTwoPartySurplusPreservingGlobalRun.actualPartyFinalSeats] using
      globalRun.actualPartyFinal_eq_cutoffWinners_of_exhausted hexhausted

/--
Legacy raw-run exhausted-other-party suffix theorem retained only for
compatibility. It is not eligible for source-facing Proposition 1 credit.
-/
theorem paper_cross_party_transfer_suffix_freezes_exhausted_other_party_output
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {quota partyInitialVotes otherPartyInitialVotes : ℝ}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule quota}
    {seats : ℕ}
    (rawRun :
      SourceTwoPartyExactTerminalGlobalRun globalRule partyRule
        otherPartyRule partyInitialVotes otherPartyInitialVotes seats) :
    ∃ cutoffState,
      Relation.ReflTransGen
          (paper_source_stv_batched_transition globalRule quota seats)
          cutoffState rawRun.terminalState ∧
        (SourceSTVTerminal seats cutoffState ∨
          (cutoffState.active ∩
            rawRun.refinement.partyCandidates).card = 0 ∨
          (cutoffState.active ∩
            rawRun.refinement.otherPartyCandidates).card = 0) ∧
        ((cutoffState.active ∩
              rawRun.refinement.otherPartyCandidates).card = 0 →
          (rawRun.refinement.otherPartyProjection
                rawRun.terminalState).quotaWinners +
              (if rawRun.terminalState.elected < seats then
                (rawRun.terminalState.active ∩
                  rawRun.refinement.otherPartyCandidates).card
              else 0) =
            (rawRun.refinement.otherPartyProjection cutoffState).quotaWinners) := by
  let globalRun := rawRun.toCommonCutoffRun
  refine ⟨globalRun.cutoffState, ?_, ?_, ?_⟩
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun,
      paper_source_stv_batched_transition] using globalRun.suffix
  · simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun] using
      globalRun.cutoff_condition
  · intro hexhausted
    simpa [globalRun,
      SourceTwoPartyExactTerminalGlobalRun.toCommonCutoffRun,
      SourceTwoPartyExactTerminalGlobalRun.actualOtherPartyFinalSeats,
      SourceTwoPartySurplusPreservingGlobalRun.actualOtherPartyFinalSeats] using
      globalRun.actualOtherPartyFinal_eq_cutoffWinners_of_exhausted hexhausted

/--
Legacy raw-run Proposition 1 wrapper retained only for downstream
compatibility. Its \`rawRun\` input makes it ineligible for source-facing
Proposition 1 credit.
-/
theorem paper_proposition1_for_all_surplus_preserving_transfer_rules_and_pav_min_argmax
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    {seats voters pavSeatCount : ℕ} {partyShare : ℝ}
    {globalRule : SourceSTVTransferRule Candidate TransferState}
    {partyRule otherPartyRule :
      SourceSurplusPreservingPartyTransferRule
        (STVQuota seats voters : ℝ)}
    (rawRun :
      SourceTwoPartyExactTerminalGlobalRun globalRule partyRule
        otherPartyRule (partyShare * (voters : ℝ))
        ((1 - partyShare) * (voters : ℝ)) seats)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ rawRun.partyInitialCandidates)
    (hotherPartyCandidates : seats ≤ rawRun.otherPartyInitialCandidates)
    (hpav : paper_pav_min_argmax pavSeatCount partyShare seats) :
    paper_seat_share_rounded rawRun.actualPartyFinalSeats partyShare seats ∧
      paper_seat_share_rounded pavSeatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score,
    paper_seat_share_rounded, pavSeatMinArgmax, pavSeatScore,
    seatShareRounded] using
    (proposition1_seatSharesRounded_of_exactTerminalGlobalRun_all_surplusPreservingTransferRules_and_pavMinArgmax
      (rawRun := rawRun) hpos hle hvoters hpartyCandidates
        hotherPartyCandidates hpav)

end GGRS26CombattingGerrymanderingRCV
