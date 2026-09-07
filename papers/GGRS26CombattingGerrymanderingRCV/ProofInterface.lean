import GGRS26CombattingGerrymanderingRCV.PaperInterface

/-!
# Proof endpoints for the paper-facing GGRS specifications

`PaperInterface` contains each source claim once as a transparent `Spec`.
This module supplies the separately compiled evidence endpoint for that
specification without adding a second human semantic-review target.
-/

namespace GGRS26CombattingGerrymanderingRCV

open AppliedModelingLib.SocialChoice.Voting

/-- The constructed Republican selector satisfies the exact source min-argmax rule. -/
theorem paper_thiele_party_republican_seat_count_spec
    (weights : PaperThieleWeights) (partyShare : ℝ) (seats : ℕ) :
    paper_thiele_party_min_argmax weights
      (paper_thiele_party_republican_seat_count weights partyShare seats)
      partyShare seats := by
  exact (paper_thiele_party_republican_selection weights partyShare seats).2

/--
The constructed source selectors satisfy the complete two-party selector
relation; in particular the natural-number complement is taken only after the
Republican count has been proved feasible.
-/
theorem paper_thiele_party_selected_seat_counts_spec
    (weights : PaperThieleWeights) (partyShare : ℝ) (seats : ℕ) :
    paper_thiele_party_selected_seat_counts weights partyShare seats
      (paper_thiele_party_republican_seat_count weights partyShare seats)
      (paper_thiele_party_democratic_seat_count weights partyShare seats) := by
  exact ⟨paper_thiele_party_republican_seat_count_spec weights partyShare seats, rfl⟩

/-- The two selected party counts add to the district magnitude, without truncation. -/
theorem paper_thiele_party_selected_seat_counts_add
    (weights : PaperThieleWeights) (partyShare : ℝ) (seats : ℕ) :
    paper_thiele_party_republican_seat_count weights partyShare seats +
        paper_thiele_party_democratic_seat_count weights partyShare seats = seats := by
  have hle :=
    (paper_thiele_party_republican_seat_count_spec weights partyShare seats).1
  exact Nat.add_sub_of_le hle

/-- The PAV specialization satisfies the exact source leftmost-maximizer rule. -/
theorem paper_pav_selected_seat_count_spec
    (partyShare : ℝ) (seats : ℕ) :
    paper_pav_min_argmax (paper_pav_selected_seat_count partyShare seats)
      partyShare seats := by
  exact paper_thiele_party_republican_seat_count_spec
    paper_pav_thiele_weights partyShare seats

theorem paper_lemma_c1_pav_selector_eq_unique_integer_interval
    {seats : ℕ} {partyShare : ℝ}
    (hseats : 1 ≤ seats) (hpos : 0 < partyShare) (hle : partyShare ≤ 1) :
    paper_lemma_c1_pav_selector_eq_unique_integer_intervalSpec
      (seats := seats) hseats hpos hle := by
  obtain ⟨seatCount, hmin⟩ :=
    exists_isMinArgmaxOn (pavSeatScore partyShare seats) seats
  have hpaper : paper_pav_min_argmax seatCount partyShare seats := by
    simpa [paper_pav_min_argmax, paper_pav_seat_score, pavSeatMinArgmax,
      pavSeatScore] using hmin
  refine ⟨seatCount, hpaper, ?_⟩
  have hinterval := paper_pav_min_argmax_seat_interval hpos hle hpaper
  have hinteger : paper_pav_integer_interval (seatCount : ℤ) partyShare seats := by
    constructor
    · exact_mod_cast hinterval.1
    · exact_mod_cast hinterval.2
  refine ⟨(seatCount : ℤ), rfl, hinteger, ?_, ?_⟩
  · intro other hother
    exact pavSeatIntegerInterval_eq_of_pavSeatInterval
      (by simpa [paper_pav_seat_interval] using hinterval) hother
  · intro otherSeatCount hother
    have hotherInterval := paper_pav_min_argmax_seat_interval hpos hle hother
    exact pavSeatIntegerInterval_eq_of_pavSeatInterval
      (by simpa [paper_pav_seat_interval] using hinterval)
      (by
        constructor
        · exact_mod_cast hotherInterval.1
        · exact_mod_cast hotherInterval.2)

theorem paper_pav_selected_seat_count_zero (seats : ℕ) :
    paper_pav_selected_seat_count 0 seats = 0 := by
  let choice := pavSeatMinArgmaxChoice 0 seats
  have hmin : pavSeatMinArgmax choice 0 seats :=
    pavSeatMinArgmaxChoice_spec 0 seats
  have hweightNonneg : ∀ n, 0 ≤ pavWeight n := by
    intro n
    unfold pavWeight
    split <;> positivity
  have hmono : Monotone pavHarmonicSum := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Nat.add_succ, pavHarmonicSum_succ]
        exact ih.trans (le_add_of_nonneg_right (hweightNonneg _))
  have hchoiceScoreLe :
      pavSeatScore 0 seats choice ≤ pavSeatScore 0 seats 0 := by
    simpa [pavSeatScore] using hmono (Nat.sub_le seats choice)
  have hzeroScoreLe :
      pavSeatScore 0 seats 0 ≤ pavSeatScore 0 seats choice :=
    hmin.2.1 0 (Nat.zero_le seats)
  have hzeroScoreEq :
      pavSeatScore 0 seats 0 = pavSeatScore 0 seats choice :=
    le_antisymm hzeroScoreLe hchoiceScoreLe
  have hchoiceZero : choice = 0 :=
    Nat.eq_zero_of_le_zero (hmin.2.2 0 (Nat.zero_le seats) hzeroScoreEq)
  simpa [paper_pav_selected_seat_count, choice] using hchoiceZero

theorem paper_pav_selected_seat_count_rounded_of_nonneg
    {seats : ℕ} {partyShare : ℝ}
    (hnonneg : 0 ≤ partyShare) (hle : partyShare ≤ 1) :
    paper_seat_share_rounded
      (paper_pav_selected_seat_count partyShare seats) partyShare seats := by
  rcases hnonneg.eq_or_lt with hzero | hpos
  · subst partyShare
    unfold paper_seat_share_rounded seatShareRounded
    rw [paper_pav_selected_seat_count_zero]
    left
    rw [zero_mul, Nat.floor_zero]
  · apply paper_pav_min_argmax_seat_share_rounded hpos hle
    simpa [paper_pav_min_argmax, paper_pav_selected_seat_count,
      paper_pav_seat_score, pavSeatMinArgmax, pavSeatScore] using
      (pavSeatMinArgmaxChoice_spec partyShare seats)

/--
Every D-favoring terminal run of an admitted surplus-preserving ballot policy
satisfies the STV half of Proposition 1, including at Republican share zero.
-/
theorem paper_source_selected_ballot_routed_terminal_rounded
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
    (policy : BallotRoutedSTVTransferPolicy allVoters ballots
      (STVQuota seats voters : ℝ))
    (hnonneg : 0 ≤ partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyComplete :
      paper_complete_party_ranking_ballots
        partyVoters ballots partyCandidates initialActive)
    (hotherComplete :
      paper_complete_party_ranking_ballots
        otherPartyVoters ballots otherPartyCandidates initialActive)
    (hvoters_card : voters = allVoters.card)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset : initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard :
      partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard :
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ))
    {terminal : BallotRoutedSTVState allVoters initialActive}
    (hrun : BallotRoutedDFavoringSTVRun
      (favoredParty := otherPartyCandidates)
      ballots (STVQuota seats voters : ℝ) policy seats
      (paper_proposition1_ballot_routed_stv_initial_state
        allVoters initialActive) terminal)
    (hterminal : BallotRoutedSTVTerminal seats terminal) :
    paper_seat_share_rounded
      (ballotRoutedPartyFinalSeats partyCandidates seats terminal)
      partyShare seats := by
  have hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates :=
    paper_complete_party_ranking_ballots_solid_coalition hpartyComplete
  have hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates :=
    paper_complete_party_ranking_ballots_solid_coalition hotherComplete
  have hrunGeneral :
      BallotRoutedSTVRun ballots (STVQuota seats voters : ℝ) policy seats
        (paper_proposition1_ballot_routed_stv_initial_state
          allVoters initialActive) terminal :=
    BallotRoutedDFavoringSTVRun.refines hrun
  rcases hnonneg.eq_or_lt with hzero | hpos
  · have hotherResult :=
      proposition1_seatSharesRounded_of_ballotRoutedSTVTerminalRun_and_pavMinArgmax
        (Voter := Voter) (Candidate := Candidate)
        (partyVoters := otherPartyVoters) (otherPartyVoters := partyVoters)
        (allVoters := allVoters) (ballots := ballots)
        (partyCandidates := otherPartyCandidates)
        (otherPartyCandidates := partyCandidates)
        (initialActive := initialActive)
        (initialWeight := fun _ : Voter => (1 : ℝ))
        (pavSeatCount := pavSeatMinArgmaxChoice 1 seats)
        (seats := seats) (voters := voters) (partyShare := (1 : ℝ))
        (policy := policy) (by norm_num) (by norm_num) hvoters
        hotherPartyCandidates hpartyCandidates hotherSolid hpartySolid
        hvoters_card (by simpa [Finset.union_comm] using hvoterPartition)
        hcandidateDisjoint.symm hotherPartyInitialActive hpartyInitialActive
        (by simpa [Finset.union_comm] using hinitialActiveSubset)
        (by simpa [hzero.symm] using hotherShareCard)
        (by simpa [hzero.symm] using hpartyShareCard)
        (by intro voter hvoter; rfl)
        (by intro voter hvoter; positivity)
        (by simpa [paper_proposition1_ballot_routed_stv_initial_state] using
          hrunGeneral)
        hterminal (pavSeatMinArgmaxChoice_spec 1 seats)
    have hotherFinal :
        ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal = seats := by
      rcases hotherResult.1 with hfloor | hceil
      · rw [one_mul, Nat.floor_natCast] at hfloor
        exact hfloor
      · rw [one_mul, Nat.ceil_natCast] at hceil
        exact hceil
    have helectedLe : terminal.elected.card ≤ seats :=
      BallotRoutedSTVTransition.elected_le_seats_of_run
        (ballots := ballots) (policy := policy) (seats := seats)
        (by simp [paper_proposition1_ballot_routed_stv_initial_state]) hrunGeneral
    have hseatSum := ballotRoutedTwoPartyFinalSeats_add helectedLe hterminal
      hcandidateDisjoint hinitialActiveSubset
    have hpartyFinal :
        ballotRoutedPartyFinalSeats partyCandidates seats terminal = 0 := by
      omega
    unfold paper_seat_share_rounded seatShareRounded
    rw [hzero.symm, hpartyFinal]
    left
    rw [zero_mul, Nat.floor_zero]
  · have hpav :
        pavSeatMinArgmax (pavSeatMinArgmaxChoice partyShare seats)
          partyShare seats := pavSeatMinArgmaxChoice_spec partyShare seats
    have hresult :=
      proposition1_seatSharesRounded_of_ballotRoutedSTVTerminalRun_and_pavMinArgmax
            (Voter := Voter) (Candidate := Candidate)
            (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
            (allVoters := allVoters) (ballots := ballots)
            (partyCandidates := partyCandidates)
            (otherPartyCandidates := otherPartyCandidates)
            (initialActive := initialActive)
            (initialWeight := fun _ : Voter => (1 : ℝ))
            (pavSeatCount := pavSeatMinArgmaxChoice partyShare seats)
            (seats := seats) (voters := voters) (partyShare := partyShare)
            (policy := policy) hpos hle hvoters hpartyCandidates
            hotherPartyCandidates hpartySolid hotherSolid hvoters_card
            hvoterPartition hcandidateDisjoint hpartyInitialActive
            hotherPartyInitialActive hinitialActiveSubset hpartyShareCard
            hotherShareCard (by intro voter hvoter; rfl)
            (by intro voter hvoter; positivity)
            (by simpa [paper_proposition1_ballot_routed_stv_initial_state] using
              hrunGeneral)
            hterminal hpav
    simpa [paper_seat_share_rounded] using hresult.1

theorem paper_proposition1_source_selected_fractional_stv_and_pav
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
    (hnonneg : 0 ≤ partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyComplete :
      paper_complete_party_ranking_ballots
        partyVoters ballots partyCandidates initialActive)
    (hotherComplete :
      paper_complete_party_ranking_ballots
        otherPartyVoters ballots otherPartyCandidates initialActive)
    (hvoters_card : voters = allVoters.card)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset : initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard :
      partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard :
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ)) :
    paper_proposition1_source_selected_fractional_stv_and_pavSpec
      hnonneg hle hvoters hpartyCandidates hotherPartyCandidates
      hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard := by
  let policy := fractionalBallotRoutedSTVTransferPolicy
    (voters := allVoters) (ballots := ballots) (stvQuota_pos seats voters)
  have hseats : seats ≤ initialActive.card :=
    le_trans hpartyCandidates (Finset.card_le_card hpartyInitialActive)
  obtain ⟨terminal, hrun, hterminal⟩ :=
    exists_ballotRoutedDFavoringSTVTerminalRun
      (favoredParty := otherPartyCandidates) (policy := policy)
      hseats (fun _ : Voter => (1 : ℝ)) (by intro voter hvoter; positivity)
  refine ⟨⟨terminal, ?_, hterminal⟩, ?_,
    paper_pav_selected_seat_count_rounded_of_nonneg hnonneg hle⟩
  · simpa [policy, paper_proposition1_ballot_routed_stv_initial_state] using hrun
  · intro terminal hrun hterminal
    exact paper_source_selected_ballot_routed_terminal_rounded
      policy hnonneg hle hvoters hpartyCandidates hotherPartyCandidates
      hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard
      (by simpa [policy] using hrun) hterminal

theorem paper_surplus_preserving_transfer_rules_induce_source_selected_rounded_seat_share
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
    (policy : BallotRoutedSTVTransferPolicy allVoters ballots
      (STVQuota seats voters : ℝ))
    (hnonneg : 0 ≤ partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyComplete :
      paper_complete_party_ranking_ballots
        partyVoters ballots partyCandidates initialActive)
    (hotherComplete :
      paper_complete_party_ranking_ballots
        otherPartyVoters ballots otherPartyCandidates initialActive)
    (hvoters_card : voters = allVoters.card)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset : initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard :
      partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard :
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ)) :
    paper_surplus_preserving_transfer_rules_induce_source_selected_rounded_seat_shareSpec
      policy hnonneg hle hvoters hpartyCandidates hotherPartyCandidates
      hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard := by
  have hseats : seats ≤ initialActive.card :=
    le_trans hpartyCandidates (Finset.card_le_card hpartyInitialActive)
  obtain ⟨terminal, hrun, hterminal⟩ :=
    exists_ballotRoutedDFavoringSTVTerminalRun
      (favoredParty := otherPartyCandidates) (policy := policy)
      hseats (fun _ : Voter => (1 : ℝ)) (by intro voter hvoter; positivity)
  refine ⟨⟨terminal, ?_, hterminal⟩, ?_⟩
  · simpa [paper_proposition1_ballot_routed_stv_initial_state] using hrun
  · intro terminal hrun hterminal
    exact paper_source_selected_ballot_routed_terminal_rounded
      policy hnonneg hle hvoters hpartyCandidates hotherPartyCandidates
      hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard hrun hterminal

theorem paper_proposition1_source_selected_stv_and_pav
    {Voter Candidate : Type*}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
    (hseats : 1 ≤ seats)
    (hnonneg : 0 ≤ partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card) :
    paper_proposition1_source_selected_stv_and_pavSpec
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates) (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) (seats := seats) (voters := voters)
      (partyShare := partyShare)
      hseats hnonneg hle hvoters hpartyCandidates hotherPartyCandidates := by
  classical
  unfold paper_proposition1_source_selected_stv_and_pavSpec
  intro hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
    hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
    hinitialActiveSubset hpartyShareCard hotherShareCard
  refine ⟨?_, paper_pav_selected_seat_count_rounded_of_nonneg hnonneg hle⟩
  intro policy
  exact
    paper_surplus_preserving_transfer_rules_induce_source_selected_rounded_seat_share
      policy hnonneg hle hvoters hpartyCandidates hotherPartyCandidates
      hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard

theorem paper_map_level_party_share_pigeonhole_and_pav_one_seat_guarantee
    {District : Type*} [Fintype District]
    (districtWeight districtPartyShare : District → ℝ)
    (statewidePartyShare : ℝ) (districtMagnitude : ℕ)
    (pavSeatCount : District → ℕ)
    (hweight_nonneg : ∀ district, 0 ≤ districtWeight district)
    (hweight_sum : (∑ district, districtWeight district) = 1)
    (hstatewide :
      statewidePartyShare =
        ∑ district, districtWeight district * districtPartyShare district)
    (hshare_bounds :
      ∀ district, 0 ≤ districtPartyShare district ∧
        districtPartyShare district ≤ 1)
    (hpav :
      ∀ district,
        paper_pav_min_argmax
          (pavSeatCount district) (districtPartyShare district)
          districtMagnitude) :
    paper_map_level_party_share_pigeonhole_and_pav_one_seat_guaranteeSpec
      districtWeight districtPartyShare statewidePartyShare districtMagnitude
      pavSeatCount hweight_nonneg hweight_sum hstatewide hshare_bounds hpav := by
  have hpigeonhole :
      ∃ district, statewidePartyShare ≤ districtPartyShare district := by
    by_contra hnone
    push Not at hnone
    obtain ⟨strictDistrict, hstrictWeight⟩ :=
      AppliedModelingLib.exists_positive_weight_of_nonneg_sum_eq_one
        districtWeight hweight_nonneg hweight_sum
    have hsum_lt :
        (∑ district, districtWeight district * districtPartyShare district) <
          ∑ district, districtWeight district * statewidePartyShare := by
      refine Finset.sum_lt_sum (fun district _ ↦ ?_) ?_
      · exact mul_le_mul_of_nonneg_left
          (le_of_lt (hnone district)) (hweight_nonneg district)
      · exact ⟨strictDistrict, Finset.mem_univ _,
          mul_lt_mul_of_pos_left (hnone strictDistrict) hstrictWeight⟩
    have hconstant :
        (∑ district, districtWeight district * statewidePartyShare) =
          statewidePartyShare := by
      rw [← Finset.sum_mul, hweight_sum, one_mul]
    rw [← hstatewide, hconstant] at hsum_lt
    exact (lt_irrefl statewidePartyShare) hsum_lt
  refine ⟨hpigeonhole, ?_, ?_⟩
  · intro smallerMagnitude largerMagnitude hsmaller
    unfold paper_pav_one_seat_vote_share_threshold
    apply one_div_lt_one_div_of_lt
    · positivity
    · exact_mod_cast Nat.add_lt_add_right hsmaller 1
  · intro habove
    obtain ⟨district, hdistrict⟩ := hpigeonhole
    refine ⟨district, hdistrict, ?_⟩
    have hthreshold_pos :
        0 < paper_pav_one_seat_vote_share_threshold districtMagnitude := by
      unfold paper_pav_one_seat_vote_share_threshold
      positivity
    have hdistrict_pos : 0 < districtPartyShare district :=
      lt_of_lt_of_le (lt_trans hthreshold_pos habove) hdistrict
    have hinterval := paper_pav_min_argmax_seat_interval
      hdistrict_pos (hshare_bounds district).2 (hpav district)
    have hthreshold_at_district :
        paper_pav_one_seat_vote_share_threshold districtMagnitude <
          districtPartyShare district :=
      lt_of_lt_of_le habove hdistrict
    have hdenominator_pos :
        0 < (((districtMagnitude + 1 : ℕ) : ℝ)) := by positivity
    have hproduct :
        1 < districtPartyShare district *
          (((districtMagnitude + 1 : ℕ) : ℝ)) := by
      have := (div_lt_iff₀ hdenominator_pos).mp hthreshold_at_district
      simpa [paper_pav_one_seat_vote_share_threshold] using this
    have hseat_pos_real : 0 < (pavSeatCount district : ℝ) :=
      lt_of_lt_of_le (sub_pos.mpr hproduct) hinterval.1
    exact_mod_cast hseat_pos_real

end GGRS26CombattingGerrymanderingRCV
