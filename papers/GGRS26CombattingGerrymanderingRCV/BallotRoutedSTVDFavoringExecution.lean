import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVExecution

/-!
# D-favoring ballot-routed STV executions

The source fixes cross-party ties in party D's favor. The general ballot-routed
transition permits every quota-eligible winner and every minimum-tally loser,
so this file restricts both election and elimination selection to the source
tie convention and proves that the restricted process still has a finite
terminal execution for every admitted surplus-preserving transfer policy.
-/

namespace GGRS26CombattingGerrymanderingRCV

open AppliedModelingLib.SocialChoice.Voting

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]

/--
One source STV transition with cross-party ties resolved in favor of
`favoredParty`.  A non-favored candidate may be selected for election only if
no tied active candidate belongs to the favored party; a favored candidate may
be eliminated only if every candidate tied at that minimum also belongs to the
favored party.  Within-party ties retain exactly the outcome support of the
source's random tie rule; the relation carries no probability weights because
the result is proved for every supported terminal outcome.
-/
inductive BallotRoutedDFavoringSTVTransition
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    (ballots : Voter -> Ballot Candidate) (quota : ℝ)
    (policy : BallotRoutedSTVTransferPolicy voters ballots quota) (seats : ℕ) :
    BallotRoutedSTVState voters initialCandidates ->
      BallotRoutedSTVState voters initialCandidates -> Prop
  | elect {before after : BallotRoutedSTVState voters initialCandidates}
      (winner : Candidate)
      (hnotTerminal : ¬ BallotRoutedSTVTerminal seats before)
      (hactive : winner ∈ before.active)
      (hroom : before.elected.card < seats)
      (hquota : quota ≤
        ballotRoutedTally voters ballots before.active before.weight winner)
      (hdFavor : winner ∉ favoredParty ->
        ∀ candidate, candidate ∈ before.active ->
          ballotRoutedTally voters ballots before.active before.weight candidate =
              ballotRoutedTally voters ballots before.active before.weight winner ->
            candidate ∉ favoredParty)
      (hafterActive : after.active = before.active.erase winner)
      (hafterElected : after.elected = insert winner before.elected)
      (hupdate : policy.electUpdate before.active winner before.weight after.weight) :
      BallotRoutedDFavoringSTVTransition ballots quota policy seats before after
  | eliminate {before after : BallotRoutedSTVState voters initialCandidates}
      (loser : Candidate)
      (hnotTerminal : ¬ BallotRoutedSTVTerminal seats before)
      (hactive : loser ∈ before.active)
      (hnoQuota : ∀ candidate, candidate ∈ before.active ->
        ballotRoutedTally voters ballots before.active before.weight candidate < quota)
      (hminimum : ∀ candidate, candidate ∈ before.active ->
        ballotRoutedTally voters ballots before.active before.weight loser ≤
          ballotRoutedTally voters ballots before.active before.weight candidate)
      (hdFavor : loser ∈ favoredParty ->
        ∀ candidate, candidate ∈ before.active ->
          ballotRoutedTally voters ballots before.active before.weight candidate =
              ballotRoutedTally voters ballots before.active before.weight loser ->
            candidate ∈ favoredParty)
      (hafterActive : after.active = before.active.erase loser)
      (hafterElected : after.elected = before.elected)
      (hupdate : policy.eliminateUpdate before.active loser before.weight after.weight) :
      BallotRoutedDFavoringSTVTransition ballots quota policy seats before after

/-- Every D-favoring source step is an admitted ballot-routed STV step. -/
theorem BallotRoutedDFavoringSTVTransition.refines
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {before after : BallotRoutedSTVState voters initialCandidates}
    (hstep : BallotRoutedDFavoringSTVTransition
      (favoredParty := favoredParty) ballots quota policy seats before after) :
    BallotRoutedSTVTransition ballots quota policy seats before after := by
  cases hstep with
  | elect winner hnotTerminal hactive hroom hquota _hdFavor
      hafterActive hafterElected hupdate =>
      exact BallotRoutedSTVTransition.elect winner hnotTerminal hactive hroom hquota
        hafterActive hafterElected hupdate
  | eliminate loser hnotTerminal hactive hnoQuota hminimum _hdFavor
      hafterActive hafterElected hupdate =>
      exact BallotRoutedSTVTransition.eliminate loser hnotTerminal hactive hnoQuota
        hminimum hafterActive hafterElected hupdate

/-- A finite source execution respecting the D-favoring tie convention. -/
abbrev BallotRoutedDFavoringSTVRun
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    (ballots : Voter -> Ballot Candidate) (quota : ℝ)
    (policy : BallotRoutedSTVTransferPolicy voters ballots quota) (seats : ℕ)
    (initial terminal : BallotRoutedSTVState voters initialCandidates) : Prop :=
  Relation.ReflTransGen
    (BallotRoutedDFavoringSTVTransition
      (favoredParty := favoredParty) ballots quota policy seats)
    initial terminal

/-- A D-favoring run is, in particular, a run of the general source process. -/
theorem BallotRoutedDFavoringSTVRun.refines
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    (hrun : BallotRoutedDFavoringSTVRun
      (favoredParty := favoredParty) ballots quota policy seats initial terminal) :
    BallotRoutedSTVRun ballots quota policy seats initial terminal := by
  exact Relation.ReflTransGen.mono
    (fun _ _ hstep => BallotRoutedDFavoringSTVTransition.refines hstep) hrun

/-- A legal D-favoring transition exists at every reachable nonterminal state. -/
theorem exists_ballotRoutedDFavoringSTVTransition_of_not_terminal
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {state : BallotRoutedSTVState voters initialCandidates}
    (helected : state.elected.card ≤ seats)
    (havailable : BallotRoutedSeatAvailability (seats := seats) state)
    (hnotTerminal : ¬ BallotRoutedSTVTerminal seats state) :
    ∃ after, BallotRoutedDFavoringSTVTransition
      (favoredParty := favoredParty) ballots quota policy seats state after := by
  classical
  have hactiveNonempty : state.active.Nonempty :=
    BallotRoutedSeatAvailability.active_nonempty_of_not_terminal
      (seats := seats) helected havailable hnotTerminal
  by_cases hquota : ∃ candidate, candidate ∈ state.active ∧
      quota ≤ ballotRoutedTally voters ballots state.active state.weight candidate
  · rcases hquota with ⟨baseWinner, hbaseWinnerActive, hbaseWinnerQuota⟩
    by_cases hfavoredTie : ∃ candidate, candidate ∈ state.active ∧
        ballotRoutedTally voters ballots state.active state.weight candidate =
          ballotRoutedTally voters ballots state.active state.weight baseWinner ∧
        candidate ∈ favoredParty
    · rcases hfavoredTie with
        ⟨winner, hwinnerActive, hwinnerTie, hwinnerFavored⟩
      have hwinnerQuota :
          quota ≤ ballotRoutedTally voters ballots state.active state.weight winner := by
        rw [hwinnerTie]
        exact hbaseWinnerQuota
      rcases policy.elect_exists state.active winner state.weight state.weight_nonneg
        hwinnerActive hwinnerQuota with ⟨afterWeight, hupdate⟩
      let after : BallotRoutedSTVState voters initialCandidates := {
        active := state.active.erase winner
        elected := insert winner state.elected
        weight := afterWeight
        active_subset_initial :=
          (Finset.erase_subset winner state.active).trans state.active_subset_initial
        elected_subset_initial := by
          intro candidate hcandidate
          rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
          · simpa [hcandidate] using state.active_subset_initial hwinnerActive
          · exact state.elected_subset_initial hcandidate
        active_elected_disjoint := by
          rw [Finset.disjoint_left]
          intro candidate hcandidateActive hcandidateElected
          rcases Finset.mem_insert.mp hcandidateElected with hcandidate | hcandidate
          · subst candidate
            exact (Finset.mem_erase.mp hcandidateActive).1 rfl
          · exact Finset.disjoint_left.mp state.active_elected_disjoint
              (Finset.mem_erase.mp hcandidateActive).2 hcandidate
        weight_nonneg := policy.elect_preserves_nonneg state.active winner state.weight
          afterWeight state.weight_nonneg hupdate }
      refine ⟨after, BallotRoutedDFavoringSTVTransition.elect winner hnotTerminal
        hwinnerActive ?_ hwinnerQuota ?_ rfl rfl hupdate⟩
      · exact Nat.lt_of_le_of_ne helected (by
          intro heq
          exact hnotTerminal (Or.inl heq))
      · intro hwinnerOutside
        exact False.elim (hwinnerOutside hwinnerFavored)
    · let winner := baseWinner
      have hwinnerActive : winner ∈ state.active := hbaseWinnerActive
      have hwinnerQuota :
          quota ≤ ballotRoutedTally voters ballots state.active state.weight winner :=
        hbaseWinnerQuota
      rcases policy.elect_exists state.active winner state.weight state.weight_nonneg
        hwinnerActive hwinnerQuota with ⟨afterWeight, hupdate⟩
      let after : BallotRoutedSTVState voters initialCandidates := {
        active := state.active.erase winner
        elected := insert winner state.elected
        weight := afterWeight
        active_subset_initial :=
          (Finset.erase_subset winner state.active).trans state.active_subset_initial
        elected_subset_initial := by
          intro candidate hcandidate
          rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
          · simpa [hcandidate] using state.active_subset_initial hwinnerActive
          · exact state.elected_subset_initial hcandidate
        active_elected_disjoint := by
          rw [Finset.disjoint_left]
          intro candidate hcandidateActive hcandidateElected
          rcases Finset.mem_insert.mp hcandidateElected with hcandidate | hcandidate
          · subst candidate
            exact (Finset.mem_erase.mp hcandidateActive).1 rfl
          · exact Finset.disjoint_left.mp state.active_elected_disjoint
              (Finset.mem_erase.mp hcandidateActive).2 hcandidate
        weight_nonneg := policy.elect_preserves_nonneg state.active winner state.weight
          afterWeight state.weight_nonneg hupdate }
      refine ⟨after, BallotRoutedDFavoringSTVTransition.elect winner hnotTerminal
        hwinnerActive ?_ hwinnerQuota ?_ rfl rfl hupdate⟩
      · exact Nat.lt_of_le_of_ne helected (by
          intro heq
          exact hnotTerminal (Or.inl heq))
      · intro hwinnerOutside candidate hcandidateActive hcandidateTie
        intro hcandidateFavored
        exact hfavoredTie
          ⟨candidate, hcandidateActive, hcandidateTie, hcandidateFavored⟩
  · have hnoQuota : ∀ candidate, candidate ∈ state.active ->
        ballotRoutedTally voters ballots state.active state.weight candidate < quota := by
      intro candidate hcandidate
      exact lt_of_not_ge (by
        intro hge
        exact hquota ⟨candidate, hcandidate, hge⟩)
    rcases Finset.exists_min_image state.active
      (ballotRoutedTally voters ballots state.active state.weight)
      hactiveNonempty with ⟨minimumLoser, hminimumLoserActive, hminimum⟩
    by_cases houtside : ∃ loser, loser ∈ state.active ∧
        (∀ candidate, candidate ∈ state.active ->
          ballotRoutedTally voters ballots state.active state.weight loser ≤
            ballotRoutedTally voters ballots state.active state.weight candidate) ∧
        loser ∉ favoredParty
    · rcases houtside with ⟨loser, hloserActive, hloserMinimum, hloserOutside⟩
      rcases policy.eliminate_exists state.active loser state.weight state.weight_nonneg
        hloserActive with ⟨afterWeight, hupdate⟩
      let after : BallotRoutedSTVState voters initialCandidates := {
        active := state.active.erase loser
        elected := state.elected
        weight := afterWeight
        active_subset_initial :=
          (Finset.erase_subset loser state.active).trans state.active_subset_initial
        elected_subset_initial := state.elected_subset_initial
        active_elected_disjoint := by
          rw [Finset.disjoint_left]
          intro candidate hcandidateActive hcandidateElected
          exact Finset.disjoint_left.mp state.active_elected_disjoint
            (Finset.mem_erase.mp hcandidateActive).2 hcandidateElected
        weight_nonneg := by
          intro voter hvoter
          rw [policy.eliminate_weight_unchanged state.active loser state.weight
            afterWeight state.weight_nonneg hupdate voter hvoter]
          exact state.weight_nonneg voter hvoter }
      refine ⟨after, BallotRoutedDFavoringSTVTransition.eliminate loser
        hnotTerminal hloserActive hnoQuota hloserMinimum ?_ rfl rfl hupdate⟩
      intro hloserFavored
      exact False.elim (hloserOutside hloserFavored)
    · rcases policy.eliminate_exists state.active minimumLoser state.weight
        state.weight_nonneg hminimumLoserActive with ⟨afterWeight, hupdate⟩
      let after : BallotRoutedSTVState voters initialCandidates := {
        active := state.active.erase minimumLoser
        elected := state.elected
        weight := afterWeight
        active_subset_initial :=
          (Finset.erase_subset minimumLoser state.active).trans
            state.active_subset_initial
        elected_subset_initial := state.elected_subset_initial
        active_elected_disjoint := by
          rw [Finset.disjoint_left]
          intro candidate hcandidateActive hcandidateElected
          exact Finset.disjoint_left.mp state.active_elected_disjoint
            (Finset.mem_erase.mp hcandidateActive).2 hcandidateElected
        weight_nonneg := by
          intro voter hvoter
          rw [policy.eliminate_weight_unchanged state.active minimumLoser state.weight
            afterWeight state.weight_nonneg hupdate voter hvoter]
          exact state.weight_nonneg voter hvoter }
      refine ⟨after, BallotRoutedDFavoringSTVTransition.eliminate minimumLoser
        hnotTerminal hminimumLoserActive hnoQuota hminimum ?_ rfl rfl hupdate⟩
      intro hminimumLoserFavored candidate hcandidateActive hcandidateTie
      by_contra hcandidateFavored
      apply houtside
      refine ⟨candidate, hcandidateActive, ?_, hcandidateFavored⟩
      intro other hotherActive
      calc
        ballotRoutedTally voters ballots state.active state.weight candidate =
            ballotRoutedTally voters ballots state.active state.weight minimumLoser :=
          hcandidateTie
        _ ≤ ballotRoutedTally voters ballots state.active state.weight other :=
          hminimum other hotherActive

/-- Every seat-available state reaches a source terminal through D-favoring steps. -/
theorem exists_ballotRoutedDFavoringSTVTerminalRun_from
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {state : BallotRoutedSTVState voters initialCandidates}
    (helected : state.elected.card ≤ seats)
    (havailable : BallotRoutedSeatAvailability (seats := seats) state) :
    ∃ terminal,
      BallotRoutedDFavoringSTVRun
          (favoredParty := favoredParty) ballots quota policy seats state terminal ∧
        BallotRoutedSTVTerminal seats terminal := by
  let P : ℕ -> Prop := fun activeCard =>
    ∀ state : BallotRoutedSTVState voters initialCandidates,
      state.active.card = activeCard ->
      state.elected.card ≤ seats ->
      BallotRoutedSeatAvailability (seats := seats) state ->
        ∃ terminal,
          BallotRoutedDFavoringSTVRun
              (favoredParty := favoredParty) ballots quota policy seats state terminal ∧
            BallotRoutedSTVTerminal seats terminal
  have hP : ∀ activeCard, P activeCard := by
    intro activeCard
    induction activeCard using Nat.strong_induction_on with
    | h activeCard ih =>
        intro current hcard hcurrentElected hcurrentAvailable
        by_cases hterminal : BallotRoutedSTVTerminal seats current
        · exact ⟨current, Relation.ReflTransGen.refl, hterminal⟩
        · rcases exists_ballotRoutedDFavoringSTVTransition_of_not_terminal
            (favoredParty := favoredParty) (policy := policy) (seats := seats)
            hcurrentElected hcurrentAvailable hterminal with ⟨after, hstep⟩
          have hgeneral := BallotRoutedDFavoringSTVTransition.refines hstep
          have hafterCardAddOne :=
            BallotRoutedSTVTransition.active_card_add_one_eq hgeneral
          have hafterLt : after.active.card < activeCard := by
            rw [hcard] at hafterCardAddOne
            omega
          have hafterElected : after.elected.card ≤ seats :=
            BallotRoutedSeatAvailability.elected_le_seats_of_transition
              (seats := seats) hcurrentElected hgeneral
          have hafterAvailable :
              BallotRoutedSeatAvailability (seats := seats) after :=
            BallotRoutedSeatAvailability.of_transition
              (seats := seats) hcurrentAvailable hgeneral
          rcases ih after.active.card hafterLt after rfl hafterElected
            hafterAvailable with ⟨terminal, hrun, hterminal⟩
          exact ⟨terminal, hrun.head hstep, hterminal⟩
  exact hP state.active.card state rfl helected havailable

/-- The unit-weight source initial state has a finite D-favoring terminal run. -/
theorem exists_ballotRoutedDFavoringSTVTerminalRun
    {voters : Finset Voter} {initialCandidates favoredParty : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    (hseats : seats ≤ initialCandidates.card)
    (initialWeight : Voter -> ℝ)
    (hweightNonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    ∃ terminal,
      BallotRoutedDFavoringSTVRun
          (favoredParty := favoredParty) ballots quota policy seats
          (BallotRoutedSTVState.initial (voters := voters)
            (initialCandidates := initialCandidates) initialWeight hweightNonneg)
          terminal ∧
        BallotRoutedSTVTerminal seats terminal := by
  apply exists_ballotRoutedDFavoringSTVTerminalRun_from
    (favoredParty := favoredParty) (policy := policy) (seats := seats)
  · simp [BallotRoutedSTVState.initial]
  · exact BallotRoutedSeatAvailability.initial
      (seats := seats) hseats initialWeight hweightNonneg

end GGRS26CombattingGerrymanderingRCV
