import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVGlobalInvariant

/-!
# Existence of Ballot-Routed STV Executions

The policy interface is intentionally nondeterministic, but it is not allowed
to leave a nonterminal well-formed count stuck.  This file derives the finite
terminal execution needed to make universal outcome theorems nonvacuous.
-/

namespace GGRS26CombattingGerrymanderingRCV

open AppliedModelingLib.SocialChoice.Voting

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
variable {voters : Finset Voter} {initialCandidates : Finset Candidate}
variable {ballots : Voter -> Ballot Candidate} {quota : ℝ}
variable {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}

/-- There are always enough active candidates left to fill the unfilled seats. -/
def BallotRoutedSeatAvailability
    (state : BallotRoutedSTVState voters initialCandidates) : Prop :=
  seats - state.elected.card ≤ state.active.card

namespace BallotRoutedSeatAvailability

variable {before after : BallotRoutedSTVState voters initialCandidates}

theorem initial
    (hseats : seats ≤ initialCandidates.card)
    (initialWeight : Voter -> ℝ)
    (hweight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    BallotRoutedSeatAvailability (seats := seats)
      (BallotRoutedSTVState.initial (voters := voters)
        (initialCandidates := initialCandidates) initialWeight hweight_nonneg) := by
  simpa [BallotRoutedSeatAvailability]
    using hseats

theorem elected_le_seats_of_transition
    (helected : before.elected.card ≤ seats)
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    after.elected.card ≤ seats := by
  cases htransition with
  | elect winner hnotTerminal hactive hroom hquota hafterActive hafterElected hupdate =>
      have hcard := BallotRoutedSTVTransition.elected_card_succ_of_elect
        (policy := policy) (seats := seats) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hroom := hroom) (hquota := hquota)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate)
      omega
  | eliminate loser hnotTerminal hactive hnoQuota hminimum hafterActive hafterElected hupdate =>
      simpa [hafterElected] using helected

theorem of_transition
    (havailable : BallotRoutedSeatAvailability (seats := seats) before)
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    BallotRoutedSeatAvailability (seats := seats) after := by
  cases htransition with
  | elect winner hnotTerminal hactive hroom hquota hafterActive hafterElected hupdate =>
      have hactive_card := BallotRoutedSTVTransition.active_card_add_one_eq
        (policy := policy) (seats := seats)
        (BallotRoutedSTVTransition.elect (ballots := ballots) (quota := quota)
          (policy := policy) (seats := seats) winner hnotTerminal hactive hroom hquota
          hafterActive hafterElected hupdate)
      have helected_card := BallotRoutedSTVTransition.elected_card_succ_of_elect
        (policy := policy) (seats := seats) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hroom := hroom) (hquota := hquota)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate)
      unfold BallotRoutedSeatAvailability at havailable ⊢
      omega
  | eliminate loser hnotTerminal hactive hnoQuota hminimum hafterActive hafterElected hupdate =>
      have hactive_card := BallotRoutedSTVTransition.active_card_add_one_eq
        (policy := policy) (seats := seats)
        (BallotRoutedSTVTransition.eliminate (ballots := ballots) (quota := quota)
          (policy := policy) (seats := seats) loser hnotTerminal hactive hnoQuota hminimum
          hafterActive hafterElected hupdate)
      have hnot_fill : before.active.card ≠ seats - before.elected.card := by
        intro hfill
        exact hnotTerminal (Or.inr hfill)
      unfold BallotRoutedSeatAvailability at havailable ⊢
      rw [hafterElected]
      omega

theorem active_nonempty_of_not_terminal
    (helected : before.elected.card ≤ seats)
    (havailable : BallotRoutedSeatAvailability (seats := seats) before)
    (hnotTerminal : ¬ BallotRoutedSTVTerminal seats before) :
    before.active.Nonempty := by
  by_contra hnot_nonempty
  have hempty : before.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot_nonempty
  have helected_ne : before.elected.card ≠ seats := by
    intro heq
    exact hnotTerminal (Or.inl heq)
  have helected_lt : before.elected.card < seats :=
    Nat.lt_of_le_of_ne helected helected_ne
  unfold BallotRoutedSeatAvailability at havailable
  rw [hempty] at havailable
  simp at havailable
  omega

end BallotRoutedSeatAvailability

/-- A legal source transition exists at every reachable nonterminal state. -/
theorem exists_ballotRoutedSTVTransition_of_not_terminal
    {state : BallotRoutedSTVState voters initialCandidates}
    (helected : state.elected.card ≤ seats)
    (havailable : BallotRoutedSeatAvailability (seats := seats) state)
    (hnotTerminal : ¬ BallotRoutedSTVTerminal seats state) :
    ∃ after, BallotRoutedSTVTransition ballots quota policy seats state after := by
  classical
  have hactive_nonempty : state.active.Nonempty :=
    BallotRoutedSeatAvailability.active_nonempty_of_not_terminal
      (seats := seats) helected havailable hnotTerminal
  by_cases hquota : ∃ candidate, candidate ∈ state.active ∧
      quota ≤ ballotRoutedTally voters ballots state.active state.weight candidate
  · rcases hquota with ⟨winner, hwinner_active, hwinner_quota⟩
    rcases policy.elect_exists state.active winner state.weight state.weight_nonneg
      hwinner_active hwinner_quota with ⟨afterWeight, hupdate⟩
    let after : BallotRoutedSTVState voters initialCandidates := {
      active := state.active.erase winner
      elected := insert winner state.elected
      weight := afterWeight
      active_subset_initial :=
        (Finset.erase_subset winner state.active).trans state.active_subset_initial
      elected_subset_initial := by
        intro candidate hcandidate
        rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
        · simpa [hcandidate] using state.active_subset_initial hwinner_active
        · exact state.elected_subset_initial hcandidate
      active_elected_disjoint := by
        rw [Finset.disjoint_left]
        intro candidate hcandidate_active hcandidate_elected
        rcases Finset.mem_insert.mp hcandidate_elected with hcandidate | hcandidate
        · have : candidate = winner := hcandidate
          subst candidate
          exact (Finset.mem_erase.mp hcandidate_active).1 rfl
        · exact Finset.disjoint_left.mp state.active_elected_disjoint
            (Finset.mem_erase.mp hcandidate_active).2 hcandidate
      weight_nonneg := policy.elect_preserves_nonneg state.active winner state.weight
        afterWeight state.weight_nonneg hupdate }
    refine ⟨after, BallotRoutedSTVTransition.elect winner hnotTerminal hwinner_active ?_
      hwinner_quota rfl rfl hupdate⟩
    exact Nat.lt_of_le_of_ne helected (by
      intro heq
      exact hnotTerminal (Or.inl heq))
  · have hnoQuota : ∀ candidate, candidate ∈ state.active ->
      ballotRoutedTally voters ballots state.active state.weight candidate < quota := by
      intro candidate hcandidate
      exact lt_of_not_ge (by
        intro hge
        exact hquota ⟨candidate, hcandidate, hge⟩)
    rcases Finset.exists_min_image state.active
      (ballotRoutedTally voters ballots state.active state.weight)
      hactive_nonempty with ⟨loser, hloser_active, hminimum⟩
    rcases policy.eliminate_exists state.active loser state.weight state.weight_nonneg
      hloser_active with ⟨afterWeight, hupdate⟩
    let after : BallotRoutedSTVState voters initialCandidates := {
      active := state.active.erase loser
      elected := state.elected
      weight := afterWeight
      active_subset_initial :=
        (Finset.erase_subset loser state.active).trans state.active_subset_initial
      elected_subset_initial := state.elected_subset_initial
      active_elected_disjoint := by
        rw [Finset.disjoint_left]
        intro candidate hcandidate_active hcandidate_elected
        exact Finset.disjoint_left.mp state.active_elected_disjoint
          (Finset.mem_erase.mp hcandidate_active).2 hcandidate_elected
      weight_nonneg := by
        intro voter hvoter
        rw [policy.eliminate_weight_unchanged state.active loser state.weight
          afterWeight state.weight_nonneg hupdate voter hvoter]
        exact state.weight_nonneg voter hvoter }
    refine ⟨after, BallotRoutedSTVTransition.eliminate loser hnotTerminal hloser_active
      hnoQuota hminimum rfl rfl hupdate⟩

/-- Every reachable, seat-available source count reaches a stopping state. -/
theorem exists_ballotRoutedSTVTerminalRun_from
    {state : BallotRoutedSTVState voters initialCandidates}
    (helected : state.elected.card ≤ seats)
    (havailable : BallotRoutedSeatAvailability (seats := seats) state) :
    ∃ terminal,
      BallotRoutedSTVRun ballots quota policy seats state terminal ∧
        BallotRoutedSTVTerminal seats terminal := by
  let P : ℕ -> Prop := fun activeCard =>
    ∀ state : BallotRoutedSTVState voters initialCandidates,
      state.active.card = activeCard ->
      state.elected.card ≤ seats ->
      BallotRoutedSeatAvailability (seats := seats) state ->
        ∃ terminal,
          BallotRoutedSTVRun ballots quota policy seats state terminal ∧
            BallotRoutedSTVTerminal seats terminal
  have hP : ∀ activeCard, P activeCard := by
    intro activeCard
    induction activeCard using Nat.strong_induction_on with
    | h activeCard ih =>
        intro state hcard helected havailable
        by_cases hterminal : BallotRoutedSTVTerminal seats state
        · exact ⟨state, Relation.ReflTransGen.refl, hterminal⟩
        · rcases exists_ballotRoutedSTVTransition_of_not_terminal
            (policy := policy) (seats := seats) helected havailable hterminal with
            ⟨after, htransition⟩
          have hafter_card_add_one :=
            BallotRoutedSTVTransition.active_card_add_one_eq htransition
          have hafter_lt : after.active.card < activeCard := by
            rw [hcard] at hafter_card_add_one
            omega
          have hafter_elected : after.elected.card ≤ seats :=
            BallotRoutedSeatAvailability.elected_le_seats_of_transition
              (seats := seats) helected htransition
          have hafter_available :
              BallotRoutedSeatAvailability (seats := seats) after :=
            BallotRoutedSeatAvailability.of_transition (seats := seats)
              havailable htransition
          rcases ih after.active.card hafter_lt after rfl hafter_elected
            hafter_available with ⟨terminal, hrun, hterminal⟩
          exact ⟨terminal, hrun.head htransition, hterminal⟩
  exact hP state.active.card state rfl helected havailable

/-- The source initial state admits at least one finite terminal execution. -/
theorem exists_ballotRoutedSTVTerminalRun
    (hseats : seats ≤ initialCandidates.card)
    (initialWeight : Voter -> ℝ)
    (hweight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    ∃ terminal,
      BallotRoutedSTVRun ballots quota policy seats
        (BallotRoutedSTVState.initial (voters := voters)
          (initialCandidates := initialCandidates) initialWeight hweight_nonneg)
        terminal ∧
      BallotRoutedSTVTerminal seats terminal := by
  apply exists_ballotRoutedSTVTerminalRun_from (policy := policy) (seats := seats)
  · simp [BallotRoutedSTVState.initial]
  · exact BallotRoutedSeatAvailability.initial (seats := seats) hseats
      initialWeight hweight_nonneg

namespace BallotRoutedSTVTransition

variable {before after : BallotRoutedSTVState voters initialCandidates}

/-- Lift a transition-local state property through a finite ballot-routed run. -/
theorem property_of_run
    {property : BallotRoutedSTVState voters initialCandidates -> Prop}
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    (hstep : ∀ {before after},
      BallotRoutedSTVTransition ballots quota policy seats before after ->
        property before -> property after)
    (hinitial : property initial)
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal) :
    property terminal := by
  induction hrun using Relation.ReflTransGen.trans_induction_on with
  | refl => exact hinitial
  | single htransition => exact hstep htransition hinitial
  | trans _ _ hleft hright => exact hright (hleft hinitial)

/-- The elected-seat bound is preserved throughout every executable source run. -/
theorem elected_le_seats_of_run
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    (hinitial : initial.elected.card ≤ seats)
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal) :
    terminal.elected.card ≤ seats := by
  induction hrun using Relation.ReflTransGen.trans_induction_on with
  | refl => exact hinitial
  | single htransition =>
      exact BallotRoutedSeatAvailability.elected_le_seats_of_transition
        (seats := seats) hinitial htransition
  | trans _ _ hleft hright =>
      exact hright (hleft hinitial)

/-- Active candidates and elected candidates retain a lineage to the start state. -/
def BallotRoutedCandidateLineage
    (initial state : BallotRoutedSTVState voters initialCandidates) : Prop :=
  state.active ⊆ initial.active ∧
    state.elected ⊆ initial.elected ∪ initial.active

theorem candidateLineage_of_transition
    {initial : BallotRoutedSTVState voters initialCandidates}
    (hlineage : BallotRoutedCandidateLineage initial before)
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    BallotRoutedCandidateLineage initial after := by
  rcases hlineage with ⟨hactive, helected⟩
  constructor
  · exact (active_subset htransition).trans hactive
  · cases htransition with
    | elect winner _ hwinner _ _ _ hafterElected _ =>
        rw [hafterElected]
        intro candidate hcandidate
        rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact Finset.mem_union_right _ (hactive hwinner)
        · exact helected hcandidate
    | eliminate _ _ _ _ _ _ hafterElected _ =>
        simpa [hafterElected] using helected

theorem candidateLineage_of_run
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal) :
    BallotRoutedCandidateLineage initial terminal := by
  apply property_of_run
  · intro before after htransition hlineage
    exact candidateLineage_of_transition hlineage htransition
  · exact ⟨Finset.Subset.rfl, by simp⟩
  · exact hrun

/-- Once a party has no active candidate, no later source transition can elect one. -/
theorem elected_party_subset_of_run_of_active_party_empty
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    {partyCandidates : Finset Candidate}
    (hactive_empty : initial.active ∩ partyCandidates = ∅)
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal) :
    terminal.elected ∩ partyCandidates ⊆ initial.elected ∩ partyCandidates := by
  have hlineage := candidateLineage_of_run hrun
  intro candidate hcandidate
  rcases Finset.mem_inter.mp hcandidate with ⟨helected, hparty⟩
  rcases Finset.mem_union.mp (hlineage.2 helected) with hinitial | hactive
  · exact Finset.mem_inter.mpr ⟨hinitial, hparty⟩
  · have hempty : candidate ∈ initial.active ∩ partyCandidates :=
      Finset.mem_inter.mpr ⟨hactive, hparty⟩
    rw [hactive_empty] at hempty
    simp at hempty

end BallotRoutedSTVTransition

end GGRS26CombattingGerrymanderingRCV
