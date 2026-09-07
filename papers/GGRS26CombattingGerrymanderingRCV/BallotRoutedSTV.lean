import AppliedModelingLib.SocialChoice.Voting

open scoped BigOperators

/-!
# Reachable Ballot-Routed STV Semantics

This module gives a source-faithful operational state space for the STV
procedure used in GGRS Proposition 1.  It is intentionally separate from the
library's fractional runner: the latter fixes a proportional weight-scaling
transfer update, whereas this model permits any ballot-routed policy that
retains one quota and transfers the remaining support.

The state carries its own reachability invariants.  In particular, local
arguments below never quantify over arbitrary malformed states with negative
vote mass or candidates outside the election's initial candidate set.
-/

namespace GGRS26CombattingGerrymanderingRCV

open AppliedModelingLib.SocialChoice.Voting

/--
One reachable state of a ballot-routed STV count.  `elected` records candidate
identity, rather than only a number of elected seats, so party seat counts can
later be derived from the execution itself.
-/
structure BallotRoutedSTVState {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (initialCandidates : Finset Candidate) where
  active : Finset Candidate
  elected : Finset Candidate
  weight : Voter -> ℝ
  active_subset_initial : active ⊆ initialCandidates
  elected_subset_initial : elected ⊆ initialCandidates
  active_elected_disjoint : Disjoint active elected
  weight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ weight voter

namespace BallotRoutedSTVState

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
variable {voters : Finset Voter} {initialCandidates : Finset Candidate}

/-- Initial state for an STV count with an externally supplied nonnegative weight. -/
def initial (initialWeight : Voter -> ℝ)
    (hinitialWeight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    BallotRoutedSTVState voters initialCandidates where
  active := initialCandidates
  elected := ∅
  weight := initialWeight
  active_subset_initial := by intro candidate hcandidate; exact hcandidate
  elected_subset_initial := by simp
  active_elected_disjoint := by simp
  weight_nonneg := hinitialWeight_nonneg

@[simp] theorem initial_active (initialWeight : Voter -> ℝ)
    (hinitialWeight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    (initial (voters := voters) (initialCandidates := initialCandidates)
      initialWeight hinitialWeight_nonneg).active = initialCandidates := rfl

@[simp] theorem initial_elected (initialWeight : Voter -> ℝ)
    (hinitialWeight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    (initial (voters := voters) (initialCandidates := initialCandidates)
      initialWeight hinitialWeight_nonneg).elected = ∅ := rfl

end BallotRoutedSTVState

/-- Voters whose current first active candidate is `candidate`. -/
def ballotRoutedSupport {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter -> Ballot Candidate)
    (active : Finset Candidate) (candidate : Candidate) : Finset Voter :=
  Ballot.activeSupport voters ballots active candidate

/-- Weighted first-active tally used by the ballot-routed model. -/
def ballotRoutedTally {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter -> Ballot Candidate)
    (active : Finset Candidate) (weight : Voter -> ℝ) (candidate : Candidate) : ℝ :=
  ∑ voter ∈ ballotRoutedSupport voters ballots active candidate, weight voter

/-- The support of a tally is drawn from the declared electorate. -/
theorem ballotRoutedSupport_subset_voters {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate} :
    ballotRoutedSupport voters ballots active candidate ⊆ voters := by
  intro voter hvoter
  exact (Finset.mem_filter.mp hvoter).1

/-- Nonnegative voter weights give nonnegative ballot-routed tallies. -/
theorem ballotRoutedTally_nonneg {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {active : Finset Candidate}
    {weight : Voter -> ℝ}
    (hweight : ∀ voter, voter ∈ voters -> 0 ≤ weight voter)
    (candidate : Candidate) :
    0 ≤ ballotRoutedTally voters ballots active weight candidate := by
  dsimp [ballotRoutedTally]
  exact Finset.sum_nonneg fun voter hvoter =>
    hweight voter (ballotRoutedSupport_subset_voters hvoter)

/-- Empty current support has zero tally. -/
theorem ballotRoutedTally_eq_zero_of_support_eq_empty
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter -> Ballot Candidate}
    {active : Finset Candidate} {weight : Voter -> ℝ} {candidate : Candidate}
    (hsupport : ballotRoutedSupport voters ballots active candidate = ∅) :
    ballotRoutedTally voters ballots active weight candidate = 0 := by
  simp [ballotRoutedTally, hsupport]

/--
A transfer policy operates on voter weights, while ballot routing itself is
fixed by recomputing each tally from `Ballot.nextActive`.  Election updates may
choose how the winning support's surplus is distributed among its ballots;
they cannot modify non-supporters and must leave total transferable winning
support equal to the pre-election tally minus exactly one quota.  This covers
fractional and random-voter transfer without imposing an additional
per-supporter upper bound that the source does not state.
Every policy obligation is conditioned on nonnegative preweights, the
reachability invariant carried by `BallotRoutedSTVState`; the interface
intentionally does not demand behavior on fictitious signed-weight states.
-/
structure BallotRoutedSTVTransferPolicy {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter -> Ballot Candidate) (quota : ℝ) where
  electUpdate : Finset Candidate -> Candidate ->
    (Voter -> ℝ) -> (Voter -> ℝ) -> Prop
  eliminateUpdate : Finset Candidate -> Candidate ->
    (Voter -> ℝ) -> (Voter -> ℝ) -> Prop
  elect_exists : ∀ active winner beforeWeight,
    (∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter) ->
    winner ∈ active ->
    quota ≤ ballotRoutedTally voters ballots active beforeWeight winner ->
      ∃ afterWeight, electUpdate active winner beforeWeight afterWeight
  eliminate_exists : ∀ active loser beforeWeight,
    (∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter) ->
    loser ∈ active ->
      ∃ afterWeight, eliminateUpdate active loser beforeWeight afterWeight
  elect_preserves_nonneg : ∀ active winner beforeWeight afterWeight,
    (∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter) ->
    electUpdate active winner beforeWeight afterWeight ->
      ∀ voter, voter ∈ voters -> 0 ≤ afterWeight voter
  elect_unchanged_off_support : ∀ active winner beforeWeight afterWeight,
    (∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter) ->
    electUpdate active winner beforeWeight afterWeight ->
      ∀ voter, voter ∈ voters ->
        voter ∉ ballotRoutedSupport voters ballots active winner ->
          afterWeight voter = beforeWeight voter
  elect_support_mass_drop_exactly_quota : ∀ active winner beforeWeight afterWeight,
    (∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter) ->
    electUpdate active winner beforeWeight afterWeight ->
      (∑ voter ∈ ballotRoutedSupport voters ballots active winner, afterWeight voter) =
        (∑ voter ∈ ballotRoutedSupport voters ballots active winner, beforeWeight voter) -
          quota
  eliminate_weight_unchanged : ∀ active loser beforeWeight afterWeight,
    (∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter) ->
    eliminateUpdate active loser beforeWeight afterWeight ->
      ∀ voter, voter ∈ voters -> afterWeight voter = beforeWeight voter

/-- The source's two stopping cases, stated on a reachable ballot state. -/
def BallotRoutedSTVTerminal {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (seats : ℕ) (state : BallotRoutedSTVState voters initialCandidates) : Prop :=
  state.elected.card = seats ∨
    state.active.card = seats - state.elected.card

/--
One singleton-winner source STV transition.  Elections occur before eliminations
whenever a quota is present; an elimination is a minimum-tally candidate only
when every active candidate is below quota.  The policy supplies the only
nondeterministic part: which legal surplus transfer is used.
-/
inductive BallotRoutedSTVTransition {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (ballots : Voter -> Ballot Candidate) (quota : ℝ)
    (policy : BallotRoutedSTVTransferPolicy voters ballots quota) (seats : ℕ) :
    BallotRoutedSTVState voters initialCandidates ->
      BallotRoutedSTVState voters initialCandidates -> Prop
  | elect {before after : BallotRoutedSTVState voters initialCandidates}
      (winner : Candidate)
      (hnotTerminal : ¬ BallotRoutedSTVTerminal seats before)
      (hactive : winner ∈ before.active)
      (hroom : before.elected.card < seats)
      (hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner)
      (hafterActive : after.active = before.active.erase winner)
      (hafterElected : after.elected = insert winner before.elected)
      (hupdate : policy.electUpdate before.active winner before.weight after.weight) :
      BallotRoutedSTVTransition ballots quota policy seats before after
  | eliminate {before after : BallotRoutedSTVState voters initialCandidates}
      (loser : Candidate)
      (hnotTerminal : ¬ BallotRoutedSTVTerminal seats before)
      (hactive : loser ∈ before.active)
      (hnoQuota : ∀ candidate, candidate ∈ before.active ->
        ballotRoutedTally voters ballots before.active before.weight candidate < quota)
      (hminimum : ∀ candidate, candidate ∈ before.active ->
        ballotRoutedTally voters ballots before.active before.weight loser ≤
          ballotRoutedTally voters ballots before.active before.weight candidate)
      (hafterActive : after.active = before.active.erase loser)
      (hafterElected : after.elected = before.elected)
      (hupdate : policy.eliminateUpdate before.active loser before.weight after.weight) :
      BallotRoutedSTVTransition ballots quota policy seats before after

/-- A finite execution of the reachable ballot-routed source transition. -/
abbrev BallotRoutedSTVRun {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (ballots : Voter -> Ballot Candidate) (quota : ℝ)
    (policy : BallotRoutedSTVTransferPolicy voters ballots quota) (seats : ℕ)
    (initial terminal : BallotRoutedSTVState voters initialCandidates) : Prop :=
  Relation.ReflTransGen (BallotRoutedSTVTransition ballots quota policy seats)
    initial terminal

namespace BallotRoutedSTVTransition

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
variable {voters : Finset Voter} {initialCandidates : Finset Candidate}
variable {ballots : Voter -> Ballot Candidate} {quota : ℝ}
variable {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
variable {before after : BallotRoutedSTVState voters initialCandidates}

/-- Every source transition removes exactly its focused active candidate. -/
theorem active_card_add_one_eq
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    after.active.card + 1 = before.active.card := by
  cases htransition with
  | elect winner _ hactive _ _ hafterActive _ _ =>
      rw [hafterActive]
      exact Finset.card_erase_add_one hactive
  | eliminate loser _ hactive _ _ hafterActive _ _ =>
      rw [hafterActive]
      exact Finset.card_erase_add_one hactive

/-- Active candidates are monotone along every source transition. -/
theorem active_subset
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    after.active ⊆ before.active := by
  cases htransition with
  | elect winner _ _ _ _ hafterActive _ _ =>
      rw [hafterActive]
      exact Finset.erase_subset winner before.active
  | eliminate loser _ _ _ _ hafterActive _ _ =>
      rw [hafterActive]
      exact Finset.erase_subset loser before.active

/-- Every source transition preserves the state's voter-weight nonnegativity invariant. -/
theorem weight_nonneg
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    ∀ voter, voter ∈ voters -> 0 ≤ after.weight voter :=
  after.weight_nonneg

/-- An election transition records one additional, previously active winner. -/
theorem elected_card_succ_of_elect
    {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight} :
    after.elected.card = before.elected.card + 1 := by
  have hwinner_not_elected : winner ∉ before.elected := by
    intro hwinner_elected
    exact Finset.disjoint_left.mp before.active_elected_disjoint hactive hwinner_elected
  rw [hafterElected, Finset.card_insert_of_notMem hwinner_not_elected]

/-- An elimination leaves the elected candidate set unchanged. -/
theorem elected_eq_of_eliminate
    {loser : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : loser ∈ before.active}
    {hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota}
    {hminimum : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight loser ≤
        ballotRoutedTally voters ballots before.active before.weight candidate}
    {hafterActive : after.active = before.active.erase loser}
    {hafterElected : after.elected = before.elected}
    {hupdate : policy.eliminateUpdate before.active loser before.weight after.weight} :
    after.elected = before.elected := hafterElected

end BallotRoutedSTVTransition

/--
The party's final seat count under the source stopping convention: quota
winners, plus active candidates only in the terminal fill branch.
-/
def ballotRoutedPartyFinalSeats {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (partyCandidates : Finset Candidate) (seats : ℕ)
    (state : BallotRoutedSTVState voters initialCandidates) : ℕ :=
  (state.elected ∩ partyCandidates).card +
    if state.elected.card < seats then (state.active ∩ partyCandidates).card else 0

end GGRS26CombattingGerrymanderingRCV
