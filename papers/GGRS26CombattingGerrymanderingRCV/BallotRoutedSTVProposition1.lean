import GGRS26CombattingGerrymanderingRCV.MainTheorems
import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVExecution
import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVPartyInvariant

/-!
# Proposition 1 for Reachable Ballot-Routed STV

This is the replacement for the former raw-run/refinement route.  The result
below ranges over terminal executions of a ballot-level policy whose only
transfer freedom is how an elected candidate's own supporting weight is
retained or transferred.  The proof constructs every party quota invariant
from the actual transition relation.
-/

namespace GGRS26CombattingGerrymanderingRCV

open scoped BigOperators
open AppliedModelingLib.SocialChoice.Voting

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]

/-- Stop the common two-party prefix at source termination or first party exhaustion. -/
def BallotRoutedTwoPartyCutoff
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (seats : ℕ) (partyCandidates otherPartyCandidates : Finset Candidate)
    (state : BallotRoutedSTVState voters initialCandidates) : Prop :=
  BallotRoutedSTVTerminal seats state ∨
    (state.active ∩ partyCandidates).card = 0 ∨
      (state.active ∩ otherPartyCandidates).card = 0

/-- The two source quota invariants at one reachable state of the common prefix. -/
def BallotRoutedTwoPartyProjectionInvariant
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (partyVoters otherPartyVoters : Finset Voter)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (partyInitialVotes otherPartyInitialVotes quota : ℝ)
    (state : BallotRoutedSTVState voters initialCandidates) : Prop :=
  PartyQuotaInvariant partyInitialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates state) ∧
    PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates state) ∧
    PartyQuotaInvariant otherPartyInitialVotes quota
      (ballotRoutedPartyQuotaState otherPartyVoters otherPartyCandidates state) ∧
    PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState otherPartyVoters otherPartyCandidates state)

theorem ballotRoutedPartyQuotaState_initial_eq_start
    {partyVoters voters : Finset Voter} {partyCandidates initialCandidates : Finset Candidate}
    {initialWeight : Voter -> ℝ} {initialVotes : ℝ}
    (hpartyInitialActive : partyCandidates ⊆ initialCandidates)
    (hinitialMass : initialVotes = ∑ voter ∈ partyVoters, initialWeight voter)
    (hweight_nonneg : ∀ voter, voter ∈ voters -> 0 ≤ initialWeight voter) :
    ballotRoutedPartyQuotaState partyVoters partyCandidates
        (BallotRoutedSTVState.initial (voters := voters)
          (initialCandidates := initialCandidates) initialWeight hweight_nonneg) =
      PartyQuotaStartState partyCandidates.card initialVotes := by
  simp only [ballotRoutedPartyQuotaState, BallotRoutedSTVState.initial,
    PartyQuotaStartState]
  rw [Finset.inter_eq_right.mpr hpartyInitialActive, hinitialMass]
  simp [ballotRoutedPartyWeightMass]

/-- Initial unit-weight source ballots satisfy both party quota invariants. -/
theorem ballotRoutedTwoPartyProjectionInvariant_initial_unit
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {partyCandidates otherPartyCandidates initialCandidates : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyInitialActive : partyCandidates ⊆ initialCandidates)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialCandidates)
    (hpartyShareCard : partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard : (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ))
    (hvotersCard : voters = allVoters.card) :
    BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      (partyShare * (voters : ℝ)) ((1 - partyShare) * (voters : ℝ))
      (STVQuota seats voters : ℝ)
      (BallotRoutedSTVState.initial (voters := allVoters)
        (initialCandidates := initialCandidates) (fun _ : Voter => (1 : ℝ))
        (by intro voter hvoter; positivity)) := by
  let initial := BallotRoutedSTVState.initial (voters := allVoters)
    (initialCandidates := initialCandidates) (fun _ : Voter => (1 : ℝ))
    (by intro voter hvoter; positivity)
  have hpartyMass : partyShare * (voters : ℝ) =
      ∑ voter ∈ partyVoters, (fun _ : Voter => (1 : ℝ)) voter := by
    rw [hpartyShareCard]
    simp
  have hotherMass : (1 - partyShare) * (voters : ℝ) =
      ∑ voter ∈ otherPartyVoters, (fun _ : Voter => (1 : ℝ)) voter := by
    rw [hotherShareCard]
    simp
  have hpartyState :
      ballotRoutedPartyQuotaState partyVoters partyCandidates initial =
        PartyQuotaStartState partyCandidates.card (partyShare * (voters : ℝ)) :=
    ballotRoutedPartyQuotaState_initial_eq_start hpartyInitialActive hpartyMass
      (by intro voter hvoter; positivity)
  have hotherState :
      ballotRoutedPartyQuotaState otherPartyVoters otherPartyCandidates initial =
        PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ)) :=
    ballotRoutedPartyQuotaState_initial_eq_start hotherPartyInitialActive hotherMass
      (by intro voter hvoter; positivity)
  have hpartyVotes_nonneg : 0 ≤ partyShare * (voters : ℝ) := by
    positivity
  have hotherVotes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) := by
    exact mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have hpartyCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card (partyShare * (voters : ℝ))) := by
    exact partyQuotaStartCapacityBound_of_share_le_one_candidate_bound hle
      hpartyCandidates
  have hotherShare_le : 1 - partyShare ≤ 1 := by linarith
  have hotherCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) := by
    exact partyQuotaStartCapacityBound_of_share_le_one_candidate_bound hotherShare_le
      hotherPartyCandidates
  dsimp [BallotRoutedTwoPartyProjectionInvariant]
  rw [hpartyState, hotherState]
  exact ⟨PartyQuotaInvariant.start hpartyVotes_nonneg, hpartyCapacity,
    PartyQuotaInvariant.start hotherVotes_nonneg, hotherCapacity⟩

/--
The same initial quota invariants need only unit weight on the declared
electorate. Values of the Lean weight function outside `allVoters` are not
read by the ballot-routed tallies or transfer-policy laws.
-/
theorem ballotRoutedTwoPartyProjectionInvariant_initial_unit_on_voters
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {partyCandidates otherPartyCandidates initialCandidates : Finset Candidate}
    {initialWeight : Voter -> ℝ} {seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyInitialActive : partyCandidates ⊆ initialCandidates)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialCandidates)
    (hpartyShareCard : partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard : (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ))
    (hvotersCard : voters = allVoters.card)
    (hpartyUnit : ∀ voter, voter ∈ partyVoters -> initialWeight voter = 1)
    (hotherUnit : ∀ voter, voter ∈ otherPartyVoters -> initialWeight voter = 1)
    (hinitialWeightNonneg : ∀ voter, voter ∈ allVoters -> 0 ≤ initialWeight voter) :
    BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      (partyShare * (voters : ℝ)) ((1 - partyShare) * (voters : ℝ))
      (STVQuota seats voters : ℝ)
      (BallotRoutedSTVState.initial (voters := allVoters)
        (initialCandidates := initialCandidates) initialWeight hinitialWeightNonneg) := by
  let initial := BallotRoutedSTVState.initial (voters := allVoters)
    (initialCandidates := initialCandidates) initialWeight hinitialWeightNonneg
  have hpartyMass : partyShare * (voters : ℝ) =
      ∑ voter ∈ partyVoters, initialWeight voter := by
    rw [hpartyShareCard]
    symm
    calc
      ∑ voter ∈ partyVoters, initialWeight voter =
          ∑ voter ∈ partyVoters, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro voter hvoter
        exact hpartyUnit voter hvoter
      _ = (partyVoters.card : ℝ) := by simp
  have hotherMass : (1 - partyShare) * (voters : ℝ) =
      ∑ voter ∈ otherPartyVoters, initialWeight voter := by
    rw [hotherShareCard]
    symm
    calc
      ∑ voter ∈ otherPartyVoters, initialWeight voter =
          ∑ voter ∈ otherPartyVoters, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro voter hvoter
        exact hotherUnit voter hvoter
      _ = (otherPartyVoters.card : ℝ) := by simp
  have hpartyState :
      ballotRoutedPartyQuotaState partyVoters partyCandidates initial =
        PartyQuotaStartState partyCandidates.card (partyShare * (voters : ℝ)) :=
    ballotRoutedPartyQuotaState_initial_eq_start
      (initialWeight := initialWeight) hpartyInitialActive hpartyMass hinitialWeightNonneg
  have hotherState :
      ballotRoutedPartyQuotaState otherPartyVoters otherPartyCandidates initial =
        PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ)) :=
    ballotRoutedPartyQuotaState_initial_eq_start
      (initialWeight := initialWeight) hotherPartyInitialActive hotherMass hinitialWeightNonneg
  have hpartyVotes_nonneg : 0 ≤ partyShare * (voters : ℝ) := by
    positivity
  have hotherVotes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) := by
    exact mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have hpartyCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card (partyShare * (voters : ℝ))) := by
    exact partyQuotaStartCapacityBound_of_share_le_one_candidate_bound hle
      hpartyCandidates
  have hotherShare_le : 1 - partyShare ≤ 1 := by linarith
  have hotherCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) := by
    exact partyQuotaStartCapacityBound_of_share_le_one_candidate_bound hotherShare_le
      hotherPartyCandidates
  dsimp [BallotRoutedTwoPartyProjectionInvariant]
  rw [hpartyState, hotherState]
  exact ⟨PartyQuotaInvariant.start hpartyVotes_nonneg, hpartyCapacity,
    PartyQuotaInvariant.start hotherVotes_nonneg, hotherCapacity⟩

/-- A common-prefix transition preserves the focal party's quota decomposition. -/
theorem ballotRoutedPartyQuotaInvariant_of_transition
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {before after : BallotRoutedSTVState voters initialCandidates}
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partyInitialVotes : ℝ}
    (hinvariant : PartyQuotaInvariant partyInitialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates before))
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after)
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ before.active)
    (hotherActive : ∃ same, same ∈ otherPartyCandidates ∧ same ∈ before.active) :
    PartyQuotaInvariant partyInitialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates after) := by
  rcases BallotRoutedSTVTransition.partyQuotaStep_or_eq_of_transition
      htransition hvoterPartition hcandidateDisjoint hpartySolid hotherSolid
      hpartyActive hotherActive with hstep | hstutter
  · exact PartyQuotaInvariant.of_step hinvariant hstep
  · rw [hstutter]
    exact hinvariant

/-- Both party quota invariants are preserved while neither party has exhausted. -/
theorem ballotRoutedTwoPartyProjectionInvariant_of_transition
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {before after : BallotRoutedSTVState voters initialCandidates}
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partyInitialVotes otherPartyInitialVotes : ℝ}
    (hinvariant : BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      partyInitialVotes otherPartyInitialVotes quota before)
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after)
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ before.active)
    (hotherActive : ∃ same, same ∈ otherPartyCandidates ∧ same ∈ before.active) :
    BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      partyInitialVotes otherPartyInitialVotes quota after := by
  rcases hinvariant with ⟨hpartyInvariant, hpartyCapacity,
    hotherInvariant, hotherCapacity⟩
  have hpartyInvariant' := ballotRoutedPartyQuotaInvariant_of_transition
    hpartyInvariant htransition hvoterPartition hcandidateDisjoint hpartySolid
    hotherSolid hpartyActive hotherActive
  have hpartyCapacity' := BallotRoutedSTVTransition.partyQuotaCapacity_of_transition
    hpartyCapacity htransition hvoterPartition hcandidateDisjoint hpartySolid
    hotherSolid hpartyActive hotherActive
  have hvoterPartitionSymm : voters = otherPartyVoters ∪ partyVoters := by
    simpa [Finset.union_comm] using hvoterPartition
  have hcandidateDisjointSymm : Disjoint otherPartyCandidates partyCandidates :=
    hcandidateDisjoint.symm
  have hotherInvariant' := ballotRoutedPartyQuotaInvariant_of_transition
    hotherInvariant htransition hvoterPartitionSymm hcandidateDisjointSymm
    hotherSolid hpartySolid hotherActive hpartyActive
  have hotherCapacity' := BallotRoutedSTVTransition.partyQuotaCapacity_of_transition
    hotherCapacity htransition hvoterPartitionSymm hcandidateDisjointSymm
    hotherSolid hpartySolid hotherActive hpartyActive
  exact ⟨hpartyInvariant', hpartyCapacity', hotherInvariant', hotherCapacity'⟩

/-- A non-cutoff common-prefix state has an active candidate from each party. -/
theorem ballotRoutedTwoParty_active_of_not_cutoff
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seats : ℕ} {state : BallotRoutedSTVState voters initialCandidates}
  (hnotCutoff : ¬ BallotRoutedTwoPartyCutoff seats partyCandidates
      otherPartyCandidates state) :
    (∃ same, same ∈ partyCandidates ∧ same ∈ state.active) ∧
      ∃ same, same ∈ otherPartyCandidates ∧ same ∈ state.active := by
  unfold BallotRoutedTwoPartyCutoff at hnotCutoff
  push Not at hnotCutoff
  constructor
  · have hcard : 0 < (state.active ∩ partyCandidates).card :=
      Nat.pos_of_ne_zero hnotCutoff.2.1
    rcases Finset.card_pos.mp hcard with ⟨same, hsame⟩
    exact ⟨same, (Finset.mem_inter.mp hsame).2, (Finset.mem_inter.mp hsame).1⟩
  · have hcard : 0 < (state.active ∩ otherPartyCandidates).card :=
      Nat.pos_of_ne_zero hnotCutoff.2.2
    rcases Finset.card_pos.mp hcard with ⟨same, hsame⟩
    exact ⟨same, (Finset.mem_inter.mp hsame).2, (Finset.mem_inter.mp hsame).1⟩

/-- The quota projection invariant holds through every non-cutoff common prefix. -/
theorem ballotRoutedTwoPartyProjectionInvariant_of_common_prefix
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {initial cutoff : BallotRoutedSTVState voters initialCandidates}
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partyInitialVotes otherPartyInitialVotes : ℝ}
    (hinvariant : BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      partyInitialVotes otherPartyInitialVotes quota initial)
    (hprefix : Relation.ReflTransGen
      (fun before after =>
        BallotRoutedSTVTransition ballots quota policy seats before after ∧
          ¬ BallotRoutedTwoPartyCutoff seats partyCandidates otherPartyCandidates before)
      initial cutoff)
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates) :
    BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      partyInitialVotes otherPartyInitialVotes quota cutoff := by
  induction hprefix using Relation.ReflTransGen.trans_induction_on with
  | refl => exact hinvariant
  | single hstep =>
      rcases hstep with ⟨htransition, hnotCutoff⟩
      rcases ballotRoutedTwoParty_active_of_not_cutoff hnotCutoff with
        ⟨hpartyActive, hotherActive⟩
      exact ballotRoutedTwoPartyProjectionInvariant_of_transition hinvariant
        htransition hvoterPartition hcandidateDisjoint hpartySolid hotherSolid
        hpartyActive hotherActive
  | trans _ _ hleft hright =>
      exact hright (hleft hinvariant)

/-- A terminal execution has a first terminal-or-party-exhaustion cutoff. -/
theorem exists_ballotRoutedTwoPartyCutoff
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partyInitialVotes otherPartyInitialVotes : ℝ}
    (hinvariant : BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      partyInitialVotes otherPartyInitialVotes quota initial)
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal)
    (hterminal : BallotRoutedSTVTerminal seats terminal)
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates) :
    ∃ cutoff,
      Relation.ReflTransGen
          (fun before after =>
            BallotRoutedSTVTransition ballots quota policy seats before after ∧
              ¬ BallotRoutedTwoPartyCutoff seats partyCandidates
                otherPartyCandidates before)
          initial cutoff ∧
        BallotRoutedSTVRun ballots quota policy seats cutoff terminal ∧
        BallotRoutedTwoPartyCutoff seats partyCandidates otherPartyCandidates cutoff ∧
        BallotRoutedTwoPartyProjectionInvariant
          partyVoters otherPartyVoters partyCandidates otherPartyCandidates
          partyInitialVotes otherPartyInitialVotes quota cutoff := by
  let cutoffProperty : BallotRoutedSTVState voters initialCandidates -> Prop :=
    BallotRoutedTwoPartyCutoff seats partyCandidates otherPartyCandidates
  rcases reflTransGen_split_at_first
      (relation := BallotRoutedSTVTransition ballots quota policy seats)
      (P := cutoffProperty) hrun (Or.inl hterminal) with
    ⟨cutoff, hprefix, hsuffix, hcutoff⟩
  refine ⟨cutoff, hprefix, hsuffix, hcutoff, ?_⟩
  exact ballotRoutedTwoPartyProjectionInvariant_of_common_prefix hinvariant
    hprefix hvoterPartition hcandidateDisjoint hpartySolid hotherSolid

/-- Candidate exhaustion pins a party's quota-winner count to its quota floor. -/
theorem ballotRoutedPartyQuotaWinners_eq_floor_of_exhausted
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    {quota initialVotes : ℝ}
    {state : BallotRoutedSTVState voters initialCandidates}
    (hquota_pos : 0 < quota) (hinitialVotes : 0 ≤ initialVotes)
    (hinvariant : PartyQuotaInvariant initialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates state))
    (hcapacity : PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates state))
    (hexhausted : (state.active ∩ partyCandidates).card = 0) :
    (state.elected ∩ partyCandidates).card = ⌊initialVotes / quota⌋₊ := by
  let partyState := ballotRoutedPartyQuotaState partyVoters partyCandidates state
  have hlower : ⌊initialVotes / quota⌋₊ ≤ partyState.quotaWinners := by
    have h := floor_votes_div_quota_le_quotaWinners_add_remaining_of_capacityBound
      hquota_pos hinitialVotes hinvariant.1 hcapacity
    simpa [partyState, ballotRoutedPartyQuotaState, hexhausted] using h
  have hwinners_real : (partyState.quotaWinners : ℝ) ≤ initialVotes / quota := by
    rw [le_div_iff₀ hquota_pos]
    nlinarith [hinvariant.1, hinvariant.2]
  have hupper : partyState.quotaWinners ≤ ⌊initialVotes / quota⌋₊ :=
    Nat.le_floor hwinners_real
  simpa [partyState, ballotRoutedPartyQuotaState] using le_antisymm hupper hlower

/-- Once a party is exhausted, its final source output is its cutoff quota winners. -/
theorem ballotRoutedPartyFinalSeats_eq_cutoffWinners_of_exhausted
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {partyCandidates : Finset Candidate}
    {cutoff terminal : BallotRoutedSTVState voters initialCandidates}
    (hsuffix : BallotRoutedSTVRun ballots quota policy seats cutoff terminal)
    (hexhausted : (cutoff.active ∩ partyCandidates).card = 0) :
    ballotRoutedPartyFinalSeats partyCandidates seats terminal =
      (cutoff.elected ∩ partyCandidates).card := by
  have hcutoffActiveEmpty : cutoff.active ∩ partyCandidates = ∅ :=
    Finset.card_eq_zero.mp hexhausted
  have hterminalActiveEmpty : terminal.active ∩ partyCandidates = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨candidate, hcandidate⟩
    have hlineage := BallotRoutedSTVTransition.candidateLineage_of_run hsuffix
    have hcutoffActive : candidate ∈ cutoff.active :=
      hlineage.1 (Finset.mem_inter.mp hcandidate).1
    have hcutoffParty : candidate ∈ partyCandidates :=
      (Finset.mem_inter.mp hcandidate).2
    have hcutoffIntersection : candidate ∈ cutoff.active ∩ partyCandidates :=
      Finset.mem_inter.mpr ⟨hcutoffActive, hcutoffParty⟩
    simpa [hcutoffActiveEmpty] using hcutoffIntersection
  have hforward : cutoff.elected ∩ partyCandidates ⊆
      terminal.elected ∩ partyCandidates := by
    intro candidate hcandidate
    exact Finset.mem_inter.mpr
      ⟨BallotRoutedSTVTransition.elected_subset_of_run hsuffix
          (Finset.mem_inter.mp hcandidate).1,
        (Finset.mem_inter.mp hcandidate).2⟩
  have hbackward : terminal.elected ∩ partyCandidates ⊆
      cutoff.elected ∩ partyCandidates :=
    BallotRoutedSTVTransition.elected_party_subset_of_run_of_active_party_empty
      (partyCandidates := partyCandidates) hcutoffActiveEmpty hsuffix
  have helected : terminal.elected ∩ partyCandidates =
      cutoff.elected ∩ partyCandidates := Finset.Subset.antisymm hbackward hforward
  simp [ballotRoutedPartyFinalSeats, hterminalActiveEmpty, helected]

/-- A party coalition's current mass is bounded by total transferable mass. -/
theorem ballotRoutedPartyWeightMass_le_totalMass
    {voters partyVoters : Finset Voter} {initialCandidates : Finset Candidate}
    {state : BallotRoutedSTVState voters initialCandidates}
    (hpartyVoters : partyVoters ⊆ voters) :
    ballotRoutedPartyWeightMass partyVoters state.weight ≤ ballotRoutedTotalMass state := by
  unfold ballotRoutedPartyWeightMass ballotRoutedTotalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg hpartyVoters
  intro voter hvoter _
  exact state.weight_nonneg voter hvoter

/-- Unit initial weights instantiate the global quota accounting invariant. -/
theorem ballotRoutedGlobalInvariant_initial_unit
    {allVoters : Finset Voter} {initialCandidates : Finset Candidate}
    {seats voters : ℕ}
    (hvotersCard : voters = allVoters.card) :
    BallotRoutedSTVGlobalInvariant (quota := (STVQuota seats voters : ℝ))
      (voters : ℝ)
      (BallotRoutedSTVState.initial (voters := allVoters)
        (initialCandidates := initialCandidates) (fun _ : Voter => (1 : ℝ))
        (by intro voter hvoter; positivity)) := by
  unfold BallotRoutedSTVGlobalInvariant ballotRoutedTotalMass
  rw [hvotersCard]
  simp [BallotRoutedSTVState.initial]

/--
Finite-electorate unit weights instantiate the global quota accounting
invariant without constraining values outside the declared electorate.
-/
theorem ballotRoutedGlobalInvariant_initial_unit_on_voters
    {allVoters : Finset Voter} {initialCandidates : Finset Candidate}
    {initialWeight : Voter -> ℝ} {seats voters : ℕ}
    (hvotersCard : voters = allVoters.card)
    (hunit : ∀ voter, voter ∈ allVoters -> initialWeight voter = 1)
    (hinitialWeightNonneg : ∀ voter, voter ∈ allVoters -> 0 ≤ initialWeight voter) :
    BallotRoutedSTVGlobalInvariant (quota := (STVQuota seats voters : ℝ))
      (voters : ℝ)
      (BallotRoutedSTVState.initial (voters := allVoters)
        (initialCandidates := initialCandidates) initialWeight hinitialWeightNonneg) := by
  unfold BallotRoutedSTVGlobalInvariant ballotRoutedTotalMass
  rw [hvotersCard]
  simp only [BallotRoutedSTVState.initial, Finset.card_empty, Nat.cast_zero,
    zero_mul, zero_add]
  symm
  calc
    ∑ voter ∈ allVoters, initialWeight voter =
        ∑ voter ∈ allVoters, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro voter hvoter
      exact hunit voter hvoter
    _ = (allVoters.card : ℝ) := by simp

/-- At an all-quota-winners terminal state, a party's final seats meet its quota floor. -/
theorem ballotRoutedPartyFloor_le_finalSeats_of_terminal_elected
    {voters partyVoters : Finset Voter} {initialCandidates : Finset Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ} {seats : ℕ}
    {terminal : BallotRoutedSTVState voters initialCandidates}
    (hquota_pos : 0 < quota)
    (hpartyVoters : partyVoters ⊆ voters)
    (hinvariant : PartyQuotaInvariant initialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates terminal))
    (htotalResidual : ballotRoutedTotalMass terminal < quota)
    (helected : terminal.elected.card = seats) :
    ⌊initialVotes / quota⌋₊ ≤
      ballotRoutedPartyFinalSeats partyCandidates seats terminal := by
  have hpartyResidual :
      (ballotRoutedPartyQuotaState partyVoters partyCandidates terminal).voteMass < quota := by
    change ballotRoutedPartyWeightMass partyVoters terminal.weight < quota
    exact lt_of_le_of_lt
      (ballotRoutedPartyWeightMass_le_totalMass hpartyVoters) htotalResidual
  have hresidual : QuotaResidualBound
      (ballotRoutedPartyQuotaState partyVoters partyCandidates terminal).quotaWinners
      initialVotes quota :=
    ⟨hquota_pos,
      (ballotRoutedPartyQuotaState partyVoters partyCandidates terminal).voteMass,
      hinvariant.2, hpartyResidual, hinvariant.1⟩
  have hlower := floor_votes_div_quota_le_seatsElected_of_residualBound hresidual
  simpa [ballotRoutedPartyQuotaState, ballotRoutedPartyFinalSeats, helected] using hlower

/-- At a terminal fill state, the capacity invariant supplies the party floor. -/
theorem ballotRoutedPartyFloor_le_finalSeats_of_terminal_fill
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {seats : ℕ}
    {terminal : BallotRoutedSTVState voters initialCandidates}
    (hquota_pos : 0 < quota) (hinitialVotes : 0 ≤ initialVotes)
    (hinvariant : PartyQuotaInvariant initialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates terminal))
    (hcapacity : PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates terminal))
    (helected_lt : terminal.elected.card < seats) :
    ⌊initialVotes / quota⌋₊ ≤
      ballotRoutedPartyFinalSeats partyCandidates seats terminal := by
  have hlower := floor_votes_div_quota_le_quotaWinners_add_remaining_of_capacityBound
    hquota_pos hinitialVotes hinvariant.1 hcapacity
  simpa [ballotRoutedPartyQuotaState, ballotRoutedPartyFinalSeats, helected_lt] using hlower

/-- An exhausted party's final source output meets its quota floor exactly. -/
theorem ballotRoutedPartyFloor_le_finalSeats_of_exhausted
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota initialVotes : ℝ} {seats : ℕ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota}
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    {cutoff terminal : BallotRoutedSTVState voters initialCandidates}
    (hquota_pos : 0 < quota) (hinitialVotes : 0 ≤ initialVotes)
    (hinvariant : PartyQuotaInvariant initialVotes quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates cutoff))
    (hcapacity : PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates cutoff))
    (hexhausted : (cutoff.active ∩ partyCandidates).card = 0)
    (hsuffix : BallotRoutedSTVRun ballots quota policy seats cutoff terminal) :
    ⌊initialVotes / quota⌋₊ ≤
      ballotRoutedPartyFinalSeats partyCandidates seats terminal := by
  have hfloor := ballotRoutedPartyQuotaWinners_eq_floor_of_exhausted
    hquota_pos hinitialVotes hinvariant hcapacity hexhausted
  have hfinal := ballotRoutedPartyFinalSeats_eq_cutoffWinners_of_exhausted
    (policy := policy) hsuffix hexhausted
  omega

/-- The two actual party outputs always fill exactly the source's seat count. -/
theorem ballotRoutedTwoPartyFinalSeats_add
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate} {seats : ℕ}
    {terminal : BallotRoutedSTVState voters initialCandidates}
    (helected_le : terminal.elected.card ≤ seats)
    (hterminal : BallotRoutedSTVTerminal seats terminal)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hinitialSubset : initialCandidates ⊆ partyCandidates ∪ otherPartyCandidates) :
    ballotRoutedPartyFinalSeats partyCandidates seats terminal +
        ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal = seats := by
  have helectedSubset : terminal.elected ⊆ partyCandidates ∪ otherPartyCandidates :=
    terminal.elected_subset_initial.trans hinitialSubset
  have hactiveSubset : terminal.active ⊆ partyCandidates ∪ otherPartyCandidates :=
    terminal.active_subset_initial.trans hinitialSubset
  have helectedPartition :
      (terminal.elected ∩ partyCandidates).card +
          (terminal.elected ∩ otherPartyCandidates).card = terminal.elected.card := by
    simpa only [activePartyCandidates_eq_inter] using
      (activePartyCandidates_card_add_eq_card_of_subset_union_of_disjoint
        (active := terminal.elected) hcandidateDisjoint helectedSubset)
  have hactivePartition :
      (terminal.active ∩ partyCandidates).card +
          (terminal.active ∩ otherPartyCandidates).card = terminal.active.card := by
    simpa only [activePartyCandidates_eq_inter] using
      (activePartyCandidates_card_add_eq_card_of_subset_union_of_disjoint
        (active := terminal.active) hcandidateDisjoint hactiveSubset)
  by_cases helected_lt : terminal.elected.card < seats
  · rcases hterminal with helected | hfill
    · omega
    · simp only [ballotRoutedPartyFinalSeats, if_pos helected_lt]
      omega
  · have helected_eq : terminal.elected.card = seats :=
      Nat.le_antisymm helected_le (Nat.le_of_not_lt helected_lt)
    simp only [ballotRoutedPartyFinalSeats, if_neg helected_lt]
    omega

/-- A terminal source state cannot have a nontrivial outgoing ballot-routed run. -/
theorem ballotRoutedSTVTerminal_eq_of_run
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
    {start terminal : BallotRoutedSTVState voters initialCandidates}
    (hstartTerminal : BallotRoutedSTVTerminal seats start)
    (hrun : BallotRoutedSTVRun ballots quota policy seats start terminal) :
    terminal = start := by
  apply (Relation.reflTransGen_iff_eq (a := start) (b := terminal) ?_).mp hrun
  intro after htransition
  cases htransition with
  | elect _ hnotTerminal _ _ _ _ _ _ => exact hnotTerminal hstartTerminal
  | eliminate _ hnotTerminal _ _ _ _ _ _ => exact hnotTerminal hstartTerminal

/-- Global quota accounting bounds terminal transferable mass after all seats elect. -/
theorem ballotRoutedTotalMass_lt_quota_of_all_elected
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {seats : ℕ}
    {terminal : BallotRoutedSTVState voters initialCandidates}
    (hglobal : BallotRoutedSTVGlobalInvariant (quota := quota) initialVotes terminal)
    (helected : terminal.elected.card = seats)
    (hresidual : initialVotes - (seats : ℝ) * quota < quota) :
    ballotRoutedTotalMass terminal < quota := by
  unfold BallotRoutedSTVGlobalInvariant at hglobal
  rw [helected] at hglobal
  nlinarith

/--
Every terminal execution of an admitted ballot-routed transfer policy satisfies
the two source quota-floor lower bounds.  No party projection, raw outcome, or
conservation record is accepted from the caller: the common prefix is derived
from the executable transition relation above.
-/
theorem ballotRoutedSTV_twoPartyQuotaLowerBounds_of_terminalRun
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate}
    {partyCandidates otherPartyCandidates initialActive : Finset Candidate}
    {initialWeight : Voter -> ℝ} {seats voters : ℕ} {partyShare : ℝ}
    {policy : BallotRoutedSTVTransferPolicy allVoters ballots
      (STVQuota seats voters : ℝ)}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hvotersCard : voters = allVoters.card)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset : initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard : partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard : (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ))
    (hinitialWeightUnit : ∀ voter, voter ∈ allVoters -> initialWeight voter = 1)
    (hinitialWeightNonneg : ∀ voter, voter ∈ allVoters -> 0 ≤ initialWeight voter)
    {terminal : BallotRoutedSTVState allVoters initialActive}
    (hrun : BallotRoutedSTVRun ballots (STVQuota seats voters : ℝ) policy seats
      (BallotRoutedSTVState.initial (voters := allVoters)
        (initialCandidates := initialActive) initialWeight hinitialWeightNonneg) terminal)
    (hterminal : BallotRoutedSTVTerminal seats terminal) :
    ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        ballotRoutedPartyFinalSeats partyCandidates seats terminal ∧
      ⌊((1 - partyShare) * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal := by
  let initial : BallotRoutedSTVState allVoters initialActive :=
    BallotRoutedSTVState.initial (voters := allVoters)
      (initialCandidates := initialActive) initialWeight hinitialWeightNonneg
  let quota : ℝ := STVQuota seats voters
  have hquota_pos : 0 < quota := by
    dsimp [quota]
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hpartyVotes_nonneg : 0 ≤ partyShare * (voters : ℝ) := by positivity
  have hotherVotes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) := by
    exact mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have hpartyVoters : partyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left otherPartyVoters hvoter
  have hotherVoters : otherPartyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_right partyVoters hvoter
  have hinitialInvariant : BallotRoutedTwoPartyProjectionInvariant
      partyVoters otherPartyVoters partyCandidates otherPartyCandidates
      (partyShare * (voters : ℝ)) ((1 - partyShare) * (voters : ℝ)) quota initial := by
    simpa [initial, quota] using
      (ballotRoutedTwoPartyProjectionInvariant_initial_unit_on_voters
        (Voter := Voter) (Candidate := Candidate) hpos hle hpartyCandidates
        hotherPartyCandidates hpartyInitialActive hotherPartyInitialActive
        hpartyShareCard hotherShareCard hvotersCard
        (fun voter hvoter => hinitialWeightUnit voter (hpartyVoters hvoter))
        (fun voter hvoter => hinitialWeightUnit voter (hotherVoters hvoter))
        hinitialWeightNonneg)
  have hglobalInitial : BallotRoutedSTVGlobalInvariant (quota := quota)
      (voters : ℝ) initial := by
    simpa [initial, quota] using
      (ballotRoutedGlobalInvariant_initial_unit_on_voters
        (Voter := Voter) (Candidate := Candidate) (seats := seats)
        hvotersCard hinitialWeightUnit hinitialWeightNonneg)
  have helectedLe : terminal.elected.card ≤ seats := by
    simpa [initial, quota] using
      (BallotRoutedSTVTransition.elected_le_seats_of_run
        (ballots := ballots) (policy := policy) (seats := seats)
        (by simp) hrun)
  have hfloorSum :
      ⌊(partyShare * (voters : ℝ)) / quota⌋₊ +
          ⌊((1 - partyShare) * (voters : ℝ)) / quota⌋₊ ≤ seats := by
    simpa [quota, mul_div_assoc] using
      (stvTwoPartyQuotaFloors_sum_le_seats
        (seats := seats) (voters := voters) (partyShare := partyShare)
        hpos.le hle)
  rcases exists_ballotRoutedTwoPartyCutoff hinitialInvariant
      (by simpa [initial, quota] using hrun) hterminal hvoterPartition
      hcandidateDisjoint hpartySolid hotherSolid with
    ⟨cutoff, hprefix, hsuffix, hcutoff, hcutoffInvariant⟩
  rcases hcutoffInvariant with ⟨hpartyInvariant, hpartyCapacity,
    hotherInvariant, hotherCapacity⟩
  have hterminalSeatSum :
      ballotRoutedPartyFinalSeats partyCandidates seats terminal +
          ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal = seats :=
    ballotRoutedTwoPartyFinalSeats_add helectedLe hterminal hcandidateDisjoint
      hinitialActiveSubset
  by_cases hpartyExhausted : (cutoff.active ∩ partyCandidates).card = 0
  · have hpartyFloor_eq :
        (cutoff.elected ∩ partyCandidates).card =
          ⌊(partyShare * (voters : ℝ)) / quota⌋₊ :=
      ballotRoutedPartyQuotaWinners_eq_floor_of_exhausted hquota_pos
        hpartyVotes_nonneg hpartyInvariant hpartyCapacity hpartyExhausted
    have hpartyFinal_eq : ballotRoutedPartyFinalSeats partyCandidates seats terminal =
        ⌊(partyShare * (voters : ℝ)) / quota⌋₊ := by
      rw [ballotRoutedPartyFinalSeats_eq_cutoffWinners_of_exhausted
        (policy := policy) hsuffix hpartyExhausted, hpartyFloor_eq]
    have hpartyFinal_eq' : ballotRoutedPartyFinalSeats partyCandidates seats terminal =
        ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ := by
      simpa [quota] using hpartyFinal_eq
    have hfloorSum' :
        ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ +
            ⌊((1 - partyShare) * (voters : ℝ)) /
              (STVQuota seats voters : ℝ)⌋₊ ≤ seats := by
      simpa [quota] using hfloorSum
    constructor <;> omega
  by_cases hotherExhausted : (cutoff.active ∩ otherPartyCandidates).card = 0
  · have hotherFloor_eq :
        (cutoff.elected ∩ otherPartyCandidates).card =
          ⌊((1 - partyShare) * (voters : ℝ)) / quota⌋₊ :=
      ballotRoutedPartyQuotaWinners_eq_floor_of_exhausted hquota_pos
        hotherVotes_nonneg hotherInvariant hotherCapacity hotherExhausted
    have hotherFinal_eq : ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal =
        ⌊((1 - partyShare) * (voters : ℝ)) / quota⌋₊ := by
      rw [ballotRoutedPartyFinalSeats_eq_cutoffWinners_of_exhausted
        (policy := policy) hsuffix hotherExhausted, hotherFloor_eq]
    have hotherFinal_eq' : ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal =
        ⌊((1 - partyShare) * (voters : ℝ)) /
            (STVQuota seats voters : ℝ)⌋₊ := by
      simpa [quota] using hotherFinal_eq
    have hfloorSum' :
        ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ +
            ⌊((1 - partyShare) * (voters : ℝ)) /
              (STVQuota seats voters : ℝ)⌋₊ ≤ seats := by
      simpa [quota] using hfloorSum
    constructor <;> omega
  have hcutoffTerminal : BallotRoutedSTVTerminal seats cutoff := by
    rcases hcutoff with hterminalCutoff | hpartyEmpty | hotherEmpty
    · exact hterminalCutoff
    · exact False.elim (hpartyExhausted hpartyEmpty)
    · exact False.elim (hotherExhausted hotherEmpty)
  have hterminal_eq_cutoff : terminal = cutoff :=
    ballotRoutedSTVTerminal_eq_of_run hcutoffTerminal hsuffix
  subst terminal
  have hprefixRun : BallotRoutedSTVRun ballots quota policy seats initial cutoff :=
    Relation.ReflTransGen.mono (fun _ _ hstep => hstep.1) hprefix
  have hglobalCutoff : BallotRoutedSTVGlobalInvariant (quota := quota)
      (voters : ℝ) cutoff :=
    BallotRoutedSTVTransition.globalInvariant_of_run hglobalInitial hprefixRun
  have helectedLeCutoff : cutoff.elected.card ≤ seats := by
    simpa using helectedLe
  by_cases helected_lt : cutoff.elected.card < seats
  · constructor
    · exact ballotRoutedPartyFloor_le_finalSeats_of_terminal_fill hquota_pos
        hpartyVotes_nonneg hpartyInvariant hpartyCapacity helected_lt
    · exact ballotRoutedPartyFloor_le_finalSeats_of_terminal_fill hquota_pos
        hotherVotes_nonneg hotherInvariant hotherCapacity helected_lt
  · have helected_eq : cutoff.elected.card = seats :=
      Nat.le_antisymm helectedLeCutoff (Nat.le_of_not_lt helected_lt)
    have hglobalResidual : ballotRoutedTotalMass cutoff < quota := by
      apply ballotRoutedTotalMass_lt_quota_of_all_elected hglobalCutoff helected_eq
      simpa [quota] using voters_sub_seats_mul_STVQuota_lt_STVQuota seats voters
    constructor
    · exact ballotRoutedPartyFloor_le_finalSeats_of_terminal_elected hquota_pos
        hpartyVoters hpartyInvariant hglobalResidual helected_eq
    · exact ballotRoutedPartyFloor_le_finalSeats_of_terminal_elected hquota_pos
        hotherVoters hotherInvariant hglobalResidual helected_eq

/--
Source-uniform Proposition 1 over every terminal execution of a reachable
ballot-routed surplus-transfer policy.  Proposition-valued policies cover
random whole-vote transfer and the source's random within-party tie support
pathwise, without asserting a probability law.
-/
theorem proposition1_seatSharesRounded_of_ballotRoutedSTVTerminalRun_and_pavMinArgmax
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate}
    {partyCandidates otherPartyCandidates initialActive : Finset Candidate}
    {initialWeight : Voter -> ℝ} {seats voters pavSeatCount : ℕ} {partyShare : ℝ}
    {policy : BallotRoutedSTVTransferPolicy allVoters ballots
      (STVQuota seats voters : ℝ)}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hvotersCard : voters = allVoters.card)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset : initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard : partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard : (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ))
    (hinitialWeightUnit : ∀ voter, voter ∈ allVoters -> initialWeight voter = 1)
    (hinitialWeightNonneg : ∀ voter, voter ∈ allVoters -> 0 ≤ initialWeight voter)
    {terminal : BallotRoutedSTVState allVoters initialActive}
    (hrun : BallotRoutedSTVRun ballots (STVQuota seats voters : ℝ) policy seats
      (BallotRoutedSTVState.initial (voters := allVoters)
        (initialCandidates := initialActive) initialWeight hinitialWeightNonneg) terminal)
    (hterminal : BallotRoutedSTVTerminal seats terminal)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded
        (ballotRoutedPartyFinalSeats partyCandidates seats terminal)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hlower := ballotRoutedSTV_twoPartyQuotaLowerBounds_of_terminalRun
    (Voter := Voter) (Candidate := Candidate) hpos hle hvoters hpartyCandidates
    hotherPartyCandidates hpartySolid hotherSolid hvotersCard hvoterPartition
    hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
    hinitialActiveSubset hpartyShareCard hotherShareCard hinitialWeightUnit
    hinitialWeightNonneg hrun hterminal
  have helectedLe : terminal.elected.card ≤ seats := by
    exact BallotRoutedSTVTransition.elected_le_seats_of_run
      (ballots := ballots) (policy := policy) (seats := seats) (by simp) hrun
  have hfinalAdd := ballotRoutedTwoPartyFinalSeats_add helectedLe hterminal
    hcandidateDisjoint hinitialActiveSubset
  have hstv : stvSolidCoalitionQuotaLowerBounds
      (ballotRoutedPartyFinalSeats partyCandidates seats terminal)
      partyShare seats voters := by
    refine ⟨ballotRoutedPartyFinalSeats otherPartyCandidates seats terminal,
      hfinalAdd, hpos.le, hle, hvoters, ?_, ?_⟩
    · simpa [mul_div_assoc] using hlower.1
    · simpa [mul_div_assoc] using hlower.2
  exact proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax
    hpos hle hstv hpav

end GGRS26CombattingGerrymanderingRCV
