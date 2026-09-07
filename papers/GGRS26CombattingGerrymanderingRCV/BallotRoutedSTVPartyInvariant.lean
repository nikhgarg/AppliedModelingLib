import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTV

open scoped BigOperators

/-!
# Party Invariants for Reachable Ballot-Routed STV

Local, source-facing facts about the reachable ballot-routed STV transition.
The lemmas in this file deliberately derive party facts from ballot routing,
solid-coalition rankings, and the transfer policy's local laws.  They do not
assume a precomputed party trace or a caller-supplied outcome.
-/

namespace GGRS26CombattingGerrymanderingRCV

open AppliedModelingLib.SocialChoice.Voting

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]

/-- The current total weight held by a specified voter coalition. -/
def ballotRoutedPartyWeightMass (partyVoters : Finset Voter)
    (weight : Voter -> ℝ) : ℝ :=
  ∑ voter ∈ partyVoters, weight voter

/-- The part of a reachable ballot state visible to one party's quota process. -/
def ballotRoutedPartyQuotaState
    {voters : Finset Voter} {initialCandidates : Finset Candidate}
    (partyVoters : Finset Voter) (partyCandidates : Finset Candidate)
    (state : BallotRoutedSTVState voters initialCandidates) : PartyQuotaState where
  remainingCandidates := (state.active ∩ partyCandidates).card
  quotaWinners := (state.elected ∩ partyCandidates).card
  voteMass := ballotRoutedPartyWeightMass partyVoters state.weight

/-- The ballot-routed tally is the library's weighted first-active tally. -/
theorem ballotRoutedTally_eq_fractionalActiveTally
    {voters : Finset Voter} {ballots : Voter -> Ballot Candidate}
    {active : Finset Candidate} {weight : Voter -> ℝ} {candidate : Candidate} :
    ballotRoutedTally voters ballots active weight candidate =
      fractionalActiveTally voters ballots weight active candidate := rfl

/-- A solid coalition gives no current support to an outside candidate while it remains active. -/
theorem ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
    {partyVoters : Finset Voter} {ballots : Voter -> Ballot Candidate}
    {partyCandidates active : Finset Candidate} {outside : Candidate}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active)
    (houtside : outside ∉ partyCandidates) :
    ballotRoutedSupport partyVoters ballots active outside = ∅ :=
  activeSupport_eq_empty_of_solidCoalitionBallots_outside
    hsolid hpartyActive houtside

/-- The corresponding outside tally is zero, for every current weight function. -/
theorem ballotRoutedTally_eq_zero_of_solidCoalitionBallots_outside
    {partyVoters : Finset Voter} {ballots : Voter -> Ballot Candidate}
    {partyCandidates active : Finset Candidate} {weight : Voter -> ℝ}
    {outside : Candidate}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active)
    (houtside : outside ∉ partyCandidates) :
    ballotRoutedTally partyVoters ballots active weight outside = 0 := by
  apply ballotRoutedTally_eq_zero_of_support_eq_empty
  exact ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
    hsolid hpartyActive houtside

/-- A weighted tally is at most the total mass of any coalition containing its support. -/
theorem ballotRoutedTally_le_partyWeightMass_of_support_subset
    {voters partyVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {active : Finset Candidate}
    {weight : Voter -> ℝ} {candidate : Candidate}
    (hpartyVoters : partyVoters ⊆ voters)
    (hweightNonneg : ∀ voter, voter ∈ voters -> 0 ≤ weight voter)
    (hsupport : ballotRoutedSupport voters ballots active candidate ⊆ partyVoters) :
    ballotRoutedTally voters ballots active weight candidate ≤
      ballotRoutedPartyWeightMass partyVoters weight := by
  unfold ballotRoutedTally ballotRoutedPartyWeightMass
  apply Finset.sum_le_sum_of_subset_of_nonneg hsupport
  intro voter hvoter _
  exact hweightNonneg voter (hpartyVoters hvoter)

/-- Every party-local tally is bounded by the party's current total voter mass. -/
theorem ballotRoutedTally_le_partyWeightMass
    {partyVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {active : Finset Candidate}
    {weight : Voter -> ℝ} {candidate : Candidate}
    (hweightNonneg : ∀ voter, voter ∈ partyVoters -> 0 ≤ weight voter) :
    ballotRoutedTally partyVoters ballots active weight candidate ≤
      ballotRoutedPartyWeightMass partyVoters weight := by
  apply ballotRoutedTally_le_partyWeightMass_of_support_subset
    (voters := partyVoters) (partyVoters := partyVoters) (ballots := ballots)
    (active := active) (weight := weight) (candidate := candidate)
  · exact fun _ hvoter => hvoter
  · exact hweightNonneg
  · exact ballotRoutedSupport_subset_voters

/--
While a solid coalition has an active party candidate, the sum of all of its
active party tallies is exactly its current total voter weight.
-/
theorem ballotRoutedPartyTallyMass_eq_weightMass_of_solidCoalition
    {partyVoters : Finset Voter} {ballots : Voter -> Ballot Candidate}
    {weight : Voter -> ℝ} {active partyCandidates : Finset Candidate}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active) :
    (∑ candidate ∈ activePartyCandidates active partyCandidates,
      ballotRoutedTally partyVoters ballots active weight candidate) =
        ballotRoutedPartyWeightMass partyVoters weight := by
  exact partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights_of_solidCoalition
    (voters := partyVoters) (ballots := ballots) (weight := weight)
    (active := active) (partyCandidates := partyCandidates) hsolid hpartyActive

/--
With two disjoint solid coalitions still active, a candidate of the left party
gets all of its global tally from left-party voters.
-/
theorem ballotRoutedTally_eq_left_of_twoPartySolidCoalitions
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {weight : Voter -> ℝ}
    {active leftCandidates rightCandidates : Finset Candidate}
    {candidate : Candidate}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hvoterDisjoint : Disjoint leftVoters rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hleftSolid : SolidCoalitionBallots leftVoters ballots leftCandidates)
    (hrightSolid : SolidCoalitionBallots rightVoters ballots rightCandidates)
    (hrightActive : ∃ same, same ∈ rightCandidates ∧ same ∈ active)
    (hcandidateLeft : candidate ∈ leftCandidates) :
    ballotRoutedTally allVoters ballots active weight candidate =
      ballotRoutedTally leftVoters ballots active weight candidate := by
  rw [ballotRoutedTally_eq_fractionalActiveTally,
    ballotRoutedTally_eq_fractionalActiveTally]
  apply fractionalActiveTally_eq_left_of_union_right_support_empty
    hvoterPartition hvoterDisjoint
  · exact activeSupport_eq_empty_of_solidCoalitionBallots_outside
      hrightSolid hrightActive (by
        intro hcandidateRight
        exact (Finset.disjoint_left.mp hcandidateDisjoint)
          hcandidateLeft hcandidateRight)
  · intro voter _
    rfl

/-- The symmetric global-tally decomposition for a candidate of the right party. -/
theorem ballotRoutedTally_eq_right_of_twoPartySolidCoalitions
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {weight : Voter -> ℝ}
    {active leftCandidates rightCandidates : Finset Candidate}
    {candidate : Candidate}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hvoterDisjoint : Disjoint leftVoters rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hleftSolid : SolidCoalitionBallots leftVoters ballots leftCandidates)
    (hrightSolid : SolidCoalitionBallots rightVoters ballots rightCandidates)
    (hleftActive : ∃ same, same ∈ leftCandidates ∧ same ∈ active)
    (hcandidateRight : candidate ∈ rightCandidates) :
    ballotRoutedTally allVoters ballots active weight candidate =
      ballotRoutedTally rightVoters ballots active weight candidate := by
  rw [ballotRoutedTally_eq_fractionalActiveTally,
    ballotRoutedTally_eq_fractionalActiveTally]
  apply fractionalActiveTally_eq_right_of_union_left_support_empty
    hvoterPartition hvoterDisjoint
  · exact activeSupport_eq_empty_of_solidCoalitionBallots_outside
      hleftSolid hleftActive (by
        intro hcandidateLeft
        exact (Finset.disjoint_left.mp hcandidateDisjoint)
          hcandidateLeft hcandidateRight)
  · intro voter _
    rfl

/-- Restricting a global support set to a voter subcoalition is the subcoalition's support set. -/
theorem ballotRoutedSupport_inter_eq_of_subset
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hpartyVoters : partyVoters ⊆ allVoters) :
    ballotRoutedSupport allVoters ballots active candidate ∩ partyVoters =
      ballotRoutedSupport partyVoters ballots active candidate := by
  ext voter
  constructor
  · intro hvoter
    rcases Finset.mem_inter.mp hvoter with ⟨hsupport, hparty⟩
    exact Finset.mem_filter.mpr ⟨hparty, (Finset.mem_filter.mp hsupport).2⟩
  · intro hvoter
    rcases Finset.mem_filter.mp hvoter with ⟨hparty, hnext⟩
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_filter.mpr ⟨hpartyVoters hparty, hnext⟩, hparty⟩

/--
An election update preserves the total weight of any coalition whose voters do
not support the elected candidate in the pre-election state.
-/
theorem ballotRoutedPartyWeightMass_eq_of_elect_off_support
    {voters partyVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota}
    {active : Finset Candidate} {winner : Candidate}
    {beforeWeight afterWeight : Voter -> ℝ}
    (hpartyVoters : partyVoters ⊆ voters)
    (hweight : ∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.electUpdate active winner beforeWeight afterWeight)
    (hoffSupport : ∀ voter, voter ∈ partyVoters ->
      voter ∉ ballotRoutedSupport voters ballots active winner) :
    ballotRoutedPartyWeightMass partyVoters afterWeight =
      ballotRoutedPartyWeightMass partyVoters beforeWeight := by
  unfold ballotRoutedPartyWeightMass
  apply Finset.sum_congr rfl
  intro voter hvoter
  exact policy.elect_unchanged_off_support active winner beforeWeight afterWeight
    hweight hupdate voter (hpartyVoters hvoter) (hoffSupport voter hvoter)

/--
If all pre-election support of a winner lies in a coalition, election removes
exactly one quota from that coalition's total weight.
-/
theorem ballotRoutedPartyWeightMass_after_elect_eq_sub_quota_of_support_subset
    {voters partyVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota}
    {active : Finset Candidate} {winner : Candidate}
    {beforeWeight afterWeight : Voter -> ℝ}
    (hpartyVoters : partyVoters ⊆ voters)
    (hweight : ∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.electUpdate active winner beforeWeight afterWeight)
    (hsupport : ballotRoutedSupport voters ballots active winner ⊆ partyVoters) :
    ballotRoutedPartyWeightMass partyVoters afterWeight =
      ballotRoutedPartyWeightMass partyVoters beforeWeight - quota := by
  let support := ballotRoutedSupport voters ballots active winner
  have hafterSplit :
      (∑ voter ∈ partyVoters, afterWeight voter) =
        (∑ voter ∈ support, afterWeight voter) +
          ∑ voter ∈ partyVoters \ support, afterWeight voter := by
    simpa only [support, add_comm] using
      (Finset.sum_sdiff (f := afterWeight) hsupport).symm
  have hbeforeSplit :
      (∑ voter ∈ partyVoters, beforeWeight voter) =
        (∑ voter ∈ support, beforeWeight voter) +
          ∑ voter ∈ partyVoters \ support, beforeWeight voter := by
    simpa only [support, add_comm] using
      (Finset.sum_sdiff (f := beforeWeight) hsupport).symm
  have hcomplement :
      (∑ voter ∈ partyVoters \ support, afterWeight voter) =
        ∑ voter ∈ partyVoters \ support, beforeWeight voter := by
    apply Finset.sum_congr rfl
    intro voter hvoter
    exact policy.elect_unchanged_off_support active winner beforeWeight afterWeight
      hweight hupdate voter (hpartyVoters (Finset.mem_sdiff.mp hvoter).1)
        (Finset.mem_sdiff.mp hvoter).2
  have hsupportDrop :
      (∑ voter ∈ support, afterWeight voter) =
        (∑ voter ∈ support, beforeWeight voter) - quota :=
    policy.elect_support_mass_drop_exactly_quota active winner beforeWeight
      afterWeight hweight hupdate
  unfold ballotRoutedPartyWeightMass
  calc
    (∑ voter ∈ partyVoters, afterWeight voter) =
        (∑ voter ∈ support, afterWeight voter) +
          ∑ voter ∈ partyVoters \ support, afterWeight voter := hafterSplit
    _ = ((∑ voter ∈ support, beforeWeight voter) - quota) +
          ∑ voter ∈ partyVoters \ support, beforeWeight voter := by
      rw [hsupportDrop, hcomplement]
    _ = ((∑ voter ∈ support, beforeWeight voter) +
          ∑ voter ∈ partyVoters \ support, beforeWeight voter) - quota := by ring
    _ = (∑ voter ∈ partyVoters, beforeWeight voter) - quota := by
      rw [← hbeforeSplit]

/-- Elimination leaves every coalition's total voter weight unchanged. -/
theorem ballotRoutedPartyWeightMass_eq_of_eliminate
    {voters partyVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy voters ballots quota}
    {active : Finset Candidate} {loser : Candidate}
    {beforeWeight afterWeight : Voter -> ℝ}
    (hpartyVoters : partyVoters ⊆ voters)
    (hweight : ∀ voter, voter ∈ voters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.eliminateUpdate active loser beforeWeight afterWeight) :
    ballotRoutedPartyWeightMass partyVoters afterWeight =
      ballotRoutedPartyWeightMass partyVoters beforeWeight := by
  unfold ballotRoutedPartyWeightMass
  apply Finset.sum_congr rfl
  intro voter hvoter
  exact policy.eliminate_weight_unchanged active loser beforeWeight afterWeight
    hweight hupdate voter (hpartyVoters hvoter)

/--
In a two-party solid-coalition profile, all global support for a left-party
candidate belongs to left voters while the right party remains active.
-/
theorem ballotRoutedSupport_subset_left_of_twoPartySolidCoalitions
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate}
    {active leftCandidates rightCandidates : Finset Candidate}
    {candidate : Candidate}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hrightSolid : SolidCoalitionBallots rightVoters ballots rightCandidates)
    (hrightActive : ∃ same, same ∈ rightCandidates ∧ same ∈ active)
    (hcandidateLeft : candidate ∈ leftCandidates) :
    ballotRoutedSupport allVoters ballots active candidate ⊆ leftVoters := by
  intro voter hvoter
  have hvoterAll : voter ∈ allVoters :=
    (Finset.mem_filter.mp hvoter).1
  rw [hvoterPartition] at hvoterAll
  rcases Finset.mem_union.mp hvoterAll with hvoterLeft | hvoterRight
  · exact hvoterLeft
  · have hrightEmpty :
        ballotRoutedSupport rightVoters ballots active candidate = ∅ :=
      ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
        hrightSolid hrightActive (by
          intro hcandidateRight
          exact (Finset.disjoint_left.mp hcandidateDisjoint)
            hcandidateLeft hcandidateRight)
    have hrightSupport :
        voter ∈ ballotRoutedSupport rightVoters ballots active candidate :=
      Finset.mem_filter.mpr ⟨hvoterRight, (Finset.mem_filter.mp hvoter).2⟩
    rw [hrightEmpty] at hrightSupport
    simp at hrightSupport

/-- Symmetric support containment for a right-party candidate. -/
theorem ballotRoutedSupport_subset_right_of_twoPartySolidCoalitions
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate}
    {active leftCandidates rightCandidates : Finset Candidate}
    {candidate : Candidate}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hleftSolid : SolidCoalitionBallots leftVoters ballots leftCandidates)
    (hleftActive : ∃ same, same ∈ leftCandidates ∧ same ∈ active)
    (hcandidateRight : candidate ∈ rightCandidates) :
    ballotRoutedSupport allVoters ballots active candidate ⊆ rightVoters := by
  intro voter hvoter
  have hvoterAll : voter ∈ allVoters :=
    (Finset.mem_filter.mp hvoter).1
  rw [hvoterPartition] at hvoterAll
  rcases Finset.mem_union.mp hvoterAll with hvoterLeft | hvoterRight
  · have hleftEmpty :
        ballotRoutedSupport leftVoters ballots active candidate = ∅ :=
      ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
        hleftSolid hleftActive (by
          intro hcandidateLeft
          exact (Finset.disjoint_left.mp hcandidateDisjoint)
            hcandidateLeft hcandidateRight)
    have hleftSupport :
        voter ∈ ballotRoutedSupport leftVoters ballots active candidate :=
      Finset.mem_filter.mpr ⟨hvoterLeft, (Finset.mem_filter.mp hvoter).2⟩
    rw [hleftEmpty] at hleftSupport
    simp at hleftSupport
  · exact hvoterRight

/-- A left-party election removes exactly one quota from left-party voter mass. -/
theorem ballotRoutedLeftPartyWeightMass_after_elect_eq_sub_quota
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy allVoters ballots quota}
    {active leftCandidates rightCandidates : Finset Candidate}
    {winner : Candidate} {beforeWeight afterWeight : Voter -> ℝ}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hrightSolid : SolidCoalitionBallots rightVoters ballots rightCandidates)
    (hrightActive : ∃ same, same ∈ rightCandidates ∧ same ∈ active)
    (hwinnerLeft : winner ∈ leftCandidates)
    (hweight : ∀ voter, voter ∈ allVoters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.electUpdate active winner beforeWeight afterWeight) :
    ballotRoutedPartyWeightMass leftVoters afterWeight =
      ballotRoutedPartyWeightMass leftVoters beforeWeight - quota := by
  have hleftVoters : leftVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left rightVoters hvoter
  exact ballotRoutedPartyWeightMass_after_elect_eq_sub_quota_of_support_subset
    hleftVoters hweight hupdate
      (ballotRoutedSupport_subset_left_of_twoPartySolidCoalitions
        hvoterPartition hcandidateDisjoint hrightSolid hrightActive hwinnerLeft)

/-- A right-party election removes exactly one quota from right-party voter mass. -/
theorem ballotRoutedRightPartyWeightMass_after_elect_eq_sub_quota
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy allVoters ballots quota}
    {active leftCandidates rightCandidates : Finset Candidate}
    {winner : Candidate} {beforeWeight afterWeight : Voter -> ℝ}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hleftSolid : SolidCoalitionBallots leftVoters ballots leftCandidates)
    (hleftActive : ∃ same, same ∈ leftCandidates ∧ same ∈ active)
    (hwinnerRight : winner ∈ rightCandidates)
    (hweight : ∀ voter, voter ∈ allVoters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.electUpdate active winner beforeWeight afterWeight) :
    ballotRoutedPartyWeightMass rightVoters afterWeight =
      ballotRoutedPartyWeightMass rightVoters beforeWeight - quota := by
  have hrightVoters : rightVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_right leftVoters hvoter
  exact ballotRoutedPartyWeightMass_after_elect_eq_sub_quota_of_support_subset
    hrightVoters hweight hupdate
      (ballotRoutedSupport_subset_right_of_twoPartySolidCoalitions
        hvoterPartition hcandidateDisjoint hleftSolid hleftActive hwinnerRight)

/-- A right-party election leaves left-party voter mass unchanged while the left party is active. -/
theorem ballotRoutedLeftPartyWeightMass_eq_of_rightPartyElect
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy allVoters ballots quota}
    {active leftCandidates rightCandidates : Finset Candidate}
    {winner : Candidate} {beforeWeight afterWeight : Voter -> ℝ}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hleftSolid : SolidCoalitionBallots leftVoters ballots leftCandidates)
    (hleftActive : ∃ same, same ∈ leftCandidates ∧ same ∈ active)
    (hwinnerRight : winner ∈ rightCandidates)
    (hweight : ∀ voter, voter ∈ allVoters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.electUpdate active winner beforeWeight afterWeight) :
    ballotRoutedPartyWeightMass leftVoters afterWeight =
      ballotRoutedPartyWeightMass leftVoters beforeWeight := by
  have hleftVoters : leftVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left rightVoters hvoter
  apply ballotRoutedPartyWeightMass_eq_of_elect_off_support hleftVoters hweight hupdate
  intro voter hvoterLeft hvoterSupport
  have hleftEmpty :
      ballotRoutedSupport leftVoters ballots active winner = ∅ :=
    ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
      hleftSolid hleftActive (by
        intro hwinnerLeft
        exact (Finset.disjoint_left.mp hcandidateDisjoint)
          hwinnerLeft hwinnerRight)
  have hleftSupport :
      voter ∈ ballotRoutedSupport leftVoters ballots active winner :=
    Finset.mem_filter.mpr ⟨hvoterLeft, (Finset.mem_filter.mp hvoterSupport).2⟩
  rw [hleftEmpty] at hleftSupport
  simp at hleftSupport

/-- Symmetric unchanged-mass fact for the right party during a left-party election. -/
theorem ballotRoutedRightPartyWeightMass_eq_of_leftPartyElect
    {allVoters leftVoters rightVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate} {quota : ℝ}
    {policy : BallotRoutedSTVTransferPolicy allVoters ballots quota}
    {active leftCandidates rightCandidates : Finset Candidate}
    {winner : Candidate} {beforeWeight afterWeight : Voter -> ℝ}
    (hvoterPartition : allVoters = leftVoters ∪ rightVoters)
    (hcandidateDisjoint : Disjoint leftCandidates rightCandidates)
    (hrightSolid : SolidCoalitionBallots rightVoters ballots rightCandidates)
    (hrightActive : ∃ same, same ∈ rightCandidates ∧ same ∈ active)
    (hwinnerLeft : winner ∈ leftCandidates)
    (hweight : ∀ voter, voter ∈ allVoters -> 0 ≤ beforeWeight voter)
    (hupdate : policy.electUpdate active winner beforeWeight afterWeight) :
    ballotRoutedPartyWeightMass rightVoters afterWeight =
      ballotRoutedPartyWeightMass rightVoters beforeWeight := by
  have hrightVoters : rightVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_right leftVoters hvoter
  apply ballotRoutedPartyWeightMass_eq_of_elect_off_support hrightVoters hweight hupdate
  intro voter hvoterRight hvoterSupport
  have hrightEmpty :
      ballotRoutedSupport rightVoters ballots active winner = ∅ :=
    ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
      hrightSolid hrightActive (by
        intro hwinnerRight
        exact (Finset.disjoint_left.mp hcandidateDisjoint)
          hwinnerLeft hwinnerRight)
  have hrightSupport :
      voter ∈ ballotRoutedSupport rightVoters ballots active winner :=
    Finset.mem_filter.mpr ⟨hvoterRight, (Finset.mem_filter.mp hvoterSupport).2⟩
  rw [hrightEmpty] at hrightSupport
  simp at hrightSupport

namespace BallotRoutedSTVTransition

variable {voters : Finset Voter} {initialCandidates : Finset Candidate}
variable {ballots : Voter -> Ballot Candidate} {quota : ℝ}
variable {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}
variable {before after : BallotRoutedSTVState voters initialCandidates}

/-- Erasing a party candidate removes exactly one active party candidate. -/
theorem active_party_card_succ_of_elect
    {partyCandidates : Finset Candidate} {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight}
    (hwinnerParty : winner ∈ partyCandidates) :
    (after.active ∩ partyCandidates).card + 1 =
      (before.active ∩ partyCandidates).card := by
  rw [hafterActive, Finset.erase_inter]
  exact Finset.card_erase_add_one (by simp [hactive, hwinnerParty])

/-- Electing outside a party leaves its active-candidate set unchanged. -/
theorem active_party_eq_of_elect_outside
    {partyCandidates : Finset Candidate} {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight}
    (hwinnerOutside : winner ∉ partyCandidates) :
    after.active ∩ partyCandidates = before.active ∩ partyCandidates := by
  rw [hafterActive, Finset.erase_inter]
  exact Finset.erase_eq_of_notMem (by
    intro hwinner
    exact hwinnerOutside (Finset.mem_inter.mp hwinner).2)

/-- Electing a party candidate adds exactly one elected party candidate. -/
theorem elected_party_card_succ_of_elect
    {partyCandidates : Finset Candidate} {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight}
    (hwinnerParty : winner ∈ partyCandidates) :
    (after.elected ∩ partyCandidates).card =
      (before.elected ∩ partyCandidates).card + 1 := by
  have hwinnerNotElected : winner ∉ before.elected := by
    intro hwinnerElected
    exact Finset.disjoint_left.mp before.active_elected_disjoint hactive hwinnerElected
  rw [hafterElected]
  have hinter : (insert winner before.elected) ∩ partyCandidates =
      insert winner (before.elected ∩ partyCandidates) := by
    ext candidate
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hcandidate | hcandidate, hparty⟩
      · exact Or.inl hcandidate
      · exact Or.inr ⟨hcandidate, hparty⟩
    · intro hcandidate
      rcases hcandidate with hcandidate | ⟨helected, hparty⟩
      · exact ⟨Or.inl hcandidate, by simpa [hcandidate] using hwinnerParty⟩
      · exact ⟨Or.inr helected, hparty⟩
  rw [hinter]
  exact Finset.card_insert_of_notMem (by simp [hwinnerNotElected])

/-- Electing outside a party leaves its elected-candidate set unchanged. -/
theorem elected_party_eq_of_elect_outside
    {partyCandidates : Finset Candidate} {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight}
    (hwinnerOutside : winner ∉ partyCandidates) :
    after.elected ∩ partyCandidates = before.elected ∩ partyCandidates := by
  rw [hafterElected]
  ext candidate
  simp [hwinnerOutside]

/-- Eliminating a party candidate removes exactly one active party candidate. -/
theorem active_party_card_succ_of_eliminate
    {partyCandidates : Finset Candidate} {loser : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : loser ∈ before.active}
    {hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota}
    {hminimum : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight loser <=
        ballotRoutedTally voters ballots before.active before.weight candidate}
    {hafterActive : after.active = before.active.erase loser}
    {hafterElected : after.elected = before.elected}
    {hupdate : policy.eliminateUpdate before.active loser before.weight after.weight}
    (hloserParty : loser ∈ partyCandidates) :
    (after.active ∩ partyCandidates).card + 1 =
      (before.active ∩ partyCandidates).card := by
  rw [hafterActive, Finset.erase_inter]
  exact Finset.card_erase_add_one (by simp [hactive, hloserParty])

/-- Eliminating outside a party leaves its active-candidate set unchanged. -/
theorem active_party_eq_of_eliminate_outside
    {partyCandidates : Finset Candidate} {loser : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : loser ∈ before.active}
    {hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota}
    {hminimum : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight loser <=
        ballotRoutedTally voters ballots before.active before.weight candidate}
    {hafterActive : after.active = before.active.erase loser}
    {hafterElected : after.elected = before.elected}
    {hupdate : policy.eliminateUpdate before.active loser before.weight after.weight}
    (hloserOutside : loser ∉ partyCandidates) :
    after.active ∩ partyCandidates = before.active ∩ partyCandidates := by
  rw [hafterActive, Finset.erase_inter]
  exact Finset.erase_eq_of_notMem (by
    intro hloser
    exact hloserOutside (Finset.mem_inter.mp hloser).2)

/-- Every elimination preserves the party's elected-candidate set. -/
theorem elected_party_eq_of_eliminate
    {partyCandidates : Finset Candidate} {loser : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : loser ∈ before.active}
    {hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota}
    {hminimum : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight loser <=
        ballotRoutedTally voters ballots before.active before.weight candidate}
    {hafterActive : after.active = before.active.erase loser}
    {hafterElected : after.elected = before.elected}
    {hupdate : policy.eliminateUpdate before.active loser before.weight after.weight} :
    after.elected ∩ partyCandidates = before.elected ∩ partyCandidates := by
  rw [hafterElected]

/--
Eliminating a party candidate induces one ordinary elimination in that party's
quota projection.
-/
theorem partyQuotaEliminateStep_of_eliminate
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    {loser : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : loser ∈ before.active}
    {hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota}
    {hminimum : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight loser <=
        ballotRoutedTally voters ballots before.active before.weight candidate}
    {hafterActive : after.active = before.active.erase loser}
    {hafterElected : after.elected = before.elected}
    {hupdate : policy.eliminateUpdate before.active loser before.weight after.weight}
    (hpartyVoters : partyVoters ⊆ voters)
    (hloserParty : loser ∈ partyCandidates) :
    PartyQuotaEliminateStep quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates before)
      (ballotRoutedPartyQuotaState partyVoters partyCandidates after) := by
  refine ⟨?_, ?_, ?_⟩
  · exact active_party_card_succ_of_eliminate
      (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
      (hactive := hactive) (hnoQuota := hnoQuota) (hminimum := hminimum)
      (hafterActive := hafterActive) (hafterElected := hafterElected)
      (hupdate := hupdate) hloserParty
  · exact congrArg Finset.card
      (elected_party_eq_of_eliminate
        (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hnoQuota := hnoQuota) (hminimum := hminimum)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate))
  · exact ballotRoutedPartyWeightMass_eq_of_eliminate hpartyVoters
      before.weight_nonneg hupdate

/--
While the other solid coalition remains active, electing a party candidate
induces one ordinary quota election in that party's projection.
-/
theorem partyQuotaElectStep_of_elect
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight}
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hotherActive : ∃ same, same ∈ otherPartyCandidates ∧ same ∈ before.active)
    (hwinnerParty : winner ∈ partyCandidates) :
    PartyQuotaElectStep quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates before)
      (ballotRoutedPartyQuotaState partyVoters partyCandidates after) := by
  have hpartyVoters : partyVoters ⊆ voters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left otherPartyVoters hvoter
  have hsupport :
      ballotRoutedSupport voters ballots before.active winner ⊆ partyVoters :=
    ballotRoutedSupport_subset_left_of_twoPartySolidCoalitions
      hvoterPartition hcandidateDisjoint hotherSolid hotherActive hwinnerParty
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans hquota
      (ballotRoutedTally_le_partyWeightMass_of_support_subset
        hpartyVoters before.weight_nonneg hsupport)
  · exact active_party_card_succ_of_elect
      (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
      (hactive := hactive) (hroom := hroom) (hquota := hquota)
      (hafterActive := hafterActive) (hafterElected := hafterElected)
      (hupdate := hupdate) hwinnerParty
  · exact elected_party_card_succ_of_elect
      (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
      (hactive := hactive) (hroom := hroom) (hquota := hquota)
      (hafterActive := hafterActive) (hafterElected := hafterElected)
      (hupdate := hupdate) hwinnerParty
  · exact ballotRoutedLeftPartyWeightMass_after_elect_eq_sub_quota
      hvoterPartition hcandidateDisjoint hotherSolid hotherActive hwinnerParty
        before.weight_nonneg hupdate

/-- An election of an outside candidate is a stuttering step in this party's projection. -/
theorem partyQuotaState_eq_of_elect_outside
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight}
    (hpartyVoters : partyVoters ⊆ voters)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ before.active)
    (hwinnerOutside : winner ∉ partyCandidates) :
    ballotRoutedPartyQuotaState partyVoters partyCandidates after =
      ballotRoutedPartyQuotaState partyVoters partyCandidates before := by
  have hremaining :
      (after.active ∩ partyCandidates).card =
        (before.active ∩ partyCandidates).card :=
    congrArg Finset.card
      (active_party_eq_of_elect_outside
        (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hroom := hroom) (hquota := hquota)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate) hwinnerOutside)
  have hwinners :
      (after.elected ∩ partyCandidates).card =
        (before.elected ∩ partyCandidates).card :=
    congrArg Finset.card
      (elected_party_eq_of_elect_outside
        (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hroom := hroom) (hquota := hquota)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate) hwinnerOutside)
  have hmass : ballotRoutedPartyWeightMass partyVoters after.weight =
      ballotRoutedPartyWeightMass partyVoters before.weight :=
    ballotRoutedPartyWeightMass_eq_of_elect_off_support hpartyVoters
      before.weight_nonneg hupdate
      (by
        intro voter hvoter hsupport
        have hempty :
            ballotRoutedSupport partyVoters ballots before.active winner = ∅ :=
          ballotRoutedSupport_eq_empty_of_solidCoalitionBallots_outside
            hpartySolid hpartyActive hwinnerOutside
        have hpartySupport :
            voter ∈ ballotRoutedSupport partyVoters ballots before.active winner :=
          Finset.mem_filter.mpr
            ⟨hvoter, (Finset.mem_filter.mp hsupport).2⟩
        rw [hempty] at hpartySupport
        simp at hpartySupport)
  simp only [ballotRoutedPartyQuotaState]
  rw [hremaining, hwinners, hmass]

/-- An outside elimination is a stuttering step in this party's projection. -/
theorem partyQuotaState_eq_of_eliminate_outside
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    {loser : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : loser ∈ before.active}
    {hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota}
    {hminimum : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight loser <=
        ballotRoutedTally voters ballots before.active before.weight candidate}
    {hafterActive : after.active = before.active.erase loser}
    {hafterElected : after.elected = before.elected}
    {hupdate : policy.eliminateUpdate before.active loser before.weight after.weight}
    (hpartyVoters : partyVoters ⊆ voters)
    (hloserOutside : loser ∉ partyCandidates) :
    ballotRoutedPartyQuotaState partyVoters partyCandidates after =
      ballotRoutedPartyQuotaState partyVoters partyCandidates before := by
  have hremaining :
      (after.active ∩ partyCandidates).card =
        (before.active ∩ partyCandidates).card :=
    congrArg Finset.card
      (active_party_eq_of_eliminate_outside
        (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hnoQuota := hnoQuota) (hminimum := hminimum)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate) hloserOutside)
  have hwinners :
      (after.elected ∩ partyCandidates).card =
        (before.elected ∩ partyCandidates).card :=
    congrArg Finset.card
      (elected_party_eq_of_eliminate
        (partyCandidates := partyCandidates) (hnotTerminal := hnotTerminal)
        (hactive := hactive) (hnoQuota := hnoQuota) (hminimum := hminimum)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate))
  have hmass : ballotRoutedPartyWeightMass partyVoters after.weight =
      ballotRoutedPartyWeightMass partyVoters before.weight :=
    ballotRoutedPartyWeightMass_eq_of_eliminate hpartyVoters before.weight_nonneg
      hupdate
  simp only [ballotRoutedPartyQuotaState]
  rw [hremaining, hwinners, hmass]

/--
Each actual global transition projects to either a party quota step or a
stuttering party state, provided both solid coalitions remain active.  This is
the source-level bridge used to project a reachable global run by induction.
-/
theorem partyQuotaStep_or_eq_of_transition
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after)
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ before.active)
    (hotherActive : ∃ same, same ∈ otherPartyCandidates ∧ same ∈ before.active) :
    PartyQuotaStep quota
        (ballotRoutedPartyQuotaState partyVoters partyCandidates before)
        (ballotRoutedPartyQuotaState partyVoters partyCandidates after) ∨
      ballotRoutedPartyQuotaState partyVoters partyCandidates after =
        ballotRoutedPartyQuotaState partyVoters partyCandidates before := by
  have hpartyVoters : partyVoters ⊆ voters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left otherPartyVoters hvoter
  cases htransition with
  | elect winner hnotTerminal hactive hroom hquota hafterActive hafterElected hupdate =>
      by_cases hwinnerParty : winner ∈ partyCandidates
      · left
        left
        exact partyQuotaElectStep_of_elect
          (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
          (partyCandidates := partyCandidates) (otherPartyCandidates := otherPartyCandidates)
          (hnotTerminal := hnotTerminal) (hactive := hactive) (hroom := hroom)
          (hquota := hquota) (hafterActive := hafterActive)
          (hafterElected := hafterElected) (hupdate := hupdate)
          hvoterPartition hcandidateDisjoint hotherSolid hotherActive hwinnerParty
      · right
        exact partyQuotaState_eq_of_elect_outside
          (partyVoters := partyVoters) (partyCandidates := partyCandidates)
          (hnotTerminal := hnotTerminal) (hactive := hactive) (hroom := hroom)
          (hquota := hquota) (hafterActive := hafterActive)
          (hafterElected := hafterElected) (hupdate := hupdate)
          hpartyVoters hpartySolid hpartyActive hwinnerParty
  | eliminate loser hnotTerminal hactive hnoQuota hminimum hafterActive hafterElected hupdate =>
      by_cases hloserParty : loser ∈ partyCandidates
      · left
        right
        exact partyQuotaEliminateStep_of_eliminate
          (partyVoters := partyVoters) (partyCandidates := partyCandidates)
          (hnotTerminal := hnotTerminal) (hactive := hactive)
          (hnoQuota := hnoQuota) (hminimum := hminimum)
          (hafterActive := hafterActive) (hafterElected := hafterElected)
          (hupdate := hupdate) hpartyVoters hloserParty
      · right
        exact partyQuotaState_eq_of_eliminate_outside
          (partyVoters := partyVoters) (partyCandidates := partyCandidates)
          (hnotTerminal := hnotTerminal) (hactive := hactive)
          (hnoQuota := hnoQuota) (hminimum := hminimum)
          (hafterActive := hafterActive) (hafterElected := hafterElected)
          (hupdate := hupdate) hpartyVoters hloserParty

/--
If no global active candidate reaches quota, then the active solid coalition's
own residual mass is below its number of active candidates times the quota.
-/
theorem partyVoteMass_lt_remaining_mul_quota_of_noQuota
    {partyVoters : Finset Voter} {partyCandidates : Finset Candidate}
    (hpartyVoters : partyVoters ⊆ voters)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ before.active)
    (hnoQuota : ∀ candidate, candidate ∈ before.active ->
      ballotRoutedTally voters ballots before.active before.weight candidate < quota) :
    (ballotRoutedPartyQuotaState partyVoters partyCandidates before).voteMass <
      ((ballotRoutedPartyQuotaState partyVoters partyCandidates before).remainingCandidates : ℝ) *
        quota := by
  have hnonempty :
      (activePartyCandidates before.active partyCandidates).Nonempty := by
    rcases hpartyActive with ⟨same, hsameParty, hsameActive⟩
    exact ⟨same, Finset.mem_filter.mpr ⟨hsameActive, hsameParty⟩⟩
  have hlocalBelowQuota :
      ∀ candidate,
        candidate ∈ activePartyCandidates before.active partyCandidates ->
          ballotRoutedTally partyVoters ballots before.active before.weight candidate < quota := by
    intro candidate hcandidate
    have hcandidateActive : candidate ∈ before.active :=
      (Finset.mem_filter.mp hcandidate).1
    have hlocal_le_global :
        ballotRoutedTally partyVoters ballots before.active before.weight candidate ≤
          ballotRoutedTally voters ballots before.active before.weight candidate := by
      exact fractionalActiveTally_le_of_voters_subset
        (ballots := ballots) (weight := before.weight) (active := before.active)
        (candidate := candidate) hpartyVoters before.weight_nonneg
    exact lt_of_le_of_lt hlocal_le_global (hnoQuota candidate hcandidateActive)
  have hmass_lt :
      (∑ candidate ∈ activePartyCandidates before.active partyCandidates,
        ballotRoutedTally partyVoters ballots before.active before.weight candidate) <
        ((activePartyCandidates before.active partyCandidates).card : ℝ) * quota := by
    exact partyFractionalTallyMass_lt_card_mul_quota_of_forall_lt
      (partyCandidates := partyCandidates)
      (fractionalTally := ballotRoutedTally partyVoters ballots before.active before.weight)
      (active := before.active) (quota := quota) hnonempty hlocalBelowQuota
  have hmass_eq :
      (∑ candidate ∈ activePartyCandidates before.active partyCandidates,
        ballotRoutedTally partyVoters ballots before.active before.weight candidate) =
          ballotRoutedPartyWeightMass partyVoters before.weight :=
    ballotRoutedPartyTallyMass_eq_weightMass_of_solidCoalition
      hpartySolid hpartyActive
  change ballotRoutedPartyWeightMass partyVoters before.weight <
    (((before.active ∩ partyCandidates).card : ℕ) : ℝ) * quota
  calc
    ballotRoutedPartyWeightMass partyVoters before.weight =
        ∑ candidate ∈ activePartyCandidates before.active partyCandidates,
          ballotRoutedTally partyVoters ballots before.active before.weight candidate := hmass_eq.symm
    _ < ((activePartyCandidates before.active partyCandidates).card : ℝ) * quota := hmass_lt
    _ = (((before.active ∩ partyCandidates).card : ℕ) : ℝ) * quota := by
      rw [activePartyCandidates_eq_inter]

/--
The party quota-capacity bound is preserved by every real ballot-routed STV
transition while both solid coalitions are active.  The proof derives the
no-quota elimination premise from the actual global tally condition.
-/
theorem partyQuotaCapacity_of_transition
    {partyVoters otherPartyVoters : Finset Voter}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (hcapacity : PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates before))
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after)
    (hvoterPartition : voters = partyVoters ∪ otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ before.active)
    (hotherActive : ∃ same, same ∈ otherPartyCandidates ∧ same ∈ before.active) :
    PartyQuotaCapacityBound quota
      (ballotRoutedPartyQuotaState partyVoters partyCandidates after) := by
  have hpartyVoters : partyVoters ⊆ voters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left otherPartyVoters hvoter
  cases htransition with
  | elect winner hnotTerminal hactive hroom hquota hafterActive hafterElected hupdate =>
      by_cases hwinnerParty : winner ∈ partyCandidates
      · exact PartyQuotaCapacityBound.of_electStep hcapacity
          (partyQuotaElectStep_of_elect
            (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
            (partyCandidates := partyCandidates)
            (otherPartyCandidates := otherPartyCandidates)
            (hnotTerminal := hnotTerminal) (hactive := hactive) (hroom := hroom)
            (hquota := hquota) (hafterActive := hafterActive)
            (hafterElected := hafterElected) (hupdate := hupdate)
            hvoterPartition hcandidateDisjoint hotherSolid hotherActive hwinnerParty)
      · have hstutter := partyQuotaState_eq_of_elect_outside
          (partyVoters := partyVoters) (partyCandidates := partyCandidates)
          (hnotTerminal := hnotTerminal) (hactive := hactive) (hroom := hroom)
          (hquota := hquota) (hafterActive := hafterActive)
          (hafterElected := hafterElected) (hupdate := hupdate)
          hpartyVoters hpartySolid hpartyActive hwinnerParty
        rw [hstutter]
        exact hcapacity
  | eliminate loser hnotTerminal hactive hnoQuota hminimum hafterActive hafterElected hupdate =>
      by_cases hloserParty : loser ∈ partyCandidates
      · exact PartyQuotaCapacityBound.of_eliminateStep_of_voteMass_lt_remaining_mul_quota
          (partyVoteMass_lt_remaining_mul_quota_of_noQuota
            (partyVoters := partyVoters) (partyCandidates := partyCandidates)
            hpartyVoters hpartySolid hpartyActive hnoQuota)
          (partyQuotaEliminateStep_of_eliminate
            (partyVoters := partyVoters) (partyCandidates := partyCandidates)
            (hnotTerminal := hnotTerminal) (hactive := hactive)
            (hnoQuota := hnoQuota) (hminimum := hminimum)
            (hafterActive := hafterActive) (hafterElected := hafterElected)
            (hupdate := hupdate) hpartyVoters hloserParty)
      · have hstutter := partyQuotaState_eq_of_eliminate_outside
          (partyVoters := partyVoters) (partyCandidates := partyCandidates)
          (hnotTerminal := hnotTerminal) (hactive := hactive)
          (hnoQuota := hnoQuota) (hminimum := hminimum)
          (hafterActive := hafterActive) (hafterElected := hafterElected)
          (hupdate := hupdate) hpartyVoters hloserParty
        rw [hstutter]
        exact hcapacity

end BallotRoutedSTVTransition

end GGRS26CombattingGerrymanderingRCV
