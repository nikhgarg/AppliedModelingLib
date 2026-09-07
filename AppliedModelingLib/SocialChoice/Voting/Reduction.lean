import AppliedModelingLib.SocialChoice.Voting.Ballot

/-!
# Candidate-Removal Reductions

Reusable primitives for RCV/STV reductions that delete candidates from the
candidate set and from every ranked ballot while preserving later active-support
counts after the deleted candidates have left the active set.

## Main declarations

- `ReducedElectionInstance`
- `ReducedElectionInstance.removeCandidates`
- `ReducedElectionInstance.PreservesActiveSupport`
- `ReducedElectionInstance.preservesActiveSupport_removeCandidates_of_disjoint_active`
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/--
An election instance after a candidate-removal reduction: the remaining
candidate set and the reduced ballot profile.
-/
structure ReducedElectionInstance (Voter Candidate : Type*) where
  /-- Candidate set in the reduced election. -/
  candidates : Finset Candidate
  /-- Ballot profile in the reduced election. -/
  ballots : Voter → Ballot Candidate

namespace ReducedElectionInstance

/--
Delete `removed` from the candidate set and from each ballot, preserving the
relative order of the remaining candidates.
-/
def removeCandidates {Voter Candidate : Type*} [DecidableEq Candidate]
    (removed candidates : Finset Candidate) (ballots : Voter → Ballot Candidate) :
    ReducedElectionInstance Voter Candidate where
  candidates := candidates \ removed
  ballots := fun voter => Ballot.removeCandidates removed (ballots voter)

/--
The reduced profile preserves active-support counts at `active` relative to the
source ballot profile.
-/
def PreservesActiveSupport {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (sourceBallots : Voter → Ballot Candidate)
    (active : Finset Candidate)
    (reduced : ReducedElectionInstance Voter Candidate) : Prop :=
  ∀ candidate : Candidate,
    (Ballot.activeSupport voters reduced.ballots active candidate).card =
      (Ballot.activeSupport voters sourceBallots active candidate).card

/--
Candidate deletion preserves active-support counts at any active set disjoint
from the deleted candidates.
-/
theorem preservesActiveSupport_removeCandidates_of_disjoint_active
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active removed candidates : Finset Candidate}
    (hdisjoint : active ∩ removed = ∅) :
    PreservesActiveSupport voters ballots active
      (removeCandidates removed candidates ballots) := by
  intro candidate
  exact Ballot.activeSupport_card_removeCandidates_eq_of_disjoint_active
    (voters := voters) (ballots := ballots) (active := active)
    (removed := removed) (candidate := candidate) hdisjoint

end ReducedElectionInstance

end Voting
end SocialChoice
end AppliedModelingLib
