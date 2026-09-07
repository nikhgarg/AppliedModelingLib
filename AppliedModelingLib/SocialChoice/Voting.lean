import AppliedModelingLib.SocialChoice.Voting.Ballot
import AppliedModelingLib.SocialChoice.Voting.Reduction
import AppliedModelingLib.SocialChoice.Voting.STV
import AppliedModelingLib.SocialChoice.Voting.STV.Quota
import AppliedModelingLib.SocialChoice.Voting.STV.SolidCoalition
import AppliedModelingLib.SocialChoice.Voting.STV.Structures
import AppliedModelingLib.SocialChoice.Voting.Thiele
import AppliedModelingLib.SocialChoice.Voting.Proportionality

/-!
# Voting

Aggregate import for reusable voting-rule primitives.

## Main declarations

- `AppliedModelingLib.SocialChoice.Voting.Ballot`: ranked ballots and next-active
  preference.
- `AppliedModelingLib.SocialChoice.Voting.Reduction`: candidate-deletion reductions and
  active-support preservation.
- `AppliedModelingLib.SocialChoice.Voting.STV`: deterministic STV/RCV trace vocabulary.
- `AppliedModelingLib.SocialChoice.Voting.STV.Quota`: Droop quota arithmetic.
- `AppliedModelingLib.SocialChoice.Voting.STV.SolidCoalition`: party-level quota-process
  invariants for solid-coalition STV proofs.
- `AppliedModelingLib.SocialChoice.Voting.STV.Structures`: final-order and win/loss
  structure replay predicates.
- `AppliedModelingLib.SocialChoice.Voting.Thiele`: approval ballots and committee
  score primitives.
- `AppliedModelingLib.SocialChoice.Voting.Proportionality`: two-party floor/ceiling
  seat-share arithmetic.
-/
