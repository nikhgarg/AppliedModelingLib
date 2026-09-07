import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTV

/-!
# Global Mass Invariants for Ballot-Routed STV

These are operational facts about the reachable ballot-level transition.  They
deliberately mention only voter weights, elected candidates, and the transfer
policy laws; no party projection or terminal outcome is assumed.
-/

namespace GGRS26CombattingGerrymanderingRCV

open scoped BigOperators
open AppliedModelingLib.SocialChoice.Voting

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
variable {voters : Finset Voter} {initialCandidates : Finset Candidate}
variable {ballots : Voter -> Ballot Candidate} {quota : ℝ}
variable {policy : BallotRoutedSTVTransferPolicy voters ballots quota} {seats : ℕ}

/-- Total transferable voter weight in one reachable ballot-routed state. -/
def ballotRoutedTotalMass
    (state : BallotRoutedSTVState voters initialCandidates) : ℝ :=
  ∑ voter ∈ voters, state.weight voter

/-- The source's global quota accounting invariant. -/
def BallotRoutedSTVGlobalInvariant (initialVotes : ℝ)
    (state : BallotRoutedSTVState voters initialCandidates) : Prop :=
  initialVotes = (state.elected.card : ℝ) * quota + ballotRoutedTotalMass state

namespace BallotRoutedSTVTransition

variable {before after : BallotRoutedSTVState voters initialCandidates}

/-- Elections only add their focused winner to the elected set. -/
theorem elected_subset
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    before.elected ⊆ after.elected := by
  cases htransition with
  | elect winner _ _ _ _ _ hafterElected _ =>
      rw [hafterElected]
      exact Finset.subset_insert winner before.elected
  | eliminate _ _ _ _ _ _ hafterElected _ =>
      simpa [hafterElected]

/-- An election transfer removes exactly one quota of global transferable mass. -/
theorem totalMass_of_elect
    {winner : Candidate}
    {hnotTerminal : ¬ BallotRoutedSTVTerminal seats before}
    {hactive : winner ∈ before.active} {hroom : before.elected.card < seats}
    {hquota : quota ≤ ballotRoutedTally voters ballots before.active before.weight winner}
    {hafterActive : after.active = before.active.erase winner}
    {hafterElected : after.elected = insert winner before.elected}
    {hupdate : policy.electUpdate before.active winner before.weight after.weight} :
    ballotRoutedTotalMass after = ballotRoutedTotalMass before - quota := by
  let support := ballotRoutedSupport voters ballots before.active winner
  have hsupport_subset : support ⊆ voters := by
    exact ballotRoutedSupport_subset_voters
  have houtside :
      (∑ voter ∈ voters \ support, after.weight voter) =
        ∑ voter ∈ voters \ support, before.weight voter := by
    apply Finset.sum_congr rfl
    intro voter hvoter
    exact policy.elect_unchanged_off_support before.active winner before.weight
      after.weight before.weight_nonneg hupdate voter (Finset.mem_sdiff.mp hvoter).1
      (Finset.mem_sdiff.mp hvoter).2
  have hbefore_decomp := Finset.sum_sdiff hsupport_subset (f := before.weight)
  have hafter_decomp := Finset.sum_sdiff hsupport_subset (f := after.weight)
  have hdrop := policy.elect_support_mass_drop_exactly_quota before.active winner
    before.weight after.weight before.weight_nonneg hupdate
  change (∑ voter ∈ voters, after.weight voter) =
    (∑ voter ∈ voters, before.weight voter) - quota
  rw [← hafter_decomp, houtside, hdrop, ← hbefore_decomp]
  ring

/-- Eliminations preserve all transferable voter weight. -/
theorem totalMass_of_eliminate
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
    ballotRoutedTotalMass after = ballotRoutedTotalMass before := by
  change (∑ voter ∈ voters, after.weight voter) =
    ∑ voter ∈ voters, before.weight voter
  apply Finset.sum_congr rfl
  intro voter hvoter
  exact policy.eliminate_weight_unchanged before.active loser before.weight
    after.weight before.weight_nonneg hupdate voter hvoter

/-- One source transition preserves the global quota accounting invariant. -/
theorem globalInvariant_of_transition {initialVotes : ℝ}
    (hinvariant : BallotRoutedSTVGlobalInvariant (quota := quota) initialVotes before)
    (htransition : BallotRoutedSTVTransition ballots quota policy seats before after) :
    BallotRoutedSTVGlobalInvariant (quota := quota) initialVotes after := by
  cases htransition with
  | elect winner hnotTerminal hactive hroom hquota hafterActive hafterElected hupdate =>
      have hmass := totalMass_of_elect (policy := policy) (seats := seats)
        (hnotTerminal := hnotTerminal) (hactive := hactive) (hroom := hroom)
        (hquota := hquota) (hafterActive := hafterActive)
        (hafterElected := hafterElected) (hupdate := hupdate)
      have hcard := elected_card_succ_of_elect (policy := policy) (seats := seats)
        (hnotTerminal := hnotTerminal) (hactive := hactive) (hroom := hroom)
        (hquota := hquota) (hafterActive := hafterActive)
        (hafterElected := hafterElected) (hupdate := hupdate)
      unfold BallotRoutedSTVGlobalInvariant at hinvariant ⊢
      rw [hmass, hcard, Nat.cast_add, Nat.cast_one]
      linarith
  | eliminate loser hnotTerminal hactive hnoQuota hminimum hafterActive hafterElected hupdate =>
      have hmass := totalMass_of_eliminate (policy := policy) (seats := seats)
        (hnotTerminal := hnotTerminal) (hactive := hactive)
        (hnoQuota := hnoQuota) (hminimum := hminimum)
        (hafterActive := hafterActive) (hafterElected := hafterElected)
        (hupdate := hupdate)
      unfold BallotRoutedSTVGlobalInvariant at hinvariant ⊢
      simpa [hafterElected, hmass] using hinvariant

/-- Global quota accounting holds at every point of an actual ballot-routed run. -/
theorem globalInvariant_of_run {initialVotes : ℝ}
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    (hinvariant : BallotRoutedSTVGlobalInvariant (quota := quota) initialVotes initial)
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal) :
    BallotRoutedSTVGlobalInvariant (quota := quota) initialVotes terminal := by
  induction hrun using Relation.ReflTransGen.trans_induction_on with
  | refl => exact hinvariant
  | single htransition => exact globalInvariant_of_transition hinvariant htransition
  | trans _ _ hleft hright =>
      exact hright (hleft hinvariant)

/-- Elected candidates are monotone along an actual ballot-routed run. -/
theorem elected_subset_of_run
    {initial terminal : BallotRoutedSTVState voters initialCandidates}
    (hrun : BallotRoutedSTVRun ballots quota policy seats initial terminal) :
    initial.elected ⊆ terminal.elected := by
  induction hrun using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Finset.Subset.rfl
  | single htransition => exact elected_subset htransition
  | trans _ _ hleft hright => exact Set.Subset.trans hleft hright

end BallotRoutedSTVTransition

end GGRS26CombattingGerrymanderingRCV
