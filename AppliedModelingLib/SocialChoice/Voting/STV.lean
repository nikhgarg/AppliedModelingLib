import AppliedModelingLib.SocialChoice.Voting.Ballot
import Mathlib.Data.Finset.Max

/-!
# STV Trace Primitives

Paper-neutral vocabulary for deterministic single-transferable-vote and
ranked-choice traces.

This module intentionally does not encode a single quota or tie-breaking
convention. Downstream developments should instantiate these structures with
their concrete rules and prove replay/validity theorems there or in later
generic modules.

## Main declarations

- `STVQuota`
- `strictSupportGroupRemovalCondition`
- `strictSupportGroupRemovalSafety`
- `strictSupportGroupRemovalSafety_of_condition`
- `strictSupportGroupRemovalSafety_trace_elimination_focus_mem_group`
- `StepKind`
- `STVStep`
- `STVTrace`
- `profileActiveTallyOf`
- `canonicalProfileGroupEliminationGeneratedTrace`
- `STVStep.activeMonotone`
- `STVStep.eliminatesMinimalTally`
- `STVStep.removesFocusedCandidate`
- `STVStep.focus_eq_of_tally_lt_all_other_active`
- `ActiveUntilExitRank`
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/-- Droop-style integer quota used by many STV presentations. -/
def STVQuota (seats voters : ℕ) : ℕ :=
  voters / (seats + 1) + 1

/--
Strict-support group-removal condition: every candidate inside a removable
group remains below quota after the budget, and every outside candidate still
strictly dominates the possible last inside candidate after the rest of the
group transfers away.
-/
def strictSupportGroupRemovalCondition {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Prop :=
  (∀ inside, inside ∈ group →
    budget + Ballot.strictSupportCount voters ballots group
        (candidates \ group) inside < quota) ∧
    ∀ inside, inside ∈ group → ∀ outside, outside ∈ candidates \ group →
      budget + Ballot.strictSupportCount voters ballots group
          (candidates \ group) inside <
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside ∧
      Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside < quota

/--
Separated safety consequences of strict-support group removal: inside
candidates remain below quota, outside candidates dominate each possible last
inside candidate, and outside candidates remain below quota.
-/
def strictSupportGroupRemovalSafety {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Prop :=
  (∀ inside, inside ∈ group →
    budget + Ballot.strictSupportCount voters ballots group
        (candidates \ group) inside < quota) ∧
    (∀ inside, inside ∈ group → ∀ outside, outside ∈ candidates \ group →
      budget + Ballot.strictSupportCount voters ballots group
          (candidates \ group) inside <
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) ∧
    ∀ inside, inside ∈ group → ∀ outside, outside ∈ candidates \ group →
      Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside < quota

/--
The compact strict-support group-removal condition entails its separated
safety consequences.
-/
theorem strictSupportGroupRemovalSafety_of_condition
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hcondition :
      strictSupportGroupRemovalCondition
        voters ballots candidates group budget quota) :
    strictSupportGroupRemovalSafety voters ballots candidates group budget quota := by
  rcases hcondition with ⟨hbelow_quota, houtside_condition⟩
  exact ⟨hbelow_quota,
    (by
      intro inside hinside outside houtside
      exact (houtside_condition inside hinside outside houtside).1),
    (by
      intro inside hinside outside houtside
      exact (houtside_condition inside hinside outside houtside).2)⟩

/-- A deterministic trace step either elects, eliminates, transfers, or stops. -/
inductive StepKind where
  | elect
  | eliminate
  | transfer
  | finish
  deriving DecidableEq, Repr

/--
One deterministic STV/RCV trace step.

The `tally` field is intentionally an input datum here. Different papers may
derive tallies from first-active ballots, fractional transfers, or audited data
sources before instantiating this generic trace layer.
-/
structure STVStep (Candidate : Type*) where
  beforeActive : Finset Candidate
  afterActive : Finset Candidate
  kind : StepKind
  focus : Option Candidate
  tally : Candidate → ℕ

namespace STVStep

/-- The active set only shrinks along an ordinary deterministic STV step. -/
def activeMonotone {Candidate : Type*} (step : STVStep Candidate) : Prop :=
  step.afterActive ⊆ step.beforeActive

/--
The step removes exactly its focused candidate from the active set.

This is separated from `kind`: different papers may use the same active-set
transition for eliminations, elections, or quota-transfer bookkeeping.
-/
def removesFocusedCandidate {Candidate : Type*} [DecidableEq Candidate]
    (step : STVStep Candidate) : Prop :=
  ∃ candidate, step.focus = some candidate ∧
    step.afterActive = step.beforeActive.erase candidate

/--
An elimination step chooses an active candidate whose tally is no larger than
every active candidate's tally.

This predicate deliberately leaves tie-breaking abstract. Paper-local replay
theorems can strengthen it with a concrete tie-breaker when needed.
-/
def eliminatesMinimalTally {Candidate : Type*} (step : STVStep Candidate) :
    Prop :=
  step.kind = StepKind.eliminate ∧
    ∃ loser, step.focus = some loser ∧ loser ∈ step.beforeActive ∧
      ∀ candidate, candidate ∈ step.beforeActive →
        step.tally loser ≤ step.tally candidate

/--
If an active candidate has strictly larger tally than another active
candidate, a minimum-tally elimination step cannot eliminate the larger-tally
candidate.
-/
theorem focus_ne_of_exists_active_tally_lt {Candidate : Type*}
    {step : STVStep Candidate} (hminimal : step.eliminatesMinimalTally)
    {lower candidate : Candidate}
    (hlower_active : lower ∈ step.beforeActive)
    (hcandidate_active : candidate ∈ step.beforeActive)
    (hlt : step.tally lower < step.tally candidate) :
    step.focus ≠ some candidate := by
  rcases hminimal with ⟨_hkind, loser, hfocus, _hloser_active, hloser_le⟩
  intro hfocus_candidate
  have hloser_eq_candidate : loser = candidate := by
    exact Option.some.inj (hfocus.symm.trans hfocus_candidate)
  subst loser
  have hle : step.tally candidate ≤ step.tally lower :=
    hloser_le lower hlower_active
  exact not_lt_of_ge hle hlt

/--
If one active candidate has strictly smaller tally than every other active
candidate, a minimum-tally elimination step must focus on that candidate.
-/
theorem focus_eq_of_tally_lt_all_other_active {Candidate : Type*}
    {step : STVStep Candidate} (hminimal : step.eliminatesMinimalTally)
    {candidate : Candidate}
    (hcandidate_active : candidate ∈ step.beforeActive)
    (hlt :
      ∀ other, other ∈ step.beforeActive → other ≠ candidate →
        step.tally candidate < step.tally other) :
    step.focus = some candidate := by
  rcases hminimal with ⟨_hkind, loser, hfocus, hloser_active, hloser_le⟩
  by_cases hloser_eq : loser = candidate
  · simpa [hloser_eq] using hfocus
  · have hlt_loser : step.tally candidate < step.tally loser :=
      hlt loser hloser_active hloser_eq
    have hle : step.tally loser ≤ step.tally candidate :=
      hloser_le candidate hcandidate_active
    exact (not_lt_of_ge hle hlt_loser).elim

/--
If a step removes its focused candidate, the focused candidate is absent from
the step's post-active set.
-/
theorem focus_not_mem_afterActive_of_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {step : STVStep Candidate} (hremove : step.removesFocusedCandidate)
    {candidate : Candidate} (hfocus : step.focus = some candidate) :
    candidate ∉ step.afterActive := by
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = candidate :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  simp [hafter]

/--
Removing a focused active candidate from a group strictly decreases the number
of active candidates in that group.
-/
theorem card_afterActive_inter_lt_beforeActive_inter_of_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {step : STVStep Candidate} {group : Finset Candidate}
    (hremove : step.removesFocusedCandidate)
    {candidate : Candidate} (hfocus : step.focus = some candidate)
    (hgroup : candidate ∈ group) (hactive : candidate ∈ step.beforeActive) :
    (step.afterActive ∩ group).card <
      (step.beforeActive ∩ group).card := by
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = candidate :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  have hmem : candidate ∈ step.beforeActive ∩ group := by
    simp [hactive, hgroup]
  have hinter :
      step.afterActive ∩ group =
        (step.beforeActive ∩ group).erase candidate := by
    ext other
    simp [hafter, and_comm]
  rw [hinter]
  exact Finset.card_erase_lt_of_mem hmem

/--
Removing a focused active candidate from a group decreases the number of active
group candidates by exactly one.
-/
theorem card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {step : STVStep Candidate} {group : Finset Candidate}
    (hremove : step.removesFocusedCandidate)
    {candidate : Candidate} (hfocus : step.focus = some candidate)
    (hgroup : candidate ∈ group) (hactive : candidate ∈ step.beforeActive) :
    (step.afterActive ∩ group).card + 1 =
      (step.beforeActive ∩ group).card := by
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = candidate :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  have hmem : candidate ∈ step.beforeActive ∩ group := by
    simp [hactive, hgroup]
  have hinter :
      step.afterActive ∩ group =
        (step.beforeActive ∩ group).erase candidate := by
    ext other
    simp [hafter, and_comm]
  rw [hinter]
  exact Finset.card_erase_add_one hmem

/--
Paper-neutral tally bound from ballot support: if the step tally for an active
candidate is bounded by its active-support count, and active-support voters
split by first choice into the candidate itself or a removed set, then the
tally is bounded by first-choice support plus transferred strict support from
that removed set.

The `htally_le_activeSupport` premise is explicit because this trace layer
does not prescribe how a paper computes `step.tally`.
-/
theorem tally_le_firstChoiceCount_add_strictSupportCount_removed
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {removed : Finset Candidate} {step : STVStep Candidate}
    {candidate : Candidate}
    (htally_le_activeSupport :
      step.tally candidate ≤
        (Ballot.activeSupport voters ballots step.beforeActive candidate).card)
    (hcandidate : candidate ∈ step.beforeActive)
    (hpartition :
      ∀ voter, voter ∈ voters →
        Ballot.nextActive (ballots voter) step.beforeActive =
          some candidate →
        Ballot.firstChoiceIn (ballots voter) {candidate} ∨
          Ballot.firstChoiceIn (ballots voter) removed) :
    step.tally candidate ≤
      Ballot.firstChoiceCount voters ballots candidate +
        Ballot.strictSupportCount voters ballots removed
          (step.beforeActive.erase candidate) candidate := by
  exact le_trans htally_le_activeSupport
    (Ballot.activeSupport_card_le_firstChoiceCount_add_strictSupportCount_removed
      (voters := voters) (ballots := ballots)
      (active := step.beforeActive) (removed := removed)
      (candidate := candidate) hcandidate hpartition)

/--
Numerical version of
`tally_le_firstChoiceCount_add_strictSupportCount_removed`, suitable for
transfer-prefix arguments: replace first-choice and transferred-support counts
by caller-supplied upper bounds.
-/
theorem tally_le_base_add_transferBound_of_activeSupport_partition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {removed : Finset Candidate} {step : STVStep Candidate}
    {candidate : Candidate} {base transferBound : ℕ}
    (htally_le_activeSupport :
      step.tally candidate ≤
        (Ballot.activeSupport voters ballots step.beforeActive candidate).card)
    (hcandidate : candidate ∈ step.beforeActive)
    (hpartition :
      ∀ voter, voter ∈ voters →
        Ballot.nextActive (ballots voter) step.beforeActive =
          some candidate →
        Ballot.firstChoiceIn (ballots voter) {candidate} ∨
          Ballot.firstChoiceIn (ballots voter) removed)
    (hfirst_le :
      Ballot.firstChoiceCount voters ballots candidate ≤ base)
    (htransfer_le :
      Ballot.strictSupportCount voters ballots removed
          (step.beforeActive.erase candidate) candidate ≤
        transferBound) :
    step.tally candidate ≤ base + transferBound := by
  exact le_trans
    (tally_le_firstChoiceCount_add_strictSupportCount_removed
      (voters := voters) (ballots := ballots) (removed := removed)
      (step := step) (candidate := candidate)
      htally_le_activeSupport hcandidate hpartition)
    (Nat.add_le_add hfirst_le htransfer_le)

end STVStep

/--
Strict-support group-removal safety, read as a current-round tally fact: an
inside candidate's budget-augmented strict support is still below quota.
-/
theorem strictSupportGroupRemovalSafety_inside_tally_lt_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (htally_inside :
      step.tally inside =
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside) :
    step.tally inside < quota := by
  simpa [htally_inside] using hsafety.1 inside hinside

/--
Strict-support group-removal safety, read as a current-round tally fact: an
outside candidate's strict support after transfers from `group \ {inside}` is
still below quota.
-/
theorem strictSupportGroupRemovalSafety_outside_tally_lt_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (htally_outside :
      step.tally outside =
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) :
    step.tally outside < quota := by
  simpa [htally_outside] using hsafety.2.2 inside hinside outside houtside

/--
Strict-support group-removal safety prevents an outside candidate from being
the focus of a minimum-tally elimination step when some inside candidate is
still active with the group-removal tally interpretation.
-/
theorem strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (houtside_active : outside ∈ step.beforeActive)
    (htally_inside :
      step.tally inside =
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside :
      step.tally outside =
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) :
    step.focus ≠ some outside := by
  have hlt :
      step.tally inside < step.tally outside := by
    simpa [htally_inside, htally_outside] using
      hsafety.2.1 inside hinside outside houtside
  exact STVStep.focus_ne_of_exists_active_tally_lt
    hminimal hinside_active houtside_active hlt

/--
Bounded-tally version of
`strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus`.
It is enough for the current inside tally to be bounded above by the
budget-augmented strict-support expression and for the outside tally to be
bounded below by its strict-support expression.
-/
theorem strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (houtside_active : outside ∈ step.beforeActive)
    (htally_inside_le :
      step.tally inside ≤
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside_ge :
      Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside ≤
        step.tally outside) :
    step.focus ≠ some outside := by
  have hstrict_support :
      budget +
          Ballot.strictSupportCount voters ballots group
            (candidates \ group) inside <
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside :=
    hsafety.2.1 inside hinside outside houtside
  have hlt : step.tally inside < step.tally outside :=
    lt_of_le_of_lt htally_inside_le
      (lt_of_lt_of_le hstrict_support htally_outside_ge)
  exact STVStep.focus_ne_of_exists_active_tally_lt
    hminimal hinside_active houtside_active hlt

/--
Strict-support group-removal safety forces a minimum-tally elimination step to
focus on a group candidate, provided some group candidate is still active and
the step tallies agree with the group-removal strict-support quantities.
-/
theorem strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset_candidates : step.beforeActive ⊆ candidates)
    (htally_inside :
      step.tally inside =
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside :
      ∀ outside, outside ∈ candidates \ group →
        step.tally outside =
          Ballot.strictSupportCount voters ballots
            (insert outside (group.erase inside)) (∅ : Finset Candidate)
            outside) :
    ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
      loser ∈ step.beforeActive := by
  rcases hminimal with ⟨hkind, loser, hfocus, hloser_active, hloser_le⟩
  refine ⟨loser, hfocus, ?_, hloser_active⟩
  by_contra hloser_not_group
  have hminimal' : step.eliminatesMinimalTally :=
    ⟨hkind, loser, hfocus, hloser_active, hloser_le⟩
  have hloser_candidates : loser ∈ candidates :=
    hactive_subset_candidates hloser_active
  have hloser_outside : loser ∈ candidates \ group :=
    Finset.mem_sdiff.mpr ⟨hloser_candidates, hloser_not_group⟩
  have hfocus_ne :
      step.focus ≠ some loser :=
    strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus
      hsafety hinside hloser_outside hminimal' hinside_active
      hloser_active htally_inside (htally_outside loser hloser_outside)
  exact hfocus_ne hfocus

/--
Bounded-tally version of
`strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group`.
Exact tally identities are not needed: the inside candidate may use any upper
bound and the outside candidates may use any lower bound compatible with the
strict-support safety inequalities.
-/
theorem strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset_candidates : step.beforeActive ⊆ candidates)
    (htally_inside_le :
      step.tally inside ≤
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside_ge :
      ∀ outside, outside ∈ candidates \ group →
        Ballot.strictSupportCount voters ballots
            (insert outside (group.erase inside)) (∅ : Finset Candidate)
            outside ≤
          step.tally outside) :
    ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
      loser ∈ step.beforeActive := by
  rcases hminimal with ⟨hkind, loser, hfocus, hloser_active, hloser_le⟩
  refine ⟨loser, hfocus, ?_, hloser_active⟩
  by_contra hloser_not_group
  have hminimal' : step.eliminatesMinimalTally :=
    ⟨hkind, loser, hfocus, hloser_active, hloser_le⟩
  have hloser_candidates : loser ∈ candidates :=
    hactive_subset_candidates hloser_active
  have hloser_outside : loser ∈ candidates \ group :=
    Finset.mem_sdiff.mpr ⟨hloser_candidates, hloser_not_group⟩
  have hfocus_ne :
      step.focus ≠ some loser :=
    strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus_of_tally_bounds
      hsafety hinside hloser_outside hminimal' hinside_active
      hloser_active htally_inside_le
      (htally_outside_ge loser hloser_outside)
  exact hfocus_ne hfocus

/-- A deterministic STV/RCV trace is a list of election steps. -/
structure STVTrace (Candidate : Type*) where
  steps : List (STVStep Candidate)

namespace STVTrace

/-- Every step in a trace has monotone active sets. -/
def activeMonotone {Candidate : Type*} (trace : STVTrace Candidate) : Prop :=
  ∀ step ∈ trace.steps, step.activeMonotone

@[simp] theorem activeMonotone_nil {Candidate : Type*} :
    activeMonotone ({ steps := [] } : STVTrace Candidate) := by
  intro step hstep
  simp at hstep

/--
Every elimination step in the trace removes a focused candidate from the named
group.
-/
def eliminationRemovesFromGroup {Candidate : Type*} [DecidableEq Candidate]
    (trace : STVTrace Candidate) (group : Finset Candidate) : Prop :=
  ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
    ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
      loser ∈ step.beforeActive ∧
      step.afterActive = step.beforeActive.erase loser

/--
Every elimination step in the trace strictly decreases the number of active
candidates in the named group.
-/
def eliminationActiveGroupCardDecreases {Candidate : Type*}
    [DecidableEq Candidate]
    (trace : STVTrace Candidate) (group : Finset Candidate) : Prop :=
  ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
    (step.afterActive ∩ group).card <
      (step.beforeActive ∩ group).card

/--
Every elimination step in the trace removes exactly one active candidate from
the named group.
-/
def eliminationActiveGroupCardAddOneEq {Candidate : Type*}
    [DecidableEq Candidate]
    (trace : STVTrace Candidate) (group : Finset Candidate) : Prop :=
  ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
    (step.afterActive ∩ group).card + 1 =
      (step.beforeActive ∩ group).card

/--
The list of steps replays active sets from `startActive` to `terminalActive`.
This is the recursion kernel behind `STVTrace.replaysFrom`.
-/
def replayStepsFrom {Candidate : Type*} (steps : List (STVStep Candidate))
    (startActive terminalActive : Finset Candidate) : Prop :=
  match steps with
  | [] => terminalActive = startActive
  | step :: rest =>
      step.beforeActive = startActive ∧
        replayStepsFrom rest step.afterActive terminalActive

/--
The trace replays active sets from `startActive` to `terminalActive`: the first
step starts at `startActive`, each following step starts at the previous step's
post-active set, and the final post-active set is `terminalActive`.
-/
def replaysFrom {Candidate : Type*} (trace : STVTrace Candidate)
    (startActive terminalActive : Finset Candidate) : Prop :=
  replayStepsFrom trace.steps startActive terminalActive

/--
A replayed trace supplies a replay for every strict prefix ending at the
`beforeActive` set of the next step.
-/
theorem replayStepsFrom_take_get_beforeActive {Candidate : Type*}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (i : Fin steps.length) :
    replayStepsFrom (steps.take i.1) startActive (steps.get i).beforeActive := by
  induction steps generalizing startActive with
  | nil =>
      exact Fin.elim0 i
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      cases i with
      | mk n hn =>
          cases n with
          | zero =>
              simp [replayStepsFrom, hbefore]
          | succ n =>
              have hn_rest : n < rest.length := by
                simpa using Nat.succ_lt_succ_iff.mp hn
              simp [replayStepsFrom, hbefore]
              exact ih hrest ⟨n, hn_rest⟩

/--
In a replaying trace, each non-initial step starts from the previous step's
post-active set.
-/
theorem replayStepsFrom_get_succ_beforeActive_eq_afterActive
    {Candidate : Type*} {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    {i : ℕ} (hnext : i + 1 < steps.length) :
    (steps.get ⟨i + 1, hnext⟩).beforeActive =
      (steps.get ⟨i, Nat.lt_of_succ_lt hnext⟩).afterActive := by
  induction steps generalizing startActive i with
  | nil =>
      simp at hnext
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨_hbefore, hrest⟩
      cases i with
      | zero =>
          cases rest with
          | nil =>
              simp at hnext
          | cons next restTail =>
              simp only [List.get]
              simpa [replayStepsFrom] using hrest.1
      | succ i =>
          have hnext_rest : i + 1 < rest.length := by
            exact Nat.succ_lt_succ_iff.mp (by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext)
          have hih :=
            ih (startActive := step.afterActive) hrest hnext_rest
          simpa [List.get] using hih

/--
Trace-level wrapper for `replayStepsFrom_take_get_beforeActive`.
-/
theorem replaysFrom_take_get_beforeActive {Candidate : Type*}
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (i : Fin trace.steps.length) :
    replayStepsFrom (trace.steps.take i.1) startActive
      (trace.steps.get i).beforeActive :=
  replayStepsFrom_take_get_beforeActive hreplay i

/--
If a replay prefix consists of eliminations and each elimination removes a
candidate from `group`, then every candidate missing from the terminal active
set of that prefix was a member of `group`.
-/
theorem start_sdiff_terminal_subset_group_of_replayStepsFrom_eliminationRemovesFromGroup
    {Candidate : Type*} [DecidableEq Candidate]
    {steps : List (STVStep Candidate)}
    {startActive terminalActive group : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ steps → step.kind = StepKind.eliminate)
    (htrace :
      ({ steps := steps } : STVTrace Candidate).eliminationRemovesFromGroup
        group) :
    startActive \ terminalActive ⊆ group := by
  induction steps generalizing startActive with
  | nil =>
      simp [replayStepsFrom] at hreplay
      intro candidate hcandidate
      exact False.elim ((Finset.mem_sdiff.mp hcandidate).2 (by
        simpa [hreplay] using (Finset.mem_sdiff.mp hcandidate).1))
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      intro candidate hcandidate
      have hcandidate_start : candidate ∈ startActive :=
        (Finset.mem_sdiff.mp hcandidate).1
      have hcandidate_terminal : candidate ∉ terminalActive :=
        (Finset.mem_sdiff.mp hcandidate).2
      by_cases hcandidate_after : candidate ∈ step.afterActive
      · have htail_trace :
          ({ steps := rest } : STVTrace Candidate).eliminationRemovesFromGroup
            group := by
          intro tailStep htailStep hkind
          exact htrace tailStep (by simp [htailStep]) hkind
        exact
          ih hrest
            (fun tailStep htailStep =>
              hall_eliminate tailStep (by simp [htailStep]))
            htail_trace
            (Finset.mem_sdiff.mpr
              ⟨hcandidate_after, hcandidate_terminal⟩)
      · have hkind : step.kind = StepKind.eliminate :=
          hall_eliminate step (by simp)
        rcases htrace step (by simp) hkind with
          ⟨loser, _hfocus, hloser_group, _hloser_active, hafter⟩
        have hcandidate_before : candidate ∈ step.beforeActive := by
          simpa [hbefore] using hcandidate_start
        have hcandidate_eq_loser : candidate = loser := by
          by_contra hne
          exact hcandidate_after (by
            rw [hafter]
            exact Finset.mem_erase.mpr ⟨hne, hcandidate_before⟩)
        simpa [hcandidate_eq_loser] using hloser_group

/-- Removing a focused candidate is an active-set monotone transition. -/
theorem activeMonotone_of_removesFocusedCandidate {Candidate : Type*}
    [DecidableEq Candidate] {step : STVStep Candidate}
    (hremove : step.removesFocusedCandidate) :
    step.activeMonotone := by
  rcases hremove with ⟨focused, _hfocus, hafter⟩
  intro candidate hcandidate
  rw [hafter] at hcandidate
  exact (Finset.mem_erase.mp hcandidate).2

/--
Along a replay whose steps are active-set monotone, the terminal active set is
contained in the initial active set.
-/
theorem terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
    {Candidate : Type*} {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hmono : ∀ step, step ∈ steps → step.activeMonotone) :
    terminalActive ⊆ startActive := by
  induction steps generalizing startActive with
  | nil =>
      simp [replayStepsFrom] at hreplay
      intro candidate hcandidate
      simpa [hreplay] using hcandidate
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      have htail :
          terminalActive ⊆ step.afterActive :=
        ih hrest (fun step' hstep' => hmono step' (by simp [hstep']))
      intro candidate hcandidate
      have hbefore_mem : candidate ∈ step.beforeActive :=
        hmono step (by simp) (htail hcandidate)
      simpa [hbefore] using hbefore_mem

/--
Along a replay whose steps are active-set monotone, the terminal active set is
contained in every indexed step's pre-active set.
-/
theorem terminalActive_subset_beforeActive_of_replayStepsFrom_activeMonotone
    {Candidate : Type*} {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hmono : ∀ step, step ∈ steps → step.activeMonotone)
    (i : Fin steps.length) :
    terminalActive ⊆ (steps.get i).beforeActive := by
  induction steps generalizing startActive with
  | nil =>
      exact Fin.elim0 i
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      cases i with
      | mk n hn =>
          cases n with
          | zero =>
              have htail :
                  terminalActive ⊆ step.afterActive :=
                terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
                  hrest
                  (fun step' hstep' => hmono step' (by simp [hstep']))
              intro candidate hcandidate
              have hbefore_mem : candidate ∈ step.beforeActive :=
                hmono step (by simp) (htail hcandidate)
              simpa using hbefore_mem
          | succ n =>
              have hn_rest : n < rest.length := by
                simpa using Nat.succ_lt_succ_iff.mp hn
              simpa using
                ih hrest
                  (fun step' hstep' => hmono step' (by simp [hstep']))
                  ⟨n, hn_rest⟩

/--
In a replaying trace, the first step starts at the supplied initial active set.
-/
theorem replayStepsFrom_get_zero_beforeActive_eq_startActive
    {Candidate : Type*} {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (h0 : 0 < steps.length) :
    (steps.get ⟨0, h0⟩).beforeActive = startActive := by
  cases steps with
  | nil =>
      simp at h0
  | cons step rest =>
      simpa [replayStepsFrom] using hreplay.1

/--
At every indexed step of a replay whose steps are active-set monotone, the
step's pre-active set is contained in the initial active set.
-/
theorem beforeActive_subset_startActive_of_replaysFrom_activeMonotone
    {Candidate : Type*} {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hmono : ∀ step, step ∈ trace.steps → step.activeMonotone)
    (i : Fin trace.steps.length) :
    (trace.steps.get i).beforeActive ⊆ startActive := by
  exact terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
    (replaysFrom_take_get_beforeActive hreplay i)
    (fun step hstep => hmono step (List.mem_of_mem_take hstep))

/--
At every indexed step of a replay whose steps remove their focused candidates,
the step's pre-active set is contained in the initial active set.
-/
theorem beforeActive_subset_startActive_of_replaysFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove : ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (i : Fin trace.steps.length) :
    (trace.steps.get i).beforeActive ⊆ startActive := by
  exact beforeActive_subset_startActive_of_replaysFrom_activeMonotone
    hreplay
    (fun step hstep =>
      activeMonotone_of_removesFocusedCandidate (hremove step hstep))
    i

/--
At every indexed step of a replay whose steps remove focused candidates, the
terminal active set is contained in the step's pre-active set.
-/
theorem terminalActive_subset_beforeActive_of_replaysFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove : ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (i : Fin trace.steps.length) :
    terminalActive ⊆ (trace.steps.get i).beforeActive := by
  exact terminalActive_subset_beforeActive_of_replayStepsFrom_activeMonotone
    hreplay
    (fun step hstep =>
      activeMonotone_of_removesFocusedCandidate (hremove step hstep))
    i

/--
Along a replayed prefix whose steps remove their focused candidates, a
candidate that starts active remains active at the prefix terminal set if no
step in the prefix focuses that candidate.
-/
theorem mem_terminalActive_of_replayStepsFrom_not_focused
    {Candidate : Type*} [DecidableEq Candidate]
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {candidate : Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hremove :
      ∀ step, step ∈ steps → step.removesFocusedCandidate)
    (hstart : candidate ∈ startActive)
    (hnot_focus :
      ∀ step, step ∈ steps → step.focus ≠ some candidate) :
    candidate ∈ terminalActive := by
  induction steps generalizing startActive with
  | nil =>
      simp [replayStepsFrom] at hreplay
      rw [hreplay]
      exact hstart
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      rcases hremove step (by simp) with ⟨focused, hfocus, hafter⟩
      have hfocused_ne : focused ≠ candidate := by
        intro hfocused_eq
        exact hnot_focus step (by simp) (by simpa [hfocus, hfocused_eq])
      have hcandidate_before : candidate ∈ step.beforeActive := by
        simpa [hbefore] using hstart
      have hcandidate_after : candidate ∈ step.afterActive := by
        rw [hafter]
        exact Finset.mem_erase.mpr
          ⟨fun hcandidate_eq => hfocused_ne hcandidate_eq.symm,
            hcandidate_before⟩
      exact ih hrest
        (fun step' hstep' => hremove step' (by simp [hstep']))
        hcandidate_after
        (fun step' hstep' => hnot_focus step' (by simp [hstep']))

/--
Trace-level prefix form: if a candidate starts active and none of the replayed
steps before index `i` focuses it, then the candidate is active in step `i`'s
`beforeActive` set.
-/
theorem mem_beforeActive_of_replaysFrom_not_focused_before
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    {candidate : Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove :
      ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (hstart : candidate ∈ startActive)
    (i : Fin trace.steps.length)
    (hnot_focus :
      ∀ step, step ∈ trace.steps.take i.1 →
        step.focus ≠ some candidate) :
    candidate ∈ (trace.steps.get i).beforeActive := by
  exact mem_terminalActive_of_replayStepsFrom_not_focused
    (replaysFrom_take_get_beforeActive hreplay i)
    (fun step hstep => hremove step (List.mem_of_mem_take hstep))
    hstart hnot_focus

/--
First-focused exit rank for a candidate in a trace step list. The rank is
one plus the first step index that focuses the candidate; if no step focuses
the candidate, it is one past the end of the list.
-/
def firstFocusRankOfSteps {Candidate : Type*} [DecidableEq Candidate]
    (steps : List (STVStep Candidate)) (candidate : Candidate) : ℕ :=
  match steps with
  | [] => 1
  | step :: rest =>
      if step.focus = some candidate then
        1
      else
        firstFocusRankOfSteps rest candidate + 1

/-- First-focused exit rank for a candidate in a trace. -/
def firstFocusRank {Candidate : Type*} [DecidableEq Candidate]
    (trace : STVTrace Candidate) (candidate : Candidate) : ℕ :=
  firstFocusRankOfSteps trace.steps candidate

/-- No step before the first-focused exit rank focuses the candidate. -/
theorem not_focus_of_mem_take_lt_firstFocusRankOfSteps
    {Candidate : Type*} [DecidableEq Candidate]
    {steps : List (STVStep Candidate)} {candidate : Candidate} {i : ℕ}
    (hi : i < firstFocusRankOfSteps steps candidate) :
    ∀ step, step ∈ steps.take i → step.focus ≠ some candidate := by
  induction steps generalizing i with
  | nil =>
      intro step hstep
      simp at hstep
  | cons head rest ih =>
      by_cases hhead : head.focus = some candidate
      · have hi_zero : i = 0 := by
          exact Nat.eq_zero_of_le_zero
            (Nat.le_of_lt_succ
              (by simpa [firstFocusRankOfSteps, hhead] using hi))
        subst i
        intro step hstep
        simp at hstep
      · cases i with
        | zero =>
            intro step hstep
            simp at hstep
        | succ i =>
            have hi_rest : i < firstFocusRankOfSteps rest candidate := by
              exact Nat.succ_lt_succ_iff.mp
                (by simpa [firstFocusRankOfSteps, hhead] using hi)
            intro step hstep
            simp [List.take] at hstep
            rcases hstep with hstep | hstep
            · subst step
              exact hhead
            · exact ih hi_rest step hstep

/-- Trace-level wrapper for `not_focus_of_mem_take_lt_firstFocusRankOfSteps`. -/
theorem not_focus_of_mem_take_lt_firstFocusRank
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {candidate : Candidate} {i : ℕ}
    (hi : i < trace.firstFocusRank candidate) :
    ∀ step, step ∈ trace.steps.take i → step.focus ≠ some candidate := by
  exact not_focus_of_mem_take_lt_firstFocusRankOfSteps
    (steps := trace.steps) (candidate := candidate) hi

/--
If the first `i` steps do not focus a candidate and `i` is a valid step index,
then `i` is before that candidate's first-focused exit rank.
-/
theorem lt_firstFocusRankOfSteps_of_not_focus_take
    {Candidate : Type*} [DecidableEq Candidate]
    {steps : List (STVStep Candidate)} {candidate : Candidate} {i : ℕ}
    (hi_len : i < steps.length)
    (hnot_focus :
      ∀ step, step ∈ steps.take i → step.focus ≠ some candidate) :
    i < firstFocusRankOfSteps steps candidate := by
  induction steps generalizing i with
  | nil =>
      simp at hi_len
  | cons head rest ih =>
      by_cases hhead : head.focus = some candidate
      · cases i with
        | zero =>
            simp [firstFocusRankOfSteps, hhead]
        | succ i =>
            have hhead_mem : head ∈ (head :: rest).take (i + 1) := by
              simp
            exact (hnot_focus head hhead_mem hhead).elim
      · cases i with
        | zero =>
            simp [firstFocusRankOfSteps, hhead]
        | succ i =>
            have hi_rest_len : i < rest.length := by
              exact Nat.succ_lt_succ_iff.mp hi_len
            have hnot_focus_rest :
                ∀ step, step ∈ rest.take i → step.focus ≠ some candidate := by
              intro step hstep
              exact hnot_focus step (by simp [List.take, hstep])
            simpa [firstFocusRankOfSteps, hhead, Nat.succ_eq_add_one] using
              Nat.succ_lt_succ (ih hi_rest_len hnot_focus_rest)

/--
Along a replayed prefix whose steps remove focused candidates, any candidate
that is still active at the terminal active set was not focused in that prefix.
-/
theorem not_focused_of_mem_terminalActive_of_replayStepsFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {candidate : Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hremove :
      ∀ step, step ∈ steps → step.removesFocusedCandidate)
    (hterminal : candidate ∈ terminalActive) :
    ∀ step, step ∈ steps → step.focus ≠ some candidate := by
  induction steps generalizing startActive with
  | nil =>
      intro step hstep
      simp at hstep
  | cons head rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨_hbefore, hrest⟩
      have htail_subset :
          terminalActive ⊆ head.afterActive :=
        terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
          hrest
          (fun step hstep =>
            activeMonotone_of_removesFocusedCandidate
              (hremove step (by simp [hstep])))
      have hcandidate_after : candidate ∈ head.afterActive :=
        htail_subset hterminal
      rcases hremove head (by simp) with ⟨focused, hfocus, hafter⟩
      have hhead_not : head.focus ≠ some candidate := by
        intro hfocus_candidate
        have hfocused_eq : focused = candidate :=
          Option.some.inj (hfocus.symm.trans hfocus_candidate)
        subst focused
        rw [hafter] at hcandidate_after
        exact (Finset.mem_erase.mp hcandidate_after).1 rfl
      have htail_not :
          ∀ step, step ∈ rest → step.focus ≠ some candidate :=
        ih hrest
          (fun step hstep => hremove step (by simp [hstep]))
      intro step hstep
      simp at hstep
      rcases hstep with hstep | hstep
      · subst step
        exact hhead_not
      · exact htail_not step hstep

/--
If a candidate is active in an indexed step of a replay whose steps remove
focused candidates, then the step index is before that candidate's first-focused
exit rank.
-/
theorem index_lt_firstFocusRank_of_mem_beforeActive_of_replaysFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    {candidate : Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove :
      ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (i : Fin trace.steps.length)
    (hactive : candidate ∈ (trace.steps.get i).beforeActive) :
    i.1 < trace.firstFocusRank candidate := by
  have hprefix_replay :
      replayStepsFrom (trace.steps.take i.1) startActive
        (trace.steps.get i).beforeActive :=
    replaysFrom_take_get_beforeActive hreplay i
  have hnot_focus :
      ∀ step, step ∈ trace.steps.take i.1 → step.focus ≠ some candidate :=
    not_focused_of_mem_terminalActive_of_replayStepsFrom_removesFocusedCandidate
      hprefix_replay
      (fun step hstep => hremove step (List.mem_of_mem_take hstep))
      hactive
  exact lt_firstFocusRankOfSteps_of_not_focus_take
    (steps := trace.steps) (candidate := candidate) i.2 hnot_focus

/--
A trace whose elimination steps remove focused group candidates has strictly
decreasing active-group cardinality at those elimination steps.
-/
theorem eliminationActiveGroupCardDecreases_of_eliminationRemovesFromGroup
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {group : Finset Candidate}
    (htrace : trace.eliminationRemovesFromGroup group) :
    trace.eliminationActiveGroupCardDecreases group := by
  intro step hstep hkind
  rcases htrace step hstep hkind with
    ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩
  exact STVStep.card_afterActive_inter_lt_beforeActive_inter_of_removesFocusedCandidate
    ⟨loser, hfocus, hafter⟩ hfocus hloser_group hloser_active

/--
A trace whose elimination steps remove focused group candidates removes exactly
one active group candidate at those elimination steps.
-/
theorem eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {group : Finset Candidate}
    (htrace : trace.eliminationRemovesFromGroup group) :
    trace.eliminationActiveGroupCardAddOneEq group := by
  intro step hstep hkind
  rcases htrace step hstep hkind with
    ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩
  exact STVStep.card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
    ⟨loser, hfocus, hafter⟩ hfocus hloser_group hloser_active

/--
If a replayed trace consists of eliminations and each elimination removes from
the named group, then the number of terminal active group candidates plus the
number of replayed steps is the number of initially active group candidates.
-/
theorem terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {startActive terminalActive group : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (htrace : trace.eliminationRemovesFromGroup group) :
    (terminalActive ∩ group).card + trace.steps.length =
      (startActive ∩ group).card := by
  cases trace with
  | mk steps =>
      induction steps generalizing startActive with
      | nil =>
          simp [replaysFrom, replayStepsFrom] at hreplay ⊢
          rw [hreplay]
      | cons step rest ih =>
          simp only [replaysFrom, replayStepsFrom] at hreplay
          rcases hreplay with ⟨hbefore, hrest_replay⟩
          have hkind : step.kind = StepKind.eliminate :=
            hall_eliminate step (by simp)
          rcases htrace step (by simp) hkind with
            ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩
          have hstep_card :
              (step.afterActive ∩ group).card + 1 =
                (step.beforeActive ∩ group).card :=
            STVStep.card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
              ⟨loser, hfocus, hafter⟩ hfocus hloser_group hloser_active
          have hrest_eliminate :
              ∀ step', step' ∈ rest → step'.kind = StepKind.eliminate := by
            intro step' hstep'
            exact hall_eliminate step' (by simp [hstep'])
          have hrest_trace :
              ({ steps := rest } : STVTrace Candidate).eliminationRemovesFromGroup
                group := by
            intro step' hstep' hkind'
            exact htrace step' (by simp [hstep']) hkind'
          have hrest_card :
              (terminalActive ∩ group).card + rest.length =
                (step.afterActive ∩ group).card :=
            ih hrest_replay hrest_eliminate hrest_trace
          calc
            (terminalActive ∩ group).card + (step :: rest).length
                = ((terminalActive ∩ group).card + rest.length) + 1 := by
                    simp [Nat.add_assoc]
            _ = (step.afterActive ∩ group).card + 1 := by
                    rw [hrest_card]
            _ = (step.beforeActive ∩ group).card := hstep_card
            _ = (startActive ∩ group).card := by rw [hbefore]

/--
If a replayed all-elimination trace removes from the named group for exactly
the number of initially active group candidates, no group candidate remains
active at the terminal state.
-/
theorem terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {startActive terminalActive group : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (htrace : trace.eliminationRemovesFromGroup group)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ := by
  have hsum :
      (terminalActive ∩ group).card + trace.steps.length =
        (startActive ∩ group).card :=
    terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
      hreplay hall_eliminate htrace
  have hle :
      (terminalActive ∩ group).card + trace.steps.length ≤
        0 + trace.steps.length := by
    rw [hsum, hlength]
    simp
  have hcard_le_zero : (terminalActive ∩ group).card ≤ 0 :=
    Nat.le_of_add_le_add_right hle
  have hcard_zero : (terminalActive ∩ group).card = 0 :=
    Nat.eq_zero_of_le_zero hcard_le_zero
  exact Finset.card_eq_zero.mp hcard_zero

end STVTrace

/--
A deterministic choice rule for finite minimum-tally elimination steps.

The rule is intentionally separated from the active-set runner below: papers
can instantiate it with the tie-breaking convention used in the source, while
the library proves the trace facts that follow from choosing an active minimal
candidate.
-/
structure MinimalTallyChoiceRule (Candidate : Type*) where
  choose : Finset Candidate → (Candidate → ℕ) → Option Candidate

namespace MinimalTallyChoiceRule

/-- The rule chooses some candidate whenever the eligible set is nonempty. -/
def Total {Candidate : Type*} (choice : MinimalTallyChoiceRule Candidate) :
    Prop :=
  ∀ active tally, active.Nonempty →
    ∃ focused, choice.choose active tally = some focused

/-- Any returned candidate belongs to the eligible set. -/
def ChoosesActive {Candidate : Type*}
    (choice : MinimalTallyChoiceRule Candidate) : Prop :=
  ∀ {active tally focused},
    choice.choose active tally = some focused → focused ∈ active

/-- Any returned candidate has minimum tally on the eligible set. -/
def SelectsMinimal {Candidate : Type*}
    (choice : MinimalTallyChoiceRule Candidate) : Prop :=
  ∀ {active tally focused},
    choice.choose active tally = some focused →
      ∀ candidate, candidate ∈ active → tally focused ≤ tally candidate

/--
Canonical noncomputable finite tie-breaking for minimum-tally eliminations.

This keeps paper statements from carrying a generic choice-rule object when the
source only needs some deterministic minimum-tally tie-breaking convention.
-/
noncomputable def canonical (Candidate : Type*) :
    MinimalTallyChoiceRule Candidate where
  choose active tally :=
    if hactive : active.Nonempty then
      some (Classical.choose (Finset.exists_min_image active tally hactive))
    else
      none

theorem canonical_choose_eq_some_of_nonempty {Candidate : Type*}
    {active : Finset Candidate} {tally : Candidate → ℕ}
    (hactive : active.Nonempty) :
    (canonical Candidate).choose active tally =
      some (Classical.choose
        (Finset.exists_min_image active tally hactive)) := by
  simp [canonical, hactive]

theorem canonical_choosesActive {Candidate : Type*} :
    (canonical Candidate).ChoosesActive := by
  intro active tally focused hchoose
  classical
  by_cases hactive : active.Nonempty
  · have hfocused :
        focused =
          Classical.choose
            (Finset.exists_min_image active tally hactive) := by
      simpa [canonical, hactive] using hchoose.symm
    subst focused
    exact
      (Classical.choose_spec
        (Finset.exists_min_image active tally hactive)).1
  · simp [canonical, hactive] at hchoose

theorem canonical_total {Candidate : Type*} :
    (canonical Candidate).Total := by
  intro active tally hactive
  exact ⟨Classical.choose
      (Finset.exists_min_image active tally hactive),
    canonical_choose_eq_some_of_nonempty hactive⟩

theorem canonical_selectsMinimal {Candidate : Type*} :
    (canonical Candidate).SelectsMinimal := by
  intro active tally focused hchoose candidate hcandidate
  classical
  by_cases hactive : active.Nonempty
  · have hfocused :
        focused =
          Classical.choose
            (Finset.exists_min_image active tally hactive) := by
      simpa [canonical, hactive] using hchoose.symm
    subst focused
    exact
      (Classical.choose_spec
        (Finset.exists_min_image active tally hactive)).2
        candidate hcandidate
  · simp [canonical, hactive] at hchoose

end MinimalTallyChoiceRule

/-- A single generated elimination step that removes its focused candidate. -/
def groupEliminationStep {Candidate : Type*} [DecidableEq Candidate]
    (active : Finset Candidate) (focused : Candidate)
    (tally : Candidate → ℕ) : STVStep Candidate where
  beforeActive := active
  afterActive := active.erase focused
  kind := StepKind.eliminate
  focus := some focused
  tally := tally

/--
Generate a single minimum-tally elimination step from a source choice rule.

The step is absent if the rule returns no candidate or returns a candidate
outside the active set. This keeps the executable choice boundary explicit
while letting downstream papers consume ordinary `STVStep` facts.
-/
def minimalTallyEliminationStep {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate)
    (active : Finset Candidate) (tally : Candidate → ℕ) :
    Option (STVStep Candidate) :=
  match choice.choose active tally with
  | none => none
  | some focused =>
      if focused ∈ active then
        some (groupEliminationStep active focused tally)
      else
        none

/--
A total, active-respecting source choice rule generates a single elimination
step whenever the active set is nonempty.
-/
theorem minimalTallyEliminationStep_exists_of_total
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    {active : Finset Candidate} {tally : Candidate → ℕ}
    (hactive_nonempty : active.Nonempty) :
    ∃ step, minimalTallyEliminationStep choice active tally = some step := by
  rcases htotalChoice active tally hactive_nonempty with ⟨focused, hchoose⟩
  have hfocused : focused ∈ active := hactiveChoice hchoose
  exact ⟨groupEliminationStep active focused tally, by
    simp [minimalTallyEliminationStep, hchoose, hfocused]⟩

/-- A generated single elimination step has the requested pre-active set. -/
theorem minimalTallyEliminationStep_beforeActive_eq
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {active : Finset Candidate} {tally : Candidate → ℕ}
    {step : STVStep Candidate}
    (hstep : minimalTallyEliminationStep choice active tally = some step) :
    step.beforeActive = active := by
  unfold minimalTallyEliminationStep at hstep
  cases hchoose : choice.choose active tally with
  | none =>
      simp [hchoose] at hstep
  | some focused =>
      by_cases hfocused : focused ∈ active
      · simp [hchoose, hfocused, groupEliminationStep] at hstep
        subst step
        rfl
      · simp [hchoose, hfocused] at hstep

/-- A generated single elimination step has the requested tally function. -/
theorem minimalTallyEliminationStep_tally_eq
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {active : Finset Candidate} {tally : Candidate → ℕ}
    {step : STVStep Candidate}
    (hstep : minimalTallyEliminationStep choice active tally = some step) :
    step.tally = tally := by
  unfold minimalTallyEliminationStep at hstep
  cases hchoose : choice.choose active tally with
  | none =>
      simp [hchoose] at hstep
  | some focused =>
      by_cases hfocused : focused ∈ active
      · simp [hchoose, hfocused, groupEliminationStep] at hstep
        subst step
        rfl
      · simp [hchoose, hfocused] at hstep

/-- A generated single elimination step removes its focused candidate. -/
theorem minimalTallyEliminationStep_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {active : Finset Candidate} {tally : Candidate → ℕ}
    {step : STVStep Candidate}
    (hstep : minimalTallyEliminationStep choice active tally = some step) :
    step.removesFocusedCandidate := by
  unfold minimalTallyEliminationStep at hstep
  cases hchoose : choice.choose active tally with
  | none =>
      simp [hchoose] at hstep
  | some focused =>
      by_cases hfocused : focused ∈ active
      · simp [hchoose, hfocused, groupEliminationStep] at hstep
        subst step
        exact ⟨focused, rfl, rfl⟩
      · simp [hchoose, hfocused] at hstep

/--
A generated single elimination step from a minimal source choice rule is a
minimum-tally elimination step on the full active set.
-/
theorem minimalTallyEliminationStep_eliminatesMinimalTally
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    (hminimalChoice : choice.SelectsMinimal)
    {active : Finset Candidate} {tally : Candidate → ℕ}
    {step : STVStep Candidate}
    (hstep : minimalTallyEliminationStep choice active tally = some step) :
    step.eliminatesMinimalTally := by
  unfold minimalTallyEliminationStep at hstep
  cases hchoose : choice.choose active tally with
  | none =>
      simp [hchoose] at hstep
  | some focused =>
      by_cases hfocused : focused ∈ active
      · simp [hchoose, hfocused, groupEliminationStep] at hstep
        subst step
        exact ⟨rfl, focused, rfl, hfocused, by
          intro candidate hcandidate
          exact hminimalChoice hchoose candidate hcandidate⟩
      · simp [hchoose, hfocused] at hstep

/--
Run a finite group-elimination prefix for at most `rounds` rounds.

At each round, the rule chooses from `active ∩ group`; the generated step is an
ordinary candidate-level elimination step on the full active set. If the rule
does not return an eligible candidate, the run stops. The source-specific tally
function is indexed by the current active set.
-/
noncomputable def minimalGroupEliminationGeneratedSteps {Candidate : Type*}
    [DecidableEq Candidate] (choice : MinimalTallyChoiceRule Candidate)
    (group : Finset Candidate) (tallyOf : Finset Candidate → Candidate → ℕ) :
    ℕ → Finset Candidate → List (STVStep Candidate)
  | 0, _active => []
  | rounds + 1, active =>
      match choice.choose (active ∩ group) (tallyOf active) with
      | none => []
      | some focused =>
          if hfocused : focused ∈ active ∩ group then
            let step := groupEliminationStep active focused (tallyOf active)
            step ::
            minimalGroupEliminationGeneratedSteps choice group tallyOf
                rounds step.afterActive
          else
            []

/-- Terminal active set of `minimalGroupEliminationGeneratedSteps`. -/
noncomputable def minimalGroupEliminationTerminalActive {Candidate : Type*}
    [DecidableEq Candidate] (choice : MinimalTallyChoiceRule Candidate)
    (group : Finset Candidate) (tallyOf : Finset Candidate → Candidate → ℕ) :
    ℕ → Finset Candidate → Finset Candidate
  | 0, active => active
  | rounds + 1, active =>
      match choice.choose (active ∩ group) (tallyOf active) with
      | none => active
      | some focused =>
          if hfocused : focused ∈ active ∩ group then
            let step := groupEliminationStep active focused (tallyOf active)
            minimalGroupEliminationTerminalActive choice group tallyOf
              rounds step.afterActive
          else
            active

/-- Trace wrapper for the generated group-elimination prefix. -/
noncomputable def minimalGroupEliminationGeneratedTrace {Candidate : Type*}
    [DecidableEq Candidate] (choice : MinimalTallyChoiceRule Candidate)
    (group : Finset Candidate) (tallyOf : Finset Candidate → Candidate → ℕ)
    (rounds : ℕ) (initialActive : Finset Candidate) : STVTrace Candidate where
  steps :=
    minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
      initialActive

/--
The generated group-elimination prefix replays active sets from its start to
its computed terminal active set.
-/
theorem minimalGroupEliminationGeneratedSteps_replayStepsFrom
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active,
      STVTrace.replayStepsFrom
        (minimalGroupEliminationGeneratedSteps choice group tallyOf rounds active)
        active
        (minimalGroupEliminationTerminalActive choice group tallyOf rounds
          active) := by
  intro rounds
  induction rounds with
  | zero =>
      intro active
      simp [minimalGroupEliminationGeneratedSteps,
        minimalGroupEliminationTerminalActive, STVTrace.replayStepsFrom]
  | succ rounds ih =>
      intro active
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps,
            minimalGroupEliminationTerminalActive, hchoose,
            STVTrace.replayStepsFrom]
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps,
              minimalGroupEliminationTerminalActive, groupEliminationStep,
              hchoose, hfocused, STVTrace.replayStepsFrom]
            exact ih (active.erase focused)
          · simp [minimalGroupEliminationGeneratedSteps,
              minimalGroupEliminationTerminalActive, hchoose, hfocused,
              STVTrace.replayStepsFrom]

/-- Every generated group-elimination step is an elimination step. -/
theorem minimalGroupEliminationGeneratedSteps_all_eliminate
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active →
        step.kind = StepKind.eliminate := by
  intro rounds
  induction rounds with
  | zero =>
      intro active step hstep
      simp [minimalGroupEliminationGeneratedSteps] at hstep
  | succ rounds ih =>
      intro active step hstep
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps, hchoose] at hstep
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
              hchoose, hfocused] at hstep
            rcases hstep with hhead | htail
            · subst step
              simp
            · exact ih (active.erase focused) step htail
          · simp [minimalGroupEliminationGeneratedSteps, hchoose, hfocused]
              at hstep

/-- Every generated group-elimination step removes its focused candidate. -/
theorem minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active →
        step.removesFocusedCandidate := by
  intro rounds
  induction rounds with
  | zero =>
      intro active step hstep
      simp [minimalGroupEliminationGeneratedSteps] at hstep
  | succ rounds ih =>
      intro active step hstep
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps, hchoose] at hstep
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
              hchoose, hfocused] at hstep
            rcases hstep with hhead | htail
            · subst step
              exact ⟨focused, rfl, rfl⟩
            · exact ih (active.erase focused) step htail
          · simp [minimalGroupEliminationGeneratedSteps, hchoose, hfocused]
              at hstep

/--
Every generated step has an active focused member of the eliminated group.
-/
theorem minimalGroupEliminationGeneratedSteps_group_active_at_step
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive := by
  intro rounds
  induction rounds with
  | zero =>
      intro active step hstep
      simp [minimalGroupEliminationGeneratedSteps] at hstep
  | succ rounds ih =>
      intro active step hstep
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps, hchoose] at hstep
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
              hchoose, hfocused] at hstep
            rcases hstep with hhead | htail
            · subst step
              exact ⟨focused, (Finset.mem_inter.mp hfocused).2,
                (Finset.mem_inter.mp hfocused).1⟩
            · exact ih (active.erase focused) step htail
          · simp [minimalGroupEliminationGeneratedSteps, hchoose, hfocused]
              at hstep

/--
Every generated step's pre-active set is a subset of the run's initial active
set.
-/
theorem minimalGroupEliminationGeneratedSteps_beforeActive_subset_initial
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active →
        step.beforeActive ⊆ active := by
  intro rounds
  induction rounds with
  | zero =>
      intro active step hstep
      simp [minimalGroupEliminationGeneratedSteps] at hstep
  | succ rounds ih =>
      intro active step hstep
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps, hchoose] at hstep
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
              hchoose, hfocused] at hstep
            rcases hstep with hhead | htail
            · subst step
              simp
            · have htail_subset :=
                ih (active.erase focused) step htail
              intro candidate hcandidate
              exact (Finset.mem_erase.mp (htail_subset hcandidate)).2
          · simp [minimalGroupEliminationGeneratedSteps, hchoose, hfocused]
              at hstep

/--
If the initial active set is contained in a candidate set, every generated
step's pre-active set is contained in that candidate set.
-/
theorem minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ)
    {initialActive candidates : Finset Candidate}
    (hinitial_subset : initialActive ⊆ candidates) :
    ∀ rounds, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          initialActive →
        step.beforeActive ⊆ candidates := by
  intro rounds step hstep
  exact subset_trans
    (minimalGroupEliminationGeneratedSteps_beforeActive_subset_initial
      choice group tallyOf rounds initialActive step hstep)
    hinitial_subset

/--
Every generated group-elimination step uses the source tally function evaluated
at its own pre-active set.
-/
theorem minimalGroupEliminationGeneratedSteps_tally_eq
    {Candidate : Type*} [DecidableEq Candidate]
    (choice : MinimalTallyChoiceRule Candidate) (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active →
        step.tally = tallyOf step.beforeActive := by
  intro rounds
  induction rounds with
  | zero =>
      intro active step hstep
      simp [minimalGroupEliminationGeneratedSteps] at hstep
  | succ rounds ih =>
      intro active step hstep
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps, hchoose] at hstep
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
              hchoose, hfocused] at hstep
            rcases hstep with hhead | htail
            · subst step
              rfl
            · exact ih (active.erase focused) step htail
          · simp [minimalGroupEliminationGeneratedSteps, hchoose, hfocused]
              at hstep

/--
The ordinary integer tally of first-active ballot support at an active set.

This is the concrete RCV/STV tally used by simulator-style paper endpoints:
each active candidate's tally is the number of voters whose next active ballot
entry is that candidate.
-/
def profileActiveTallyOf {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate) :
    Finset Candidate → Candidate → ℕ :=
  fun active candidate =>
    (Ballot.activeSupport voters ballots active candidate).card

/--
For profile tallies, eliminating one active source candidate can increase a
remaining target's tally by at most the source's previous tally.
-/
theorem profileActiveTallyOf_erase_le_self_add_source
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    {active : Finset Candidate} {source target : Candidate}
    (hsource : source ∈ active)
    (htarget : target ∈ active.erase source) :
    profileActiveTallyOf voters ballots (active.erase source) target ≤
      profileActiveTallyOf voters ballots active target +
        profileActiveTallyOf voters ballots active source :=
  Ballot.activeSupport_card_erase_le_activeSupport_card_add_source
    (voters := voters) (ballots := ballots) hsource htarget

/--
For profile tallies, erasing a source candidate can increase a remaining
target's tally by at most the source's previous tally. This form also covers
the degenerate case where the source was not active.
-/
theorem profileActiveTallyOf_erase_le_self_add_source_of_mem
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    {active : Finset Candidate} {source target : Candidate}
    (htarget : target ∈ active.erase source) :
    profileActiveTallyOf voters ballots (active.erase source) target ≤
      profileActiveTallyOf voters ballots active target +
        profileActiveTallyOf voters ballots active source := by
  by_cases hsource : source ∈ active
  · exact profileActiveTallyOf_erase_le_self_add_source
      voters ballots hsource htarget
  · have herase : active.erase source = active := by
      ext candidate
      simp [hsource]
    rw [herase]
    exact Nat.le_add_right
      (profileActiveTallyOf voters ballots active target)
      (profileActiveTallyOf voters ballots active source)

/--
If every voter's first choice lies in the active set, then the profile active
tally of each candidate is bounded by that candidate's first-choice count.
-/
theorem profileActiveTallyOf_le_firstChoiceCount_of_forall_firstChoiceIn
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    {active : Finset Candidate} {candidate : Candidate}
    (hfirst : ∀ voter, voter ∈ voters →
      Ballot.firstChoiceIn (ballots voter) active) :
    profileActiveTallyOf voters ballots active candidate ≤
      Ballot.firstChoiceCount voters ballots candidate :=
  Ballot.activeSupport_card_le_firstChoiceCount_of_forall_firstChoiceIn
    (voters := voters) (ballots := ballots) (active := active)
    (candidate := candidate) hfirst

/--
Generated group-elimination steps with `profileActiveTallyOf` carry exactly
the active-support ballot counts as their step tallies.
-/
theorem minimalGroupEliminationGeneratedSteps_profileActiveTally_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {group : Finset Candidate} {rounds : ℕ} {initialActive : Finset Candidate}
    {step : STVStep Candidate}
    (hstep :
      step ∈ minimalGroupEliminationGeneratedSteps choice group
        (profileActiveTallyOf voters ballots) rounds initialActive)
    (candidate : Candidate) :
    step.tally candidate =
      (Ballot.activeSupport voters ballots step.beforeActive candidate).card := by
  have htally :
      step.tally =
        profileActiveTallyOf voters ballots step.beforeActive :=
    minimalGroupEliminationGeneratedSteps_tally_eq
      choice group (profileActiveTallyOf voters ballots) rounds initialActive
      step hstep
  rw [htally]
  rfl

/--
Canonical generated group-elimination steps using the concrete profile tally.
-/
noncomputable def canonicalProfileGroupEliminationGeneratedSteps
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate) : List (STVStep Candidate) :=
  minimalGroupEliminationGeneratedSteps
    (MinimalTallyChoiceRule.canonical Candidate) group
    (profileActiveTallyOf voters ballots) rounds initialActive

/--
Terminal active set of the canonical profile-tally group-elimination runner.
-/
noncomputable def canonicalProfileGroupEliminationTerminalActive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate) : Finset Candidate :=
  minimalGroupEliminationTerminalActive
    (MinimalTallyChoiceRule.canonical Candidate) group
    (profileActiveTallyOf voters ballots) rounds initialActive

/--
Trace wrapper for the canonical profile-tally group-elimination runner.
-/
noncomputable def canonicalProfileGroupEliminationGeneratedTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate) : STVTrace Candidate where
  steps :=
    canonicalProfileGroupEliminationGeneratedSteps voters ballots group rounds
      initialActive

/--
Canonical profile-tally generated steps carry active-support ballot counts.
-/
theorem canonicalProfileGroupEliminationGeneratedSteps_tally_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {group : Finset Candidate} {rounds : ℕ} {initialActive : Finset Candidate}
    {step : STVStep Candidate}
    (hstep :
      step ∈ canonicalProfileGroupEliminationGeneratedSteps voters ballots
        group rounds initialActive)
    (candidate : Candidate) :
    step.tally candidate =
      (Ballot.activeSupport voters ballots step.beforeActive candidate).card := by
  exact
    minimalGroupEliminationGeneratedSteps_profileActiveTally_eq
      (choice := MinimalTallyChoiceRule.canonical Candidate)
      (voters := voters) (ballots := ballots) (group := group)
      (rounds := rounds) (initialActive := initialActive) hstep candidate

/--
Indexed steps of the canonical profile-tally generated trace carry exactly the
active-support ballot counts.
-/
theorem canonicalProfileGroupEliminationGeneratedTrace_get_tally_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate)
    (i :
      Fin
        (canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.length)
    (candidate : Candidate) :
    ((canonicalProfileGroupEliminationGeneratedTrace voters ballots group
        rounds initialActive).steps.get i).tally candidate =
      (Ballot.activeSupport voters ballots
        ((canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.get i).beforeActive candidate).card := by
  exact
    canonicalProfileGroupEliminationGeneratedSteps_tally_eq
      (voters := voters) (ballots := ballots) (group := group)
      (rounds := rounds) (initialActive := initialActive)
      (step :=
        (canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.get i)
      (by
        simpa [canonicalProfileGroupEliminationGeneratedTrace] using
          List.get_mem
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots group
              rounds initialActive).steps i)
      candidate

theorem canonicalProfileGroupEliminationGeneratedSteps_replayStepsFrom
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate) :
    STVTrace.replayStepsFrom
      (canonicalProfileGroupEliminationGeneratedSteps voters ballots group
        rounds initialActive)
      initialActive
      (canonicalProfileGroupEliminationTerminalActive voters ballots group
        rounds initialActive) := by
  simpa [canonicalProfileGroupEliminationGeneratedSteps,
    canonicalProfileGroupEliminationTerminalActive] using
    minimalGroupEliminationGeneratedSteps_replayStepsFrom
      (MinimalTallyChoiceRule.canonical Candidate) group
      (profileActiveTallyOf voters ballots) rounds initialActive

/--
Generated steps inherit the choice rule's group-minimality: their focused
candidate has minimum tally among the currently active group candidates.
-/
theorem minimalGroupEliminationGeneratedSteps_focus_group_minimal
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    (hminimalChoice : choice.SelectsMinimal)
    (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active, ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active →
        ∃ focused,
          step.focus = some focused ∧
            focused ∈ step.beforeActive ∩ group ∧
            ∀ candidate, candidate ∈ step.beforeActive ∩ group →
              step.tally focused ≤ step.tally candidate := by
  intro rounds
  induction rounds with
  | zero =>
      intro active step hstep
      simp [minimalGroupEliminationGeneratedSteps] at hstep
  | succ rounds ih =>
      intro active step hstep
      cases hchoose : choice.choose (active ∩ group) (tallyOf active) with
      | none =>
          simp [minimalGroupEliminationGeneratedSteps, hchoose] at hstep
      | some focused =>
          by_cases hfocused : focused ∈ active ∩ group
          · simp [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
              hchoose, hfocused] at hstep
            rcases hstep with hhead | htail
            · subst step
              refine ⟨focused, rfl, hfocused, ?_⟩
              intro candidate hcandidate
              exact hminimalChoice hchoose candidate hcandidate
            · exact ih (active.erase focused) step htail
          · simp [minimalGroupEliminationGeneratedSteps, hchoose, hfocused]
              at hstep

/--
If the choice rule is total on nonempty eligible sets and only returns eligible
candidates, running for the initial number of active group candidates generates
exactly that many elimination steps.
-/
theorem minimalGroupEliminationGeneratedSteps_length_eq
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ rounds active,
      rounds = (active ∩ group).card →
        (minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
          active).length = rounds := by
  intro rounds
  induction rounds with
  | zero =>
      intro active _hround
      simp [minimalGroupEliminationGeneratedSteps]
  | succ rounds ih =>
      intro active hround
      have hpos : 0 < (active ∩ group).card := by
        rw [← hround]
        exact Nat.succ_pos rounds
      have hnonempty : (active ∩ group).Nonempty :=
        Finset.card_pos.mp hpos
      rcases htotalChoice (active ∩ group) (tallyOf active) hnonempty with
        ⟨focused, hchoose⟩
      have hfocused : focused ∈ active ∩ group :=
        hactiveChoice hchoose
      have hafter_card : ((active.erase focused) ∩ group).card = rounds := by
        have hset :
            active.erase focused ∩ group =
              (active ∩ group).erase focused := by
          ext candidate
          by_cases hcandidate : candidate = focused
          · subst candidate
            simp [hfocused]
          · simp [hcandidate]
        have hcard :=
          Finset.card_erase_add_one hfocused
        rw [← hset] at hcard
        rw [← hround] at hcard
        have hsucc :
            Nat.succ ((active.erase focused ∩ group).card) =
              Nat.succ rounds := by
          simpa [Nat.succ_eq_add_one] using hcard
        exact Nat.succ.inj hsucc
      simpa [minimalGroupEliminationGeneratedSteps, groupEliminationStep,
        hchoose, hfocused,
        ih (active.erase focused) hafter_card.symm]

/--
Generated group-elimination traces remove a focused member of the target group
at every generated elimination step.
-/
theorem minimalGroupEliminationGeneratedTrace_eliminationRemovesFromGroup
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    (hminimalChoice : choice.SelectsMinimal)
    (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ)
    (rounds : ℕ) (initialActive : Finset Candidate) :
    (minimalGroupEliminationGeneratedTrace choice group tallyOf rounds
      initialActive).eliminationRemovesFromGroup group := by
  intro step hstep _hkind
  have hgenerated :
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf rounds
        initialActive := by
    simpa [minimalGroupEliminationGeneratedTrace] using hstep
  rcases minimalGroupEliminationGeneratedSteps_focus_group_minimal
      hminimalChoice group tallyOf rounds initialActive step hgenerated with
    ⟨focused, hfocus, hfocused_active_group, _hfocused_minimal⟩
  rcases minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
      choice group tallyOf rounds initialActive step hgenerated with
    ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = focused := by
    exact Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  exact ⟨focused, hfocus, (Finset.mem_inter.mp hfocused_active_group).2,
    (Finset.mem_inter.mp hfocused_active_group).1, hafter⟩

/--
If a generated group-elimination run is executed for exactly the initial number
of active group candidates, its terminal active set contains no group member.
-/
theorem minimalGroupEliminationTerminalActive_inter_group_eq_empty
    {Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (group : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ)
    (initialActive : Finset Candidate) :
    minimalGroupEliminationTerminalActive choice group tallyOf
        (initialActive ∩ group).card initialActive ∩ group = ∅ := by
  let trace : STVTrace Candidate :=
    minimalGroupEliminationGeneratedTrace choice group tallyOf
      (initialActive ∩ group).card initialActive
  have hreplay :
      trace.replaysFrom initialActive
        (minimalGroupEliminationTerminalActive choice group tallyOf
          (initialActive ∩ group).card initialActive) := by
    simpa [trace, minimalGroupEliminationGeneratedTrace, STVTrace.replaysFrom] using
      minimalGroupEliminationGeneratedSteps_replayStepsFrom choice group
        tallyOf (initialActive ∩ group).card initialActive
  have hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate choice group tallyOf
        (initialActive ∩ group).card initialActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have htrace :
      trace.eliminationRemovesFromGroup group := by
    simpa [trace] using
      minimalGroupEliminationGeneratedTrace_eliminationRemovesFromGroup
        (choice := choice) hminimalChoice group tallyOf
        (initialActive ∩ group).card initialActive
  have hlength :
      trace.steps.length = (initialActive ∩ group).card := by
    simpa [trace, minimalGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedSteps_length_eq
        (choice := choice) hactiveChoice htotalChoice group tallyOf
        (initialActive ∩ group).card initialActive rfl
  exact
    STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
      hreplay hall_eliminate htrace hlength

theorem canonicalProfileGroupEliminationGeneratedSteps_length_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) {rounds : ℕ}
    {initialActive : Finset Candidate}
    (hrounds : rounds = (initialActive ∩ group).card) :
    (canonicalProfileGroupEliminationGeneratedSteps voters ballots group
      rounds initialActive).length = rounds := by
  simpa [canonicalProfileGroupEliminationGeneratedSteps] using
    minimalGroupEliminationGeneratedSteps_length_eq
      (choice := MinimalTallyChoiceRule.canonical Candidate)
      MinimalTallyChoiceRule.canonical_choosesActive
      MinimalTallyChoiceRule.canonical_total group
      (profileActiveTallyOf voters ballots) rounds initialActive hrounds

/--
In a canonical profile-tally group-elimination trace, the pre-active set at
indexed step `i` has exactly `i` previously removed active candidates.
-/
theorem canonicalProfileGroupEliminationGeneratedTrace_get_beforeActive_card_add_index
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate)
    (i :
      Fin
        (canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.length) :
    ((canonicalProfileGroupEliminationGeneratedTrace voters ballots group
        rounds initialActive).steps.get i).beforeActive.card + i.1 =
      initialActive.card := by
  let trace :=
    canonicalProfileGroupEliminationGeneratedTrace voters ballots group rounds
      initialActive
  let terminalActive :=
    canonicalProfileGroupEliminationTerminalActive voters ballots group rounds
      initialActive
  have hreplay : trace.replaysFrom initialActive terminalActive := by
    simpa [trace, terminalActive, canonicalProfileGroupEliminationGeneratedTrace,
      STVTrace.replaysFrom] using
      canonicalProfileGroupEliminationGeneratedSteps_replayStepsFrom
        voters ballots group rounds initialActive
  have hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        (MinimalTallyChoiceRule.canonical Candidate) group
        (profileActiveTallyOf voters ballots) rounds initialActive step
        (by
          simpa [trace, canonicalProfileGroupEliminationGeneratedTrace,
            canonicalProfileGroupEliminationGeneratedSteps] using hstep)
  have hremove :
      ∀ step, step ∈ trace.steps → step.removesFocusedCandidate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
        (MinimalTallyChoiceRule.canonical Candidate) group
        (profileActiveTallyOf voters ballots) rounds initialActive step
        (by
          simpa [trace, canonicalProfileGroupEliminationGeneratedTrace,
            canonicalProfileGroupEliminationGeneratedSteps] using hstep)
  have hbefore_subset :
      (trace.steps.get i).beforeActive ⊆ initialActive :=
    STVTrace.beforeActive_subset_startActive_of_replaysFrom_removesFocusedCandidate
      hreplay hremove i
  have hprefix_replay :
      STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
        (trace.steps.get i).beforeActive :=
    STVTrace.replaysFrom_take_get_beforeActive hreplay i
  have hprefix_trace :
      ({ steps := trace.steps.take i.1 } : STVTrace Candidate).eliminationRemovesFromGroup
        initialActive := by
    intro step hstep hkind
    have hmem_trace : step ∈ trace.steps := List.mem_of_mem_take hstep
    have hgenerated :
        step ∈ minimalGroupEliminationGeneratedSteps
          (MinimalTallyChoiceRule.canonical Candidate) group
          (profileActiveTallyOf voters ballots) rounds initialActive := by
      simpa [trace, canonicalProfileGroupEliminationGeneratedTrace,
        canonicalProfileGroupEliminationGeneratedSteps] using hmem_trace
    rcases
      minimalGroupEliminationGeneratedSteps_focus_group_minimal
        (MinimalTallyChoiceRule.canonical_selectsMinimal
          (Candidate := Candidate)) group
        (profileActiveTallyOf voters ballots) rounds initialActive step
        hgenerated with
      ⟨focused, hfocus, hfocused_active_group, _hminimal⟩
    rcases
      minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
        (MinimalTallyChoiceRule.canonical Candidate) group
        (profileActiveTallyOf voters ballots) rounds initialActive step
        hgenerated with
      ⟨removed, hremoved_focus, hafter⟩
    have hremoved_eq : removed = focused :=
      Option.some.inj (hremoved_focus.symm.trans hfocus)
    subst removed
    have hfocused_active : focused ∈ step.beforeActive :=
      (Finset.mem_inter.mp hfocused_active_group).1
    have hfocused_initial : focused ∈ initialActive :=
      minimalGroupEliminationGeneratedSteps_beforeActive_subset_initial
        (MinimalTallyChoiceRule.canonical Candidate) group
        (profileActiveTallyOf voters ballots) rounds initialActive step
        hgenerated hfocused_active
    exact ⟨focused, hfocus, hfocused_initial, hfocused_active, hafter⟩
  have hprefix_all_eliminate :
      ∀ step, step ∈ (trace.steps.take i.1) →
        step.kind = StepKind.eliminate := by
    intro step hstep
    exact hall_eliminate step (List.mem_of_mem_take hstep)
  have hcard :=
    STVTrace.terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
      (trace := ({ steps := trace.steps.take i.1 } : STVTrace Candidate))
      (startActive := initialActive)
      (terminalActive := (trace.steps.get i).beforeActive)
      (group := initialActive)
      hprefix_replay hprefix_all_eliminate hprefix_trace
  have hterminal_inter :
      (trace.steps.get i).beforeActive ∩ initialActive =
        (trace.steps.get i).beforeActive := by
    ext candidate
    constructor
    · intro hcandidate
      exact (Finset.mem_inter.mp hcandidate).1
    · intro hcandidate
      exact Finset.mem_inter.mpr ⟨hcandidate, hbefore_subset hcandidate⟩
  have hstart_inter : initialActive ∩ initialActive = initialActive := by
    ext candidate
    simp
  have htake_length : (trace.steps.take i.1).length = i.1 := by
    have hi : i.1 ≤ trace.steps.length := by
      exact Nat.le_of_lt (by simpa [trace] using i.2)
    simp [List.length_take, hi]
  rw [hterminal_inter, hstart_inter, htake_length] at hcard
  simpa [trace] using hcard

/--
In a canonical profile-tally group-elimination trace, every indexed
pre-active set remains inside the initial active set.
-/
theorem canonicalProfileGroupEliminationGeneratedTrace_get_beforeActive_subset_initial
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate)
    (i :
      Fin
        (canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.length) :
    ((canonicalProfileGroupEliminationGeneratedTrace voters ballots group
        rounds initialActive).steps.get i).beforeActive ⊆ initialActive := by
  intro candidate hcandidate
  let trace :=
    canonicalProfileGroupEliminationGeneratedTrace voters ballots group rounds
      initialActive
  have hmem : trace.steps.get i ∈ trace.steps := by
    exact List.get_mem trace.steps i
  exact
    minimalGroupEliminationGeneratedSteps_beforeActive_subset_initial
      (MinimalTallyChoiceRule.canonical Candidate) group
      (profileActiveTallyOf voters ballots) rounds initialActive
      (trace.steps.get i)
      (by
        simpa [trace, canonicalProfileGroupEliminationGeneratedTrace,
          canonicalProfileGroupEliminationGeneratedSteps] using hmem)
      (by simpa [trace] using hcandidate)

/--
In a canonical profile-tally group-elimination trace, every candidate removed
before indexed step `i` belongs to the target group.
-/
theorem canonicalProfileGroupEliminationGeneratedTrace_removed_before_get_subset_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate)
    (i :
      Fin
        (canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.length) :
    initialActive \
        ((canonicalProfileGroupEliminationGeneratedTrace voters ballots group
          rounds initialActive).steps.get i).beforeActive ⊆
      group := by
  let trace :=
    canonicalProfileGroupEliminationGeneratedTrace voters ballots group rounds
      initialActive
  let terminalActive :=
    canonicalProfileGroupEliminationTerminalActive voters ballots group rounds
      initialActive
  have hreplay : trace.replaysFrom initialActive terminalActive := by
    simpa [trace, terminalActive, canonicalProfileGroupEliminationGeneratedTrace,
      STVTrace.replaysFrom] using
      canonicalProfileGroupEliminationGeneratedSteps_replayStepsFrom
        voters ballots group rounds initialActive
  have hprefix_replay :
      STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
        (trace.steps.get i).beforeActive :=
    STVTrace.replaysFrom_take_get_beforeActive hreplay i
  have hfull_trace : trace.eliminationRemovesFromGroup group := by
    simpa [trace, canonicalProfileGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedTrace_eliminationRemovesFromGroup
        (choice := MinimalTallyChoiceRule.canonical Candidate)
        (MinimalTallyChoiceRule.canonical_selectsMinimal
          (Candidate := Candidate))
        group (profileActiveTallyOf voters ballots) rounds initialActive
  have hprefix_trace :
      ({ steps := trace.steps.take i.1 } : STVTrace Candidate).eliminationRemovesFromGroup
        group := by
    intro step hstep hkind
    exact hfull_trace step (List.mem_of_mem_take hstep) hkind
  have hall_eliminate :
      ∀ step, step ∈ trace.steps.take i.1 →
        step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        (MinimalTallyChoiceRule.canonical Candidate) group
        (profileActiveTallyOf voters ballots) rounds initialActive step
        (by
          simpa [trace, canonicalProfileGroupEliminationGeneratedTrace,
            canonicalProfileGroupEliminationGeneratedSteps] using
            List.mem_of_mem_take hstep)
  have hsubset :=
    STVTrace.start_sdiff_terminal_subset_group_of_replayStepsFrom_eliminationRemovesFromGroup
      hprefix_replay hall_eliminate hprefix_trace
  simpa [trace] using hsubset

/--
Under strict-support group-removal safety, generated group-minimal elimination
steps are minimum-tally elimination steps on the full active set.
-/
theorem strictSupportGroupRemovalSafety_generated_minimal_eliminations
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ} {rounds : ℕ}
    {initialActive : Finset Candidate}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    (hminimalChoice : choice.SelectsMinimal)
    (hactive_subset_candidates :
      ∀ step,
        step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
            rounds initialActive →
          step.kind = StepKind.eliminate →
            step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step,
        step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
            rounds initialActive →
          step.kind = StepKind.eliminate →
            ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
              step.tally inside =
                budget +
                  Ballot.strictSupportCount voters ballots group
                    (candidates \ group) inside)
    (htally_outside :
      ∀ step,
        step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
            rounds initialActive →
          step.kind = StepKind.eliminate →
            ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
              ∀ outside, outside ∈ candidates \ group →
                step.tally outside =
                  Ballot.strictSupportCount voters ballots
                    (insert outside (group.erase inside))
                    (∅ : Finset Candidate) outside) :
    ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
          rounds initialActive →
        step.kind = StepKind.eliminate →
          step.eliminatesMinimalTally := by
  intro step hstep hkind
  rcases minimalGroupEliminationGeneratedSteps_focus_group_minimal
      hminimalChoice group tallyOf rounds initialActive step hstep with
    ⟨focused, hfocus, hfocused_active_group, hfocused_min_group⟩
  rcases Finset.mem_inter.mp hfocused_active_group with
    ⟨hfocused_active, hfocused_group⟩
  refine ⟨hkind, focused, hfocus, hfocused_active, ?_⟩
  intro candidate hcandidate_active
  by_cases hcandidate_group : candidate ∈ group
  · exact hfocused_min_group candidate
      (Finset.mem_inter.mpr ⟨hcandidate_active, hcandidate_group⟩)
  · have hcandidate_candidates : candidate ∈ candidates :=
      hactive_subset_candidates step hstep hkind hcandidate_active
    have hcandidate_outside : candidate ∈ candidates \ group :=
      Finset.mem_sdiff.mpr ⟨hcandidate_candidates, hcandidate_group⟩
    have hlt :
        step.tally focused < step.tally candidate := by
      have hinside_eq :=
        htally_inside step hstep hkind focused hfocused_group
          hfocused_active
      have houtside_eq :=
        htally_outside step hstep hkind focused hfocused_group
          hfocused_active candidate hcandidate_outside
      simpa [hinside_eq, houtside_eq] using
        hsafety.2.1 focused hfocused_group candidate hcandidate_outside
    exact le_of_lt hlt

/--
Bounded-tally generated group-elimination bridge: under strict-support
group-removal safety, generated group-minimal elimination steps are
minimum-tally elimination steps on the full active set when the generated
tallies are only bounded by the strict-support expressions used in the source
proof.
-/
theorem strictSupportGroupRemovalSafety_generated_minimal_eliminations_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ} {rounds : ℕ}
    {initialActive : Finset Candidate}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    (hminimalChoice : choice.SelectsMinimal)
    (hactive_subset_candidates :
      ∀ step,
        step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
            rounds initialActive →
          step.kind = StepKind.eliminate →
            step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step,
        step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
            rounds initialActive →
          step.kind = StepKind.eliminate →
            ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
              step.tally inside ≤
                budget +
                  Ballot.strictSupportCount voters ballots group
                    (candidates \ group) inside)
    (htally_outside_ge :
      ∀ step,
        step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
            rounds initialActive →
          step.kind = StepKind.eliminate →
            ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
              ∀ outside, outside ∈ candidates \ group →
                Ballot.strictSupportCount voters ballots
                    (insert outside (group.erase inside))
                    (∅ : Finset Candidate) outside ≤
                  step.tally outside) :
    ∀ step,
      step ∈ minimalGroupEliminationGeneratedSteps choice group tallyOf
          rounds initialActive →
        step.kind = StepKind.eliminate →
          step.eliminatesMinimalTally := by
  intro step hstep hkind
  rcases minimalGroupEliminationGeneratedSteps_focus_group_minimal
      hminimalChoice group tallyOf rounds initialActive step hstep with
    ⟨focused, hfocus, hfocused_active_group, hfocused_min_group⟩
  rcases Finset.mem_inter.mp hfocused_active_group with
    ⟨hfocused_active, hfocused_group⟩
  refine ⟨hkind, focused, hfocus, hfocused_active, ?_⟩
  intro candidate hcandidate_active
  by_cases hcandidate_group : candidate ∈ group
  · exact hfocused_min_group candidate
      (Finset.mem_inter.mpr ⟨hcandidate_active, hcandidate_group⟩)
  · have hcandidate_candidates : candidate ∈ candidates :=
      hactive_subset_candidates step hstep hkind hcandidate_active
    have hcandidate_outside : candidate ∈ candidates \ group :=
      Finset.mem_sdiff.mpr ⟨hcandidate_candidates, hcandidate_group⟩
    have hlt :
        step.tally focused < step.tally candidate := by
      exact
        lt_of_le_of_lt
          (htally_inside_le step hstep hkind focused hfocused_group
            hfocused_active)
          (lt_of_lt_of_le
            (hsafety.2.1 focused hfocused_group candidate
              hcandidate_outside)
            (htally_outside_ge step hstep hkind focused hfocused_group
              hfocused_active candidate hcandidate_outside))
    exact le_of_lt hlt

/--
Strict-support group-removal trace bridge: along any trace whose elimination
steps choose and remove minimum-tally active candidates, the safety inequalities
force every certified elimination step to remove a focused group candidate.
-/
theorem strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    trace.eliminationRemovesFromGroup group := by
  intro step hstep hkind
  rcases hgroup_active step hstep hkind with
    ⟨inside, hinside, hinside_active⟩
  rcases strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group
      hsafety hinside (hminimal step hstep hkind) hinside_active
      (hactive_subset_candidates step hstep hkind)
      (htally_inside step hstep hkind inside hinside hinside_active)
      (fun outside houtside =>
        htally_outside step hstep hkind inside hinside hinside_active
          outside houtside) with
    ⟨loser, hfocus, hloser_group, hloser_active⟩
  rcases hremove step hstep hkind with
    ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq_loser : removed = loser :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  exact ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩

/--
Bounded-tally strict-support group-removal trace bridge. Along any trace whose
elimination steps choose and remove minimum-tally active candidates, it is
enough to bound group-candidate tallies above by the budget-augmented
strict-support expression and outside-candidate tallies below by the
corresponding strict-support expression.
-/
theorem strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside) :
    trace.eliminationRemovesFromGroup group := by
  intro step hstep hkind
  rcases hgroup_active step hstep hkind with
    ⟨inside, hinside, hinside_active⟩
  rcases strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group_of_tally_bounds
      hsafety hinside (hminimal step hstep hkind) hinside_active
      (hactive_subset_candidates step hstep hkind)
      (htally_inside_le step hstep hkind inside hinside hinside_active)
      (fun outside houtside =>
        htally_outside_ge step hstep hkind inside hinside hinside_active
          outside houtside) with
    ⟨loser, hfocus, hloser_group, hloser_active⟩
  rcases hremove step hstep hkind with
    ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq_loser : removed = loser :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  exact ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩

/--
Strict-support group-removal trace bridge: along any trace whose elimination
steps choose and remove minimum-tally active candidates, the safety inequalities
force every certified elimination step to remove a focused group candidate.
-/
theorem strictSupportGroupRemovalSafety_trace_elimination_focus_mem_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
        loser ∈ step.beforeActive ∧
        step.afterActive = step.beforeActive.erase loser := by
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    hsafety hminimal hremove hgroup_active hactive_subset_candidates
    htally_inside htally_outside

/--
Strict-support group-removal trace bridge, cardinality form: every certified
minimum-tally elimination step strictly decreases the number of active
candidates in the removable group.
-/
theorem strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_decreases
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ group).card <
        (step.beforeActive ∩ group).card := by
  exact STVTrace.eliminationActiveGroupCardDecreases_of_eliminationRemovesFromGroup
    (strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
      hsafety (trace := trace) hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside htally_outside
    )

/--
Strict-support group-removal trace bridge, exact cardinality form: every
certified minimum-tally elimination step removes exactly one active candidate
from the removable group.
-/
theorem strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_add_one_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ group).card + 1 =
        (step.beforeActive ∩ group).card := by
  exact STVTrace.eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    (strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
      hsafety (trace := trace) hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside htally_outside
    )

/--
Source-shaped strict-support trace certificate.

This is the paper-neutral package behind the Algorithm 6 / Algorithm 2 replay
arguments: a compact strict-support group-removal condition plus a concrete
candidate-level trace whose elimination steps choose minimum-tally focused
candidates and whose tallies agree with the strict-support quantities.
-/
structure StrictSupportGroupRemovalTraceCertificate
    (Voter Candidate : Type*) [DecidableEq Candidate] where
  voters : Finset Voter
  ballots : Voter → Ballot Candidate
  candidates : Finset Candidate
  group : Finset Candidate
  budget : ℕ
  quota : ℕ
  trace : STVTrace Candidate
  condition :
    strictSupportGroupRemovalCondition
      voters ballots candidates group budget quota
  minimal_eliminations :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.removesFocusedCandidate
  group_active_at_elimination :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.beforeActive ⊆ candidates
  tally_inside :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        step.tally inside =
          budget +
            Ballot.strictSupportCount voters ballots group
              (candidates \ group) inside
  tally_outside :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
      ∀ outside, outside ∈ candidates \ group →
        step.tally outside =
          Ballot.strictSupportCount voters ballots
            (insert outside (group.erase inside)) (∅ : Finset Candidate)
            outside

namespace StrictSupportGroupRemovalTraceCertificate

/-- The compact condition supplies the separated safety inequalities. -/
theorem safety {Voter Candidate : Type*} [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    strictSupportGroupRemovalSafety
      cert.voters cert.ballots cert.candidates cert.group
      cert.budget cert.quota := by
  exact strictSupportGroupRemovalSafety_of_condition cert.condition

/-- The certified trace removes focused candidates from the removable group. -/
theorem eliminationRemovesFromGroup {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    cert.trace.eliminationRemovesFromGroup cert.group := by
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    (safety cert)
    cert.minimal_eliminations
    cert.focused_eliminations_remove_focus
    cert.group_active_at_elimination
    cert.active_subset_candidates
    cert.tally_inside
    cert.tally_outside

/-- Every certified elimination step strictly decreases active group size. -/
theorem eliminationActiveGroupCardDecreases {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    cert.trace.eliminationActiveGroupCardDecreases cert.group := by
  exact STVTrace.eliminationActiveGroupCardDecreases_of_eliminationRemovesFromGroup
    (eliminationRemovesFromGroup cert)

/-- Every certified elimination step removes exactly one active group member. -/
theorem eliminationActiveGroupCardAddOneEq {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    cert.trace.eliminationActiveGroupCardAddOneEq cert.group := by
  exact STVTrace.eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    (eliminationRemovesFromGroup cert)

/--
Replay accounting for a certified all-elimination prefix: terminal active group
count plus prefix length equals initial active group count.
-/
theorem terminal_activeGroup_card_add_length_eq {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate)
    {startActive terminalActive : Finset Candidate}
    (hreplay : cert.trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ cert.trace.steps → step.kind = StepKind.eliminate) :
    (terminalActive ∩ cert.group).card + cert.trace.steps.length =
      (startActive ∩ cert.group).card := by
  exact STVTrace.terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
    hreplay hall_eliminate (eliminationRemovesFromGroup cert)

/--
If the certified all-elimination replay prefix is long enough to remove every
initial active group member, no group member remains terminally active.
-/
theorem terminal_activeGroup_empty {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate)
    {startActive terminalActive : Finset Candidate}
    (hreplay : cert.trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ cert.trace.steps → step.kind = StepKind.eliminate)
    (hlength :
      cert.trace.steps.length = (startActive ∩ cert.group).card) :
    terminalActive ∩ cert.group = ∅ := by
  exact STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
    hreplay hall_eliminate (eliminationRemovesFromGroup cert) hlength

end StrictSupportGroupRemovalTraceCertificate

/--
Round-rank active-set invariant: candidates whose exit rank is strictly after
the current round rank are active in that round.

This is intentionally independent of a particular quota or transfer convention;
downstream replay proofs can instantiate `roundRank` from their deterministic
trace.
-/
def ActiveUntilExitRank {Candidate Round : Type*}
    (active : Round → Finset Candidate)
    (roundRank : Round → ℕ)
    (exitRank : Candidate → ℕ) : Prop :=
  ∀ {candidate round}, roundRank round < exitRank candidate →
    candidate ∈ active round

/--
Domain-scoped round-rank active-set invariant: tracked candidates whose exit
rank is strictly after the current round rank are active in that round.

This is the source-shaped form used when a paper only needs the invariant for a
coalition or protected group, rather than for every candidate in the ambient
type.
-/
def ActiveUntilExitRankOn {Candidate Round : Type*}
    (tracked : Finset Candidate)
    (active : Round → Finset Candidate)
    (roundRank : Round → ℕ)
    (exitRank : Candidate → ℕ) : Prop :=
  ∀ {candidate round}, candidate ∈ tracked →
    roundRank round < exitRank candidate →
      candidate ∈ active round

namespace ActiveUntilExitRank

/--
If a round is before one candidate's exit rank, then any candidate with weakly
later exit rank is active in that round.
-/
theorem active_of_rank_lt_of_le {Candidate Round : Type*}
    {active : Round → Finset Candidate}
    {roundRank : Round → ℕ} {exitRank : Candidate → ℕ}
    (hactive : ActiveUntilExitRank active roundRank exitRank)
    {candidate other : Candidate} {round : Round}
    (hround_lt : roundRank round < exitRank candidate)
    (hle : exitRank candidate ≤ exitRank other) :
    other ∈ active round :=
  hactive (lt_of_lt_of_le hround_lt hle)

end ActiveUntilExitRank

namespace ActiveUntilExitRankOn

/-- A global active-until-exit invariant restricts to any tracked set. -/
theorem of_global {Candidate Round : Type*}
    {tracked : Finset Candidate}
    {active : Round → Finset Candidate}
    {roundRank : Round → ℕ} {exitRank : Candidate → ℕ}
    (hactive : ActiveUntilExitRank active roundRank exitRank) :
    ActiveUntilExitRankOn tracked active roundRank exitRank := by
  intro candidate round _htracked hround_lt
  exact hactive hround_lt

/--
If a round is before one tracked candidate's exit rank, then any tracked
candidate with weakly later exit rank is active in that round.
-/
theorem active_of_rank_lt_of_le {Candidate Round : Type*}
    {tracked : Finset Candidate}
    {active : Round → Finset Candidate}
    {roundRank : Round → ℕ} {exitRank : Candidate → ℕ}
    (hactive : ActiveUntilExitRankOn tracked active roundRank exitRank)
    {candidate other : Candidate} {round : Round}
    (hother : other ∈ tracked)
    (hround_lt : roundRank round < exitRank candidate)
    (hle : exitRank candidate ≤ exitRank other) :
    other ∈ active round :=
  hactive hother (lt_of_lt_of_le hround_lt hle)

end ActiveUntilExitRankOn

namespace STVTrace

/--
Build a coalition/group-scoped active-until-exit invariant from concrete trace
replay facts: tracked candidates start active and are not focused before their
exit rank.
-/
theorem activeUntilExitRankOn_beforeActive_of_replaysFrom_not_focused_before
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive tracked : Finset Candidate}
    {exitRank : Candidate → ℕ}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove :
      ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (hstart : tracked ⊆ startActive)
    (hnot_focus_before_exit :
      ∀ {candidate : Candidate}, candidate ∈ tracked →
        ∀ i : Fin trace.steps.length, i.1 < exitRank candidate →
          ∀ step, step ∈ trace.steps.take i.1 →
            step.focus ≠ some candidate) :
    ActiveUntilExitRankOn tracked
      (fun i : Fin trace.steps.length => (trace.steps.get i).beforeActive)
      (fun i : Fin trace.steps.length => i.1) exitRank := by
  intro candidate i htracked hround_lt
  exact mem_beforeActive_of_replaysFrom_not_focused_before
    (trace := trace)
    (startActive := startActive)
    (terminalActive := terminalActive)
    (candidate := candidate)
    hreplay hremove (hstart htracked) i
    (hnot_focus_before_exit htracked i hround_lt)

end STVTrace

end Voting
end SocialChoice
end AppliedModelingLib
