import AppliedModelingLib.SocialChoice.Voting.STV.Quota
import AppliedModelingLib.SocialChoice.Voting.STV.Structures
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators

/-!
# Solid-Coalition STV Process Primitives

Paper-neutral process invariants for STV proofs under solid coalitions.

The central abstraction is a separate same-party quota process. It tracks how
many same-party candidates have reached quota and how much same-party vote mass
remains. When the remaining same-party vote mass is below one quota, the process
provides the quota-witness used by two-party STV seat-share arguments.

The fractional replay layer below is deliberately phrased over the shared
`STVStep`/`STVTrace` dynamics vocabulary, with a real-valued tally oracle supplied
by the concrete transfer rule being replayed.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/-- State of a same-party quota process. -/
structure PartyQuotaState where
  remainingCandidates : ℕ
  quotaWinners : ℕ
  voteMass : ℝ

/-- Initial state for a same-party quota process. -/
def PartyQuotaStartState (remainingCandidates : ℕ) (initialVotes : ℝ) :
    PartyQuotaState where
  remainingCandidates := remainingCandidates
  quotaWinners := 0
  voteMass := initialVotes

/--
Invariant for a same-party quota process: the initial vote mass decomposes into
`quotaWinners` full quotas plus current residual same-party vote mass.
-/
def PartyQuotaInvariant (initialVotes quota : ℝ) (state : PartyQuotaState) : Prop :=
  initialVotes = (state.quotaWinners : ℝ) * quota + state.voteMass ∧
    0 ≤ state.voteMass

/-- The start state satisfies the quota decomposition invariant. -/
theorem PartyQuotaInvariant.start {initialVotes quota : ℝ} {remainingCandidates : ℕ}
    (hvotes_nonneg : 0 ≤ initialVotes) :
    PartyQuotaInvariant initialVotes quota
      (PartyQuotaStartState remainingCandidates initialVotes) := by
  constructor
  · simp [PartyQuotaStartState]
  · simpa [PartyQuotaStartState] using hvotes_nonneg

/-- An elect step consumes one quota and records one additional quota winner. -/
def PartyQuotaElectStep (quota : ℝ) (before after : PartyQuotaState) : Prop :=
  quota ≤ before.voteMass ∧
    after.remainingCandidates + 1 = before.remainingCandidates ∧
    after.quotaWinners = before.quotaWinners + 1 ∧
    after.voteMass = before.voteMass - quota

/-- An elimination step removes a candidate without consuming same-party vote mass. -/
def PartyQuotaEliminateStep (_quota : ℝ) (before after : PartyQuotaState) : Prop :=
  after.remainingCandidates + 1 = before.remainingCandidates ∧
    after.quotaWinners = before.quotaWinners ∧
    after.voteMass = before.voteMass

/-- A process is terminal for the lower-bound proof once residual vote mass is below quota. -/
def PartyQuotaTerminalBelowQuota (quota : ℝ) (state : PartyQuotaState) : Prop :=
  state.voteMass < quota

/--
Capacity invariant for the party projection: the current residual vote mass is
strictly less than one more quota than the number of remaining same-party
candidates. Quota-respecting STV preserves this invariant through elections
and no-quota eliminations; when no same-party candidates remain, it is exactly
the terminal below-quota condition.
-/
def PartyQuotaCapacityBound (quota : ℝ) (state : PartyQuotaState) : Prop :=
  state.voteMass < ((state.remainingCandidates + 1 : ℕ) : ℝ) * quota

namespace PartyQuotaCapacityBound

/-- With no remaining candidates, the capacity bound is the terminal residual bound. -/
theorem terminalBelowQuota_of_remaining_zero {quota : ℝ}
    {state : PartyQuotaState}
    (hbound : PartyQuotaCapacityBound quota state)
    (hremaining : state.remainingCandidates = 0) :
    PartyQuotaTerminalBelowQuota quota state := by
  change state.voteMass < quota
  simpa [PartyQuotaCapacityBound, hremaining] using hbound

/-- Electing a quota winner preserves the capacity bound. -/
theorem of_electStep {quota : ℝ} {before after : PartyQuotaState}
    (hbound : PartyQuotaCapacityBound quota before)
    (hstep : PartyQuotaElectStep quota before after) :
    PartyQuotaCapacityBound quota after := by
  rcases hstep with ⟨_hquota, hremaining, _hwinners, hmass⟩
  have hremaining_cast :
      (before.remainingCandidates : ℝ) =
        (after.remainingCandidates : ℝ) + 1 := by
    exact_mod_cast hremaining.symm
  change after.voteMass <
    ((after.remainingCandidates + 1 : ℕ) : ℝ) * quota
  rw [hmass]
  rw [PartyQuotaCapacityBound] at hbound
  norm_num [Nat.cast_add] at hbound ⊢
  rw [hremaining_cast] at hbound
  nlinarith

/--
Subtracting one quota while removing one remaining candidate preserves the
capacity bound.  Unlike `of_electStep`, this lower-bound form does not require
the current party residual itself to be at quota.
-/
theorem of_electUpdate {quota : ℝ} {before after : PartyQuotaState}
    (hbound : PartyQuotaCapacityBound quota before)
    (hremaining : after.remainingCandidates + 1 = before.remainingCandidates)
    (hmass : after.voteMass = before.voteMass - quota) :
    PartyQuotaCapacityBound quota after := by
  have hremaining_cast :
      (before.remainingCandidates : ℝ) =
        (after.remainingCandidates : ℝ) + 1 := by
    exact_mod_cast hremaining.symm
  change after.voteMass <
    ((after.remainingCandidates + 1 : ℕ) : ℝ) * quota
  rw [hmass]
  rw [PartyQuotaCapacityBound] at hbound
  norm_num [Nat.cast_add] at hbound ⊢
  rw [hremaining_cast] at hbound
  nlinarith

/--
Eliminating a same-party candidate preserves the capacity bound when the
current residual mass is already below `remainingCandidates * quota`; this is
the party-level consequence of "no active same-party candidate has reached
quota."
-/
theorem of_eliminateStep_of_voteMass_lt_remaining_mul_quota
    {quota : ℝ} {before after : PartyQuotaState}
    (hmass_lt :
      before.voteMass < (before.remainingCandidates : ℝ) * quota)
    (hstep : PartyQuotaEliminateStep quota before after) :
    PartyQuotaCapacityBound quota after := by
  rcases hstep with ⟨hremaining, _hwinners, hmass⟩
  have hremaining_cast :
      (before.remainingCandidates : ℝ) =
        (after.remainingCandidates : ℝ) + 1 := by
    exact_mod_cast hremaining.symm
  change after.voteMass <
    ((after.remainingCandidates + 1 : ℕ) : ℝ) * quota
  rw [hmass]
  rw [hremaining_cast] at hmass_lt
  norm_num [Nat.cast_add] at hmass_lt ⊢
  exact hmass_lt

end PartyQuotaCapacityBound

/--
The standard party start state satisfies the capacity bound whenever the party
vote share is at most one and the party has at least as many candidates as
there are seats. This is the Droop-quota arithmetic needed before replaying a
solid-coalition STV prefix.
-/
theorem partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
    {seats voters remainingCandidates : ℕ} {partyShare : ℝ}
    (hshare_le : partyShare ≤ 1)
    (hseats_le_candidates : seats ≤ remainingCandidates) :
    PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
      (PartyQuotaStartState remainingCandidates
        (partyShare * (voters : ℝ))) := by
  change partyShare * (voters : ℝ) <
    ((remainingCandidates + 1 : ℕ) : ℝ) * (STVQuota seats voters : ℝ)
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hvoters_lt :
      (voters : ℝ) <
        ((seats + 1 : ℕ) : ℝ) * (STVQuota seats voters : ℝ) := by
    have h := voters_div_STVQuota_lt_seats_succ seats voters
    rw [div_lt_iff₀ hquota_pos] at h
    simpa [Nat.cast_add, Nat.cast_one, add_comm, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hshare_votes_le :
      partyShare * (voters : ℝ) ≤ (voters : ℝ) := by
    have hvoters_nonneg : 0 ≤ (voters : ℝ) := by positivity
    nlinarith
  have hseat_succ_le :
      ((seats + 1 : ℕ) : ℝ) ≤
        ((remainingCandidates + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hseats_le_candidates
  have hquota_nonneg : 0 ≤ (STVQuota seats voters : ℝ) := hquota_pos.le
  have hcap_le :
      ((seats + 1 : ℕ) : ℝ) * (STVQuota seats voters : ℝ) ≤
        ((remainingCandidates + 1 : ℕ) : ℝ) *
          (STVQuota seats voters : ℝ) :=
    mul_le_mul_of_nonneg_right hseat_succ_le hquota_nonneg
  exact lt_of_le_of_lt hshare_votes_le (lt_of_lt_of_le hvoters_lt hcap_le)

/-- A same-party quota process step either elects a quota winner or eliminates a candidate. -/
def PartyQuotaStep (quota : ℝ) (before after : PartyQuotaState) : Prop :=
  PartyQuotaElectStep quota before after ∨ PartyQuotaEliminateStep quota before after

/--
A complete same-party quota process certificate: a start state with the quota
decomposition invariant, a reachable terminal state, and terminal residual vote
mass below quota.
-/
structure PartyQuotaProcess (initialVotes quota : ℝ) where
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : Relation.ReflTransGen (PartyQuotaStep quota) startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/--
Operational solid-coalition ballot condition.

For each voter in the coalition, whenever at least one same-party candidate is
active, the voter's first active candidate is still a same-party candidate.
This is the trace-level form of the usual STV assumption that same-party
candidates are ranked above all other-party candidates.
-/
def SolidCoalitionBallots {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates : Finset Candidate) : Prop :=
  ∀ voter, voter ∈ voters → ∀ active,
    (∃ same, same ∈ partyCandidates ∧ same ∈ active) →
      ∃ same, same ∈ partyCandidates ∧
        Ballot.nextActive (ballots voter) active = some same

/--
Trace-level no-cross-party-transfer condition before party exhaustion.

At every trace step, if a coalition still has an active same-party candidate,
then its voters give no active support to any outside-party candidate.
-/
def NoCrossPartyTransferBeforeExhaustion {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates : Finset Candidate) (trace : STVTrace Candidate) : Prop :=
  ∀ step, step ∈ trace.steps →
    (∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive) →
      ∀ outside, outside ∉ partyCandidates →
        (Ballot.activeSupport voters ballots step.beforeActive outside).card = 0

namespace SolidCoalitionBallots

/--
A solid coalition's first active candidate belongs to the coalition party while
any same-party candidate remains active.
-/
theorem nextActive_mem_party {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates active : Finset Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    {voter : Voter} (hvoter : voter ∈ voters)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active) :
    ∃ same, same ∈ partyCandidates ∧ same ∈ active ∧
      Ballot.nextActive (ballots voter) active = some same := by
  rcases hsolid voter hvoter active hpartyActive with
    ⟨same, hsame_party, hnext⟩
  exact ⟨same, hsame_party, Ballot.nextActive_mem hnext, hnext⟩

end SolidCoalitionBallots

/--
If a solid coalition has not exhausted its same-party candidates, then an
outside-party candidate has empty active support from that coalition.
-/
theorem activeSupport_eq_empty_of_solidCoalitionBallots_outside
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates active : Finset Candidate} {outside : Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active)
    (houtside : outside ∉ partyCandidates) :
    Ballot.activeSupport voters ballots active outside = ∅ := by
  ext voter
  constructor
  · intro hvoterSupport
    simp [Ballot.activeSupport] at hvoterSupport
    rcases hvoterSupport with ⟨hvoter, hnextOutside⟩
    rcases hsolid voter hvoter active hpartyActive with
      ⟨same, hsame_party, hnextSame⟩
    have hsame_eq_outside : same = outside :=
      Option.some.inj (hnextSame.symm.trans hnextOutside)
    exact False.elim (houtside (by simpa [hsame_eq_outside] using hsame_party))
  · intro hfalse
    exact False.elim (by simpa using hfalse)

/--
Cardinality form: before a solid coalition exhausts its same-party candidates,
outside-party active support from that coalition is zero.
-/
theorem activeSupport_card_eq_zero_of_solidCoalitionBallots_outside
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates active : Finset Candidate} {outside : Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active)
    (houtside : outside ∉ partyCandidates) :
    (Ballot.activeSupport voters ballots active outside).card = 0 := by
  rw [activeSupport_eq_empty_of_solidCoalitionBallots_outside
    hsolid hpartyActive houtside]
  rfl

/--
Solid-coalition ballots justify party-level STV trace analysis: along any trace,
outside-party support from the coalition can appear only after the coalition has
no active same-party candidate.
-/
theorem noCrossPartyTransferBeforeExhaustion_of_solidCoalitionBallots
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {trace : STVTrace Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates) :
    NoCrossPartyTransferBeforeExhaustion
      voters ballots partyCandidates trace := by
  intro step _hstep hpartyActive outside houtside
  exact activeSupport_card_eq_zero_of_solidCoalitionBallots_outside
    hsolid hpartyActive houtside

/--
Fractional election step with its focused real-valued tally explicit.

This is the local shape expected from a concrete fractional transfer rule before
projecting the step to the coarser party-quota process.
-/
def FractionalPartySTVElectStepWithTally (quota focusedTally : ℝ)
    (before after : PartyQuotaState) : Prop :=
  ∃ surplusWeight,
    0 ≤ focusedTally ∧
      quota ≤ focusedTally ∧
      focusedTally ≤ before.voteMass ∧
      surplusWeight = focusedTally - quota ∧
      0 ≤ surplusWeight ∧
      after.remainingCandidates + 1 = before.remainingCandidates ∧
      after.quotaWinners = before.quotaWinners + 1 ∧
      after.voteMass = before.voteMass - quota

/--
Fractional elimination step with its focused real-valued tally explicit.

The tally is exposed so a downstream replay theorem can bind it to the concrete
transfer/tally calculation for the shared `STVStep`.
-/
def FractionalPartySTVEliminateStepWithTally (_quota focusedTally : ℝ)
    (before after : PartyQuotaState) : Prop :=
  0 ≤ focusedTally ∧
    focusedTally ≤ before.voteMass ∧
    after.remainingCandidates + 1 = before.remainingCandidates ∧
    after.quotaWinners = before.quotaWinners ∧
    after.voteMass = before.voteMass

/--
Concrete party-projected fractional STV election step.

The focused candidate has fractional tally at least quota; exactly one quota is
retained for the winner, and the surplus is the remaining focused tally that is
available for same-party transfer. At the party-process level this consumes one
quota of party vote mass and records one additional quota winner.
-/
def FractionalPartySTVElectStep (quota : ℝ)
    (before after : PartyQuotaState) : Prop :=
  ∃ focusedTally,
    FractionalPartySTVElectStepWithTally quota focusedTally before after

/--
Concrete party-projected fractional STV elimination step.

Eliminating a same-party candidate removes one remaining party candidate but
does not consume party vote mass; the candidate's fractional tally is available
for transfer within the party projection.
-/
def FractionalPartySTVEliminateStep (_quota : ℝ)
    (before after : PartyQuotaState) : Prop :=
  ∃ focusedTally,
    FractionalPartySTVEliminateStepWithTally _quota focusedTally before after

/-- An explicit-tally fractional election step forgets to the existential form. -/
theorem fractionalPartySTVElectStep_of_withTally {quota focusedTally : ℝ}
    {before after : PartyQuotaState}
    (hstep :
      FractionalPartySTVElectStepWithTally quota focusedTally before after) :
    FractionalPartySTVElectStep quota before after :=
  ⟨focusedTally, hstep⟩

/-- An explicit-tally fractional elimination step forgets to the existential form. -/
theorem fractionalPartySTVEliminateStep_of_withTally {quota focusedTally : ℝ}
    {before after : PartyQuotaState}
    (hstep :
      FractionalPartySTVEliminateStepWithTally quota focusedTally before after) :
    FractionalPartySTVEliminateStep quota before after :=
  ⟨focusedTally, hstep⟩

/--
A concrete party-projected fractional STV step is either a quota election with
surplus transfer or an elimination with conserved same-party vote mass.
-/
def FractionalPartySTVStep (quota : ℝ)
    (before after : PartyQuotaState) : Prop :=
  FractionalPartySTVElectStep quota before after ∨
    FractionalPartySTVEliminateStep quota before after

/--
A shared-trace fractional STV step, projected to one party.

The `STVStep` supplies the common election dynamics and focused candidate; the
real-valued `fractionalTally` is supplied by the concrete transfer rule being
replayed. The step is useful for downstream STV instantiations that need to show
their concrete trace induces the party-quota process.
-/
def FractionalPartySTVTraceStep {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (quota : ℝ) (step : STVStep Candidate)
    (before after : PartyQuotaState) : Prop :=
  step.removesFocusedCandidate ∧
    ((step.kind = StepKind.elect ∧
        ∃ focused, step.focus = some focused ∧ focused ∈ partyCandidates ∧
          FractionalPartySTVElectStepWithTally
            quota (fractionalTally focused) before after) ∨
      (step.kind = StepKind.eliminate ∧
        ∃ focused, step.focus = some focused ∧ focused ∈ partyCandidates ∧
          FractionalPartySTVEliminateStepWithTally
            quota (fractionalTally focused) before after))

/-- A shared-trace fractional STV step forgets to the party-projected step. -/
theorem fractionalPartySTVStep_of_traceStep {Candidate : Type*}
    [DecidableEq Candidate] {partyCandidates : Finset Candidate}
    {fractionalTally : Candidate → ℝ} {quota : ℝ}
    {step : STVStep Candidate} {before after : PartyQuotaState}
    (hstep :
      FractionalPartySTVTraceStep partyCandidates fractionalTally quota step
        before after) :
    FractionalPartySTVStep quota before after := by
  rcases hstep with ⟨_hremove, helect | heliminate⟩
  · rcases helect with
      ⟨_hkind, focused, _hfocus, _hfocused_party, hstep⟩
    exact Or.inl (fractionalPartySTVElectStep_of_withTally hstep)
  · rcases heliminate with
      ⟨_hkind, focused, _hfocus, _hfocused_party, hstep⟩
    exact Or.inr (fractionalPartySTVEliminateStep_of_withTally hstep)

/--
Replay path for a shared `STVTrace`, projected to one party's fractional quota
state.
-/
inductive FractionalPartySTVTraceReplayPath {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ) :
    List (STVStep Candidate) → PartyQuotaState → PartyQuotaState → Prop
  | nil (state : PartyQuotaState) :
      FractionalPartySTVTraceReplayPath
        partyCandidates quota fractionalTally [] state state
  | cons {step : STVStep Candidate} {steps : List (STVStep Candidate)}
      {before middle after : PartyQuotaState}
      (hstep :
        FractionalPartySTVTraceStep partyCandidates (fractionalTally step)
          quota step before middle)
      (hrest :
        FractionalPartySTVTraceReplayPath
          partyCandidates quota fractionalTally steps middle after) :
      FractionalPartySTVTraceReplayPath
        partyCandidates quota fractionalTally (step :: steps) before after

/--
A shared-trace fractional replay path projects to the abstract fractional party
step path.
-/
theorem fractionalPartySTVPath_of_traceReplayPath {Candidate : Type*}
    [DecidableEq Candidate] {partyCandidates : Finset Candidate}
    {quota : ℝ} {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {before after : PartyQuotaState}
    (hpath :
      FractionalPartySTVTraceReplayPath partyCandidates quota fractionalTally
        steps before after) :
    Relation.ReflTransGen (FractionalPartySTVStep quota) before after := by
  induction hpath with
  | nil state =>
      exact Relation.ReflTransGen.refl
  | cons hstep _hrest ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single
          (fractionalPartySTVStep_of_traceStep hstep))
        ih

/--
A replay certificate for one party in a fractional STV election.

The path records concrete party-projected fractional steps, while the terminal
condition states that the replay has reached the below-quota stopping point used
by the party-level quota-process proof.
-/
structure FractionalPartySTVReplay (initialVotes quota : ℝ) where
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : Relation.ReflTransGen (FractionalPartySTVStep quota)
    startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/--
A trace replay certificate for one party in a fractional STV election.

The certificate is parameterized by the concrete shared trace and a real-valued
fractional tally interpretation for each trace step.
-/
structure FractionalPartySTVTraceReplay {Candidate : Type*}
    [DecidableEq Candidate] (initialVotes quota : ℝ) where
  partyCandidates : Finset Candidate
  trace : STVTrace Candidate
  fractionalTally : STVStep Candidate → Candidate → ℝ
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : FractionalPartySTVTraceReplayPath partyCandidates quota
    fractionalTally trace.steps startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/--
Abstract fractional transfer rule for the shared STV trace layer.

The rule supplies the real-valued tally interpretation used when replaying a
trace. A concrete downstream rule should instantiate this object and prove
that its trace induces the party replay laws below.
-/
structure FractionalSTVTransferRule (Candidate : Type*) where
  fractionalTally : STVStep Candidate → Candidate → ℝ

/--
Rule-parametric replay certificate for one party in a fractional STV election.

This is the transfer-rule-facing version of `FractionalPartySTVTraceReplay`:
the tally oracle is supplied by the rule, and the proof obligation is that the
rule's trace steps project to the party quota-state transitions.
-/
structure FractionalPartySTVRuleReplay {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (initialVotes quota : ℝ) where
  partyCandidates : Finset Candidate
  trace : STVTrace Candidate
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : FractionalPartySTVTraceReplayPath partyCandidates quota
    rule.fractionalTally trace.steps startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/--
A shared-trace fractional replay forgets to the party-projected replay
certificate.
-/
def fractionalPartySTVReplay_of_traceReplay {Candidate : Type*}
    [DecidableEq Candidate] {initialVotes quota : ℝ}
    (replay :
      FractionalPartySTVTraceReplay
        (Candidate := Candidate) initialVotes quota) :
    FractionalPartySTVReplay initialVotes quota where
  startState := replay.startState
  terminalState := replay.terminalState
  startInvariant := replay.startInvariant
  path := fractionalPartySTVPath_of_traceReplayPath replay.path
  terminalBelowQuota := replay.terminalBelowQuota

/--
A rule-parametric replay forgets to the existing shared-trace replay
certificate by exposing the rule's fractional tally interpretation.
-/
def fractionalPartySTVTraceReplay_of_ruleReplay {Candidate : Type*}
    [DecidableEq Candidate] {rule : FractionalSTVTransferRule Candidate}
    {initialVotes quota : ℝ}
    (replay :
      FractionalPartySTVRuleReplay
        (Candidate := Candidate) rule initialVotes quota) :
    FractionalPartySTVTraceReplay
      (Candidate := Candidate) initialVotes quota where
  partyCandidates := replay.partyCandidates
  trace := replay.trace
  fractionalTally := rule.fractionalTally
  startState := replay.startState
  terminalState := replay.terminalState
  startInvariant := replay.startInvariant
  path := replay.path
  terminalBelowQuota := replay.terminalBelowQuota

/--
The concrete fractional election step projects to the abstract quota-process
election step.
-/
theorem partyQuotaElectStep_of_fractionalPartySTVElectStep {quota : ℝ}
    {before after : PartyQuotaState}
    (hstep : FractionalPartySTVElectStep quota before after) :
    PartyQuotaElectStep quota before after := by
  rcases hstep with
    ⟨focusedTally, _surplusWeight, _htally_nonneg, hquota_le_tally,
      htally_le_mass, _hsurplus, _hsurplus_nonneg, hremaining, hwinners,
      hmass⟩
  exact ⟨le_trans hquota_le_tally htally_le_mass, hremaining, hwinners,
    hmass⟩

/--
The concrete fractional elimination step projects to the abstract quota-process
elimination step.
-/
theorem partyQuotaEliminateStep_of_fractionalPartySTVEliminateStep {quota : ℝ}
    {before after : PartyQuotaState}
    (hstep : FractionalPartySTVEliminateStep quota before after) :
    PartyQuotaEliminateStep quota before after := by
  rcases hstep with
    ⟨_focusedTally, _htally_nonneg, _htally_le_mass, hremaining, hwinners,
      hmass⟩
  exact ⟨hremaining, hwinners, hmass⟩

/--
Every concrete party-projected fractional STV step is a valid abstract
same-party quota-process step.
-/
theorem partyQuotaStep_of_fractionalPartySTVStep {quota : ℝ}
    {before after : PartyQuotaState}
    (hstep : FractionalPartySTVStep quota before after) :
    PartyQuotaStep quota before after := by
  rcases hstep with hstep | hstep
  · exact Or.inl (partyQuotaElectStep_of_fractionalPartySTVElectStep hstep)
  · exact Or.inr
      (partyQuotaEliminateStep_of_fractionalPartySTVEliminateStep hstep)

/--
Replay paths made of concrete fractional party steps project to abstract
same-party quota-process paths.
-/
theorem partyQuotaPath_of_fractionalPartySTVPath {quota : ℝ}
    {before after : PartyQuotaState}
    (hpath :
      Relation.ReflTransGen (FractionalPartySTVStep quota) before after) :
    Relation.ReflTransGen (PartyQuotaStep quota) before after := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hstep =>
      exact Relation.ReflTransGen.single
        (partyQuotaStep_of_fractionalPartySTVStep hstep)
  | trans _ _ hleft hright => exact Relation.ReflTransGen.trans hleft hright

/--
A concrete party-projected fractional STV replay yields the terminal
same-party quota-process certificate used by solid-coalition STV proofs.
-/
def partyQuotaProcess_of_fractionalPartySTVReplay {initialVotes quota : ℝ}
    (replay : FractionalPartySTVReplay initialVotes quota) :
    PartyQuotaProcess initialVotes quota where
  startState := replay.startState
  terminalState := replay.terminalState
  startInvariant := replay.startInvariant
  path := partyQuotaPath_of_fractionalPartySTVPath replay.path
  terminalBelowQuota := replay.terminalBelowQuota

/--
A concrete shared-trace fractional STV replay yields the terminal same-party
quota-process certificate used by solid-coalition STV proofs.
-/
def partyQuotaProcess_of_fractionalPartySTVTraceReplay {Candidate : Type*}
    [DecidableEq Candidate] {initialVotes quota : ℝ}
    (replay :
      FractionalPartySTVTraceReplay
        (Candidate := Candidate) initialVotes quota) :
    PartyQuotaProcess initialVotes quota :=
  partyQuotaProcess_of_fractionalPartySTVReplay
    (fractionalPartySTVReplay_of_traceReplay replay)

/--
Source-shaped transfer preservation step for a party projection of a shared
fractional STV trace.

This is weaker than requiring every shared trace step to be a same-party
quota-process step. If the focused candidate is in the party, quota elections
retain exactly one quota and preserve/transfer the full surplus inside the
party, while eliminations preserve the party's vote mass. If the focused
candidate is outside the party, the party state is unchanged for this projection.
-/
def FractionalPartySTVTransferPreservationStep {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (quota : ℝ) (step : STVStep Candidate)
    (before after : PartyQuotaState) : Prop :=
  step.removesFocusedCandidate ∧
    ((step.kind = StepKind.elect ∧
        ∃ focused, step.focus = some focused ∧ focused ∈ partyCandidates ∧
          FractionalPartySTVElectStepWithTally
            quota (fractionalTally focused) before after) ∨
      (step.kind = StepKind.eliminate ∧
        ∃ focused, step.focus = some focused ∧ focused ∈ partyCandidates ∧
          FractionalPartySTVEliminateStepWithTally
            quota (fractionalTally focused) before after) ∨
      (∃ focused, step.focus = some focused ∧ focused ∉ partyCandidates ∧
        after = before))

/--
Deterministic party-state update induced by one source STV trace step.

If the focused candidate belongs to the party, an election consumes one quota
and an elimination removes one remaining party candidate while preserving party
vote mass. If the focused candidate is outside the party, the party projection
stutters.
-/
def partyTransferPreservationNextState {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (quota : ℝ) (step : STVStep Candidate)
    (before : PartyQuotaState) : PartyQuotaState :=
  match step.focus with
  | none => before
  | some focused =>
      if focused ∈ partyCandidates then
        match step.kind with
        | StepKind.elect =>
            { remainingCandidates := before.remainingCandidates - 1
              quotaWinners := before.quotaWinners + 1
              voteMass := before.voteMass - quota }
        | StepKind.eliminate =>
            { remainingCandidates := before.remainingCandidates - 1
              quotaWinners := before.quotaWinners
              voteMass := before.voteMass }
        | StepKind.transfer => before
        | StepKind.finish => before
      else before

/--
Active candidates belonging to a party at a concrete STV trace step.

This small helper is shared by source-step semantics: the party state tracks
exactly these active same-party candidates.
-/
def activePartyCandidates {Candidate : Type*} [DecidableEq Candidate]
    (active partyCandidates : Finset Candidate) : Finset Candidate :=
  active.filter fun candidate => candidate ∈ partyCandidates

theorem activePartyCandidates_eq_inter {Candidate : Type*}
    [DecidableEq Candidate] (active partyCandidates : Finset Candidate) :
    activePartyCandidates active partyCandidates = active ∩ partyCandidates := by
  ext candidate
  simp [activePartyCandidates]

theorem activePartyCandidates_eq_self_of_subset {Candidate : Type*}
    [DecidableEq Candidate] {active partyCandidates : Finset Candidate}
    (hsubset : partyCandidates ⊆ active) :
    activePartyCandidates active partyCandidates = partyCandidates := by
  ext candidate
  constructor
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro hmem
    exact Finset.mem_filter.mpr ⟨hsubset hmem, hmem⟩

theorem activePartyCandidates_card_eq_of_subset {Candidate : Type*}
    [DecidableEq Candidate] {active partyCandidates : Finset Candidate}
    (hsubset : partyCandidates ⊆ active) :
    (activePartyCandidates active partyCandidates).card = partyCandidates.card := by
  rw [activePartyCandidates_eq_self_of_subset hsubset]

/--
If a replayed executable trace ends with an active same-party candidate, that
candidate was active before every earlier trace step.
-/
theorem step_activePartyWitness_of_terminal_activePartyCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive partyCandidates : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove : ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (hterminal : ∃ same, same ∈ partyCandidates ∧ same ∈ terminalActive) :
    ∀ i : Fin trace.steps.length,
      ∃ same, same ∈ partyCandidates ∧
        same ∈ (trace.steps.get i).beforeActive := by
  intro i
  rcases hterminal with ⟨same, hsame_party, hsame_terminal⟩
  exact ⟨same, hsame_party,
    STVTrace.terminalActive_subset_beforeActive_of_replaysFrom_removesFocusedCandidate
      hreplay hremove i hsame_terminal⟩

/--
Current same-party fractional vote mass: the sum of fractional tallies of the
active candidates belonging to that party.
-/
def partyFractionalTallyMass {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (active : Finset Candidate) : ℝ :=
  ∑ candidate ∈ activePartyCandidates active partyCandidates,
    fractionalTally candidate

/--
If every active same-party candidate has tally below quota and at least one
same-party candidate is active, then total active same-party tally mass is
below `remaining candidates * quota`.
-/
theorem partyFractionalTallyMass_lt_card_mul_quota_of_forall_lt
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates active : Finset Candidate}
    {fractionalTally : Candidate → ℝ} {quota : ℝ}
    (hnonempty :
      (activePartyCandidates active partyCandidates).Nonempty)
    (hlt :
      ∀ candidate,
        candidate ∈ activePartyCandidates active partyCandidates →
          fractionalTally candidate < quota) :
    partyFractionalTallyMass partyCandidates fractionalTally active <
      ((activePartyCandidates active partyCandidates).card : ℝ) * quota := by
  calc
    partyFractionalTallyMass partyCandidates fractionalTally active
        =
        ∑ candidate ∈ activePartyCandidates active partyCandidates,
          fractionalTally candidate := rfl
    _ <
        ∑ _candidate ∈ activePartyCandidates active partyCandidates,
          quota :=
        Finset.sum_lt_sum_of_nonempty hnonempty hlt
    _ =
        ((activePartyCandidates active partyCandidates).card : ℝ) * quota := by
        simp [Finset.sum_const, nsmul_eq_mul]

/--
Primitive transfer law for one party projection of one concrete STV trace step.

This exposes a step-level transfer-rule assumption: focused same-party
elections retain exactly one quota and transfer the full surplus, focused
same-party eliminations preserve same-party vote mass, and focused outside-party
steps leave this party projection unchanged.
-/
def FractionalPartySTVPrimitiveTransferStepLaw {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (quota : ℝ) (step : STVStep Candidate)
    (before : PartyQuotaState) : Prop :=
  step.removesFocusedCandidate ∧
    ∃ focused, step.focus = some focused ∧
      if focused ∈ partyCandidates then
        match step.kind with
        | StepKind.elect =>
            0 < before.remainingCandidates ∧
              0 ≤ fractionalTally focused ∧
              quota ≤ fractionalTally focused ∧
              fractionalTally focused ≤ before.voteMass
        | StepKind.eliminate =>
            0 < before.remainingCandidates ∧
              0 ≤ fractionalTally focused ∧
              fractionalTally focused ≤ before.voteMass
        | StepKind.transfer => False
        | StepKind.finish => False
      else True

/--
Source-step law for one party projection of a concrete fractional STV step.

This is closer to executable trace semantics than
`FractionalPartySTVPrimitiveTransferStepLaw`: it states that the focused
candidate is active, active fractional tallies are nonnegative, the party state
records the current active same-party candidate count and same-party tally
mass, and same-party focused elections meet quota. These are the facts a
concrete STV implementation or transfer-rule replay should prove step by step.
-/
def FractionalPartySTVSourceStepLaw {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (quota : ℝ) (step : STVStep Candidate)
    (before : PartyQuotaState) : Prop :=
  step.removesFocusedCandidate ∧
    ∃ focused, step.focus = some focused ∧
      focused ∈ step.beforeActive ∧
      (∀ candidate, candidate ∈ step.beforeActive →
        0 ≤ fractionalTally candidate) ∧
      before.remainingCandidates =
        (activePartyCandidates step.beforeActive partyCandidates).card ∧
      before.voteMass =
        partyFractionalTallyMass partyCandidates fractionalTally
          step.beforeActive ∧
      (focused ∈ partyCandidates →
        (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) ∧
          (step.kind = StepKind.elect → quota ≤ fractionalTally focused))

/--
When a source step's party projection has no active same-party candidate at
quota, the projected party vote mass is below `remainingCandidates * quota`.
-/
theorem voteMass_lt_remaining_mul_quota_of_sourceStepLaw_forall_activeParty_lt
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {fractionalTally : Candidate → ℝ}
    {quota : ℝ} {step : STVStep Candidate} {before : PartyQuotaState}
    (hlaw :
      FractionalPartySTVSourceStepLaw partyCandidates fractionalTally quota
        step before)
    (hpartyActive :
      ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive)
    (hlt :
      ∀ candidate,
        candidate ∈ activePartyCandidates step.beforeActive partyCandidates →
          fractionalTally candidate < quota) :
    before.voteMass < (before.remainingCandidates : ℝ) * quota := by
  rcases hlaw with
    ⟨_hremove, _focused, _hfocus, _hfocused_active, _hnonneg,
      hremaining, hmass, _hfocused_party_law⟩
  rcases hpartyActive with ⟨same, hsame_party, hsame_active⟩
  have hnonempty :
      (activePartyCandidates step.beforeActive partyCandidates).Nonempty := by
    exact ⟨same, by
      simp [activePartyCandidates, hsame_active, hsame_party]⟩
  have hmass_lt :
      partyFractionalTallyMass partyCandidates fractionalTally
          step.beforeActive <
        ((activePartyCandidates step.beforeActive partyCandidates).card : ℝ) *
          quota :=
    partyFractionalTallyMass_lt_card_mul_quota_of_forall_lt
      (partyCandidates := partyCandidates) (active := step.beforeActive)
      (fractionalTally := fractionalTally) (quota := quota)
      hnonempty hlt
  rw [hmass, hremaining]
  exact hmass_lt

/--
Fractional first-active tally induced by voter weights at an active set.
-/
def fractionalActiveTally {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (weight : Voter → ℝ) (active : Finset Candidate)
    (candidate : Candidate) : ℝ :=
  ∑ voter ∈ Ballot.activeSupport voters ballots active candidate, weight voter

theorem activeSupport_union {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters₁ voters₂ : Finset Voter) (ballots : Voter → Ballot Candidate)
    (active : Finset Candidate) (candidate : Candidate) :
    Ballot.activeSupport (voters₁ ∪ voters₂) ballots active candidate =
      Ballot.activeSupport voters₁ ballots active candidate ∪
        Ballot.activeSupport voters₂ ballots active candidate := by
  ext voter
  by_cases hnext : Ballot.nextActive (ballots voter) active = some candidate
  · simp [Ballot.activeSupport, hnext]
  · simp [Ballot.activeSupport, hnext]

theorem fractionalActiveTally_congr_weight_on_activeSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight otherWeight : Voter → ℝ} {active : Finset Candidate}
    {candidate : Candidate}
    (hweight :
      ∀ voter,
        voter ∈ Ballot.activeSupport voters ballots active candidate →
          weight voter = otherWeight voter) :
    fractionalActiveTally voters ballots weight active candidate =
      fractionalActiveTally voters ballots otherWeight active candidate := by
  dsimp [fractionalActiveTally]
  exact Finset.sum_congr rfl hweight

theorem fractionalActiveTally_union
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters₁ voters₂ : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {active : Finset Candidate} {candidate : Candidate}
    (hdisjoint : Disjoint voters₁ voters₂) :
    fractionalActiveTally (voters₁ ∪ voters₂) ballots weight active candidate =
      fractionalActiveTally voters₁ ballots weight active candidate +
        fractionalActiveTally voters₂ ballots weight active candidate := by
  dsimp [fractionalActiveTally]
  rw [activeSupport_union]
  have hsupport_disjoint :
      Disjoint (Ballot.activeSupport voters₁ ballots active candidate)
        (Ballot.activeSupport voters₂ ballots active candidate) := by
    rw [Finset.disjoint_left] at hdisjoint ⊢
    intro voter hvoter₁ hvoter₂
    exact hdisjoint ((Finset.mem_filter.mp hvoter₁).1)
      ((Finset.mem_filter.mp hvoter₂).1)
  exact Finset.sum_union hsupport_disjoint

theorem fractionalActiveTally_eq_left_of_union_right_support_empty
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters₁ voters₂ : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {weight leftWeight : Voter → ℝ} {active : Finset Candidate}
    {candidate : Candidate}
    (hpartition : allVoters = voters₁ ∪ voters₂)
    (hdisjoint : Disjoint voters₁ voters₂)
    (hright_empty :
      Ballot.activeSupport voters₂ ballots active candidate = ∅)
    (hleft_weight :
      ∀ voter, voter ∈ voters₁ → weight voter = leftWeight voter) :
    fractionalActiveTally allVoters ballots weight active candidate =
      fractionalActiveTally voters₁ ballots leftWeight active candidate := by
  rw [hpartition, fractionalActiveTally_union hdisjoint]
  have hright_zero :
      fractionalActiveTally voters₂ ballots weight active candidate = 0 := by
    simp [fractionalActiveTally, hright_empty]
  have hleft_eq :
      fractionalActiveTally voters₁ ballots weight active candidate =
        fractionalActiveTally voters₁ ballots leftWeight active candidate :=
    fractionalActiveTally_congr_weight_on_activeSupport (by
      intro voter hvoter
      exact hleft_weight voter ((Finset.mem_filter.mp hvoter).1))
  rw [hright_zero, add_zero, hleft_eq]

theorem fractionalActiveTally_eq_right_of_union_left_support_empty
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters₁ voters₂ : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {weight rightWeight : Voter → ℝ} {active : Finset Candidate}
    {candidate : Candidate}
    (hpartition : allVoters = voters₁ ∪ voters₂)
    (hdisjoint : Disjoint voters₁ voters₂)
    (hleft_empty :
      Ballot.activeSupport voters₁ ballots active candidate = ∅)
    (hright_weight :
      ∀ voter, voter ∈ voters₂ → weight voter = rightWeight voter) :
    fractionalActiveTally allVoters ballots weight active candidate =
      fractionalActiveTally voters₂ ballots rightWeight active candidate := by
  rw [hpartition, fractionalActiveTally_union hdisjoint]
  have hleft_zero :
      fractionalActiveTally voters₁ ballots weight active candidate = 0 := by
    simp [fractionalActiveTally, hleft_empty]
  have hright_eq :
      fractionalActiveTally voters₂ ballots weight active candidate =
        fractionalActiveTally voters₂ ballots rightWeight active candidate :=
    fractionalActiveTally_congr_weight_on_activeSupport (by
      intro voter hvoter
      exact hright_weight voter ((Finset.mem_filter.mp hvoter).1))
  rw [hleft_zero, zero_add, hright_eq]

/-- Fractional active tallies are nonnegative when all voter weights are nonnegative. -/
theorem fractionalActiveTally_nonneg {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {weight : Voter → ℝ}
    {active : Finset Candidate}
    (hweight_nonneg : ∀ voter, voter ∈ voters → 0 ≤ weight voter)
    (candidate : Candidate) :
    0 ≤ fractionalActiveTally voters ballots weight active candidate := by
  dsimp [fractionalActiveTally]
  exact Finset.sum_nonneg fun voter hvoter =>
    hweight_nonneg voter ((Finset.mem_filter.mp hvoter).1)

/-- Scale exactly the voters in `support` by `factor`, leaving all others unchanged. -/
def scaleOnSupport {Voter : Type*} [DecidableEq Voter]
    (support : Finset Voter) (factor : ℝ) (weight : Voter → ℝ)
    (voter : Voter) : ℝ :=
  if voter ∈ support then factor * weight voter else weight voter

/--
Splitting identity for support scaling: scaling `support` by `factor` changes
the total weight over a containing electorate by `(factor - 1)` times the
support's current total weight.
-/
theorem sum_scaleOnSupport_eq_sum_add_factor_sub_one_mul_sum
    {Voter : Type*} [DecidableEq Voter]
    {support voters : Finset Voter} {factor : ℝ} {weight : Voter → ℝ}
    (hsubset : support ⊆ voters) :
    (∑ voter ∈ voters, scaleOnSupport support factor weight voter) =
      (∑ voter ∈ voters, weight voter) +
        (factor - 1) * (∑ voter ∈ support, weight voter) := by
  classical
  have hfilter :
      voters.filter (fun voter => voter ∈ support) = support := by
    ext voter
    constructor
    · intro hvoter
      exact (Finset.mem_filter.mp hvoter).2
    · intro hvoter
      exact Finset.mem_filter.mpr ⟨hsubset hvoter, hvoter⟩
  calc
    (∑ voter ∈ voters, scaleOnSupport support factor weight voter)
        =
        ∑ voter ∈ voters,
          (weight voter +
            if voter ∈ support then
              (factor - 1) * weight voter
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro voter hvoter
          by_cases hsupport : voter ∈ support
          · simp [scaleOnSupport, hsupport]
            ring
          · simp [scaleOnSupport, hsupport]
    _ =
        (∑ voter ∈ voters, weight voter) +
          ∑ voter ∈ voters,
            (if voter ∈ support then
              (factor - 1) * weight voter
            else
              0) := by
          rw [Finset.sum_add_distrib]
    _ =
        (∑ voter ∈ voters, weight voter) +
          ∑ voter ∈ voters.filter (fun voter => voter ∈ support),
            (factor - 1) * weight voter := by
          rw [Finset.sum_filter]
    _ =
        (∑ voter ∈ voters, weight voter) +
          ∑ voter ∈ support, (factor - 1) * weight voter := by
          rw [hfilter]
    _ =
        (∑ voter ∈ voters, weight voter) +
          (factor - 1) * (∑ voter ∈ support, weight voter) := by
          rw [← Finset.mul_sum]

/--
If focused supporters have total tally `focusedTally` and are scaled by the
fractional STV surplus factor `(focusedTally - quota) / focusedTally`, the
total electorate weight drops by exactly one quota.
-/
theorem sum_scaleOnSupport_surplusFactor_eq_sum_sub_quota
    {Voter : Type*} [DecidableEq Voter]
    {support voters : Finset Voter} {weight : Voter → ℝ}
    {focusedTally quota : ℝ}
    (hsubset : support ⊆ voters)
    (hfocused :
      (∑ voter ∈ support, weight voter) = focusedTally)
    (hfocused_ne : focusedTally ≠ 0) :
    (∑ voter ∈ voters,
        scaleOnSupport support ((focusedTally - quota) / focusedTally)
          weight voter) =
      (∑ voter ∈ voters, weight voter) - quota := by
  rw [sum_scaleOnSupport_eq_sum_add_factor_sub_one_mul_sum hsubset,
    hfocused]
  have hfactor :
      ((focusedTally - quota) / focusedTally - 1) * focusedTally =
        -quota := by
    field_simp [hfocused_ne]
    ring
  linarith

/-- Fractional STV surplus multiplier for an elected candidate's supporters. -/
noncomputable def fractionalSurplusFactor (focusedTally quota : ℝ) : ℝ :=
  (focusedTally - quota) / focusedTally

/--
One-round fractional STV weight update. An election scales the focused
candidate's current active supporters by the surplus factor; eliminations and
nonordinary bookkeeping labels preserve voter weights.
-/
noncomputable def fractionalSTVNextWeight {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (step : STVStep Candidate) (weight : Voter → ℝ)
    (voter : Voter) : ℝ :=
  match step.focus with
  | none => weight voter
  | some focused =>
      match step.kind with
      | StepKind.elect =>
          scaleOnSupport
            (Ballot.activeSupport voters ballots step.beforeActive focused)
            (fractionalSurplusFactor
              (fractionalActiveTally voters ballots weight
                step.beforeActive focused)
              quota)
            weight voter
      | StepKind.eliminate => weight voter
      | StepKind.transfer => weight voter
      | StepKind.finish => weight voter

theorem activeSupport_subset_voters {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate} :
    Ballot.activeSupport voters ballots active candidate ⊆ voters := by
  intro voter hvoter
  exact (Finset.mem_filter.mp hvoter).1

/-- Active support is monotone in the voter set. -/
theorem activeSupport_subset_of_subset {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters₁ voters₂ : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hsubset : voters₁ ⊆ voters₂) :
    Ballot.activeSupport voters₁ ballots active candidate ⊆
      Ballot.activeSupport voters₂ ballots active candidate := by
  intro voter hvoter
  rw [Ballot.activeSupport] at hvoter ⊢
  exact Finset.mem_filter.mpr
    ⟨hsubset (Finset.mem_filter.mp hvoter).1,
      (Finset.mem_filter.mp hvoter).2⟩

/--
Fractional active tallies are monotone in the voter set when all added voters
have nonnegative weight.
-/
theorem fractionalActiveTally_le_of_voters_subset {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters₁ voters₂ : Finset Voter}
    {ballots : Voter → Ballot Candidate} {weight : Voter → ℝ}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : voters₁ ⊆ voters₂)
    (hweight_nonneg : ∀ voter, voter ∈ voters₂ → 0 ≤ weight voter) :
    fractionalActiveTally voters₁ ballots weight active candidate ≤
      fractionalActiveTally voters₂ ballots weight active candidate := by
  dsimp [fractionalActiveTally]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (activeSupport_subset_of_subset (ballots := ballots)
        (active := active) (candidate := candidate) hsubset)
      (by
        intro voter hvoter _hvoter_not_left
        exact hweight_nonneg voter ((Finset.mem_filter.mp hvoter).1))

/--
The fractional STV weight update preserves nonnegativity when an elected
focused candidate meets a positive quota.
-/
theorem fractionalSTVNextWeight_nonneg {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {step : STVStep Candidate} {weight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, voter ∈ voters → 0 ≤ weight voter)
    (hquota_pos : 0 < quota)
    (hquota_if_elect :
      ∀ focused, step.focus = some focused →
        step.kind = StepKind.elect →
          quota ≤
            fractionalActiveTally voters ballots weight step.beforeActive
              focused) :
    ∀ voter, voter ∈ voters →
      0 ≤ fractionalSTVNextWeight voters ballots quota step weight voter := by
  intro voter hvoter
  cases hfocus : step.focus with
  | none =>
      simp [fractionalSTVNextWeight, hfocus, hweight_nonneg voter hvoter]
  | some focused =>
      cases hkind : step.kind with
      | elect =>
          by_cases hsupport :
              voter ∈
                Ballot.activeSupport voters ballots step.beforeActive
                  focused
          · have hquota_le :
                quota ≤
                  fractionalActiveTally voters ballots weight
                    step.beforeActive focused :=
              hquota_if_elect focused hfocus hkind
            have htally_pos :
                0 <
                  fractionalActiveTally voters ballots weight
                    step.beforeActive focused :=
              lt_of_lt_of_le hquota_pos hquota_le
            have hfactor_nonneg :
                0 ≤
                  fractionalSurplusFactor
                    (fractionalActiveTally voters ballots weight
                      step.beforeActive focused)
                    quota := by
              dsimp [fractionalSurplusFactor]
              exact div_nonneg (sub_nonneg.mpr hquota_le) htally_pos.le
            simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
              hsupport, mul_nonneg hfactor_nonneg
                (hweight_nonneg voter hvoter)]
          · simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
              hsupport, hweight_nonneg voter hvoter]
      | eliminate =>
          simp [fractionalSTVNextWeight, hfocus, hkind,
            hweight_nonneg voter hvoter]
      | transfer =>
          simp [fractionalSTVNextWeight, hfocus, hkind,
            hweight_nonneg voter hvoter]
      | finish =>
          simp [fractionalSTVNextWeight, hfocus, hkind,
            hweight_nonneg voter hvoter]

/--
Under two solid coalitions, the global one-round fractional weight update
restricts to the party-specific update on voters in the first coalition.
-/
theorem fractionalSTVNextWeight_eq_on_solidCoalition_left
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters otherVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {quota : ℝ} {step : STVStep Candidate}
    {allWeight weight : Voter → ℝ}
    (hpartition : allVoters = voters ∪ otherVoters)
    (hvoterDisjoint : Disjoint voters otherVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherVoters ballots otherPartyCandidates)
    (hpartyActive :
      ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive)
    (hotherActive :
      ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive)
    (hweight : ∀ voter, voter ∈ voters → allWeight voter = weight voter) :
    ∀ voter, voter ∈ voters →
      fractionalSTVNextWeight allVoters ballots quota step allWeight voter =
        fractionalSTVNextWeight voters ballots quota step weight voter := by
  intro voter hvoter
  cases hfocus : step.focus with
  | none =>
      simp [fractionalSTVNextWeight, hfocus, hweight voter hvoter]
  | some focused =>
      cases hkind : step.kind with
      | elect =>
          by_cases hparty : focused ∈ partyCandidates
          · have hfocused_not_other : focused ∉ otherPartyCandidates := by
              intro hfocused_other
              exact (Finset.disjoint_left.mp hcandidateDisjoint)
                hparty hfocused_other
            have hother_empty :
                Ballot.activeSupport otherVoters ballots step.beforeActive
                  focused = ∅ :=
              activeSupport_eq_empty_of_solidCoalitionBallots_outside
                hotherSolid hotherActive hfocused_not_other
            have htally :
                fractionalActiveTally allVoters ballots allWeight
                    step.beforeActive focused =
                  fractionalActiveTally voters ballots weight
                    step.beforeActive focused :=
              fractionalActiveTally_eq_left_of_union_right_support_empty
                (allVoters := allVoters) (voters₁ := voters)
                (voters₂ := otherVoters) (ballots := ballots)
                (weight := allWeight) (leftWeight := weight)
                (active := step.beforeActive) (candidate := focused)
                hpartition hvoterDisjoint hother_empty hweight
            by_cases hsupport :
                voter ∈
                  Ballot.activeSupport voters ballots step.beforeActive focused
            · have hsupport_all :
                  voter ∈
                    Ballot.activeSupport allVoters ballots step.beforeActive
                      focused := by
                rw [Ballot.activeSupport] at hsupport ⊢
                exact Finset.mem_filter.mpr
                  ⟨by
                    rw [hpartition]
                    exact Finset.mem_union.mpr (Or.inl hvoter),
                   (Finset.mem_filter.mp hsupport).2⟩
              simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
                hsupport, hsupport_all, htally, hweight voter hvoter]
            · have hsupport_all :
                  voter ∉
                    Ballot.activeSupport allVoters ballots step.beforeActive
                      focused := by
                intro hsupport_all
                have hnext :
                    Ballot.nextActive (ballots voter) step.beforeActive =
                      some focused :=
                  (Finset.mem_filter.mp hsupport_all).2
                exact hsupport
                  (Finset.mem_filter.mpr ⟨hvoter, hnext⟩)
              simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
                hsupport, hsupport_all, hweight voter hvoter]
          · have hsupport :
                voter ∉
                  Ballot.activeSupport voters ballots step.beforeActive
                    focused := by
              rw [activeSupport_eq_empty_of_solidCoalitionBallots_outside
                hsolid hpartyActive hparty]
              simp
            have hsupport_all :
                voter ∉
                  Ballot.activeSupport allVoters ballots step.beforeActive
                    focused := by
              intro hsupport_all
              have hnext :
                  Ballot.nextActive (ballots voter) step.beforeActive =
                    some focused :=
                (Finset.mem_filter.mp hsupport_all).2
              exact hsupport (Finset.mem_filter.mpr ⟨hvoter, hnext⟩)
            simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
              hsupport, hsupport_all, hweight voter hvoter]
      | eliminate =>
          simp [fractionalSTVNextWeight, hfocus, hkind,
            hweight voter hvoter]
      | transfer =>
          simp [fractionalSTVNextWeight, hfocus, hkind,
            hweight voter hvoter]
      | finish =>
          simp [fractionalSTVNextWeight, hfocus, hkind,
            hweight voter hvoter]

/--
On an election round with nonzero focused tally, the one-round fractional STV
weight update transfers all excess weight and removes exactly one quota of
total weight.
-/
theorem sum_fractionalSTVNextWeight_elect_eq_sum_sub_quota
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {step : STVStep Candidate} {weight : Voter → ℝ}
    {focused : Candidate}
    (hfocus : step.focus = some focused)
    (hkind : step.kind = StepKind.elect)
    (hfocused_ne :
      fractionalActiveTally voters ballots weight step.beforeActive
        focused ≠ 0) :
    (∑ voter ∈ voters,
        fractionalSTVNextWeight voters ballots quota step weight voter) =
      (∑ voter ∈ voters, weight voter) - quota := by
  simp [fractionalSTVNextWeight, hfocus, hkind, fractionalSurplusFactor]
  exact
    sum_scaleOnSupport_surplusFactor_eq_sum_sub_quota
      (support :=
        Ballot.activeSupport voters ballots step.beforeActive focused)
      (voters := voters) (weight := weight)
      (focusedTally :=
        fractionalActiveTally voters ballots weight step.beforeActive focused)
      (quota := quota)
      activeSupport_subset_voters rfl hfocused_ne

/-- Non-election rounds preserve total voter weight under the one-round update. -/
theorem sum_fractionalSTVNextWeight_of_kind_ne_elect
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {step : STVStep Candidate} {weight : Voter → ℝ}
    (hkind : step.kind ≠ StepKind.elect) :
    (∑ voter ∈ voters,
        fractionalSTVNextWeight voters ballots quota step weight voter) =
      ∑ voter ∈ voters, weight voter := by
  cases hfocus : step.focus with
  | none =>
      simp [fractionalSTVNextWeight, hfocus]
  | some focused =>
      cases hstep_kind : step.kind <;>
        simp [fractionalSTVNextWeight, hfocus, hstep_kind] at hkind ⊢

/--
An election round whose focused candidate has no current support in the chosen
voter set preserves that set's total weight.
-/
theorem sum_fractionalSTVNextWeight_elect_eq_sum_of_activeSupport_eq_empty
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {step : STVStep Candidate} {weight : Voter → ℝ}
    {focused : Candidate}
    (hfocus : step.focus = some focused)
    (hkind : step.kind = StepKind.elect)
    (hempty :
      Ballot.activeSupport voters ballots step.beforeActive focused = ∅) :
    (∑ voter ∈ voters,
        fractionalSTVNextWeight voters ballots quota step weight voter) =
      ∑ voter ∈ voters, weight voter := by
  refine Finset.sum_congr rfl ?_
  intro voter hvoter
  have hsupport :
      voter ∉ Ballot.activeSupport voters ballots step.beforeActive focused := by
    rw [hempty]
    simp
  simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport, hsupport]

/--
For any subgroup of voters, a global fractional STV election round can remove
at most one quota of that subgroup's total weight.
-/
theorem sum_fractionalSTVNextWeight_elect_ge_sum_sub_quota_of_subset
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {step : STVStep Candidate} {weight : Voter → ℝ}
    {focused : Candidate}
    (hvoters_subset : voters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ weight voter)
    (hquota_pos : 0 < quota)
    (hfocus : step.focus = some focused)
    (hkind : step.kind = StepKind.elect)
    (hquota_le :
      quota ≤
        fractionalActiveTally allVoters ballots weight step.beforeActive
          focused) :
    (∑ voter ∈ voters, weight voter) - quota ≤
      ∑ voter ∈ voters,
        fractionalSTVNextWeight allVoters ballots quota step weight voter := by
  let globalTally :=
    fractionalActiveTally allVoters ballots weight step.beforeActive focused
  let partyTally :=
    fractionalActiveTally voters ballots weight step.beforeActive focused
  have hglobal_pos : 0 < globalTally := by
    exact lt_of_lt_of_le hquota_pos hquota_le
  have hglobal_ne : globalTally ≠ 0 := hglobal_pos.ne'
  have hparty_nonneg : 0 ≤ partyTally := by
    exact fractionalActiveTally_nonneg
      (voters := voters) (ballots := ballots) (weight := weight)
      (active := step.beforeActive)
      (fun voter hvoter => hweight_nonneg voter (hvoters_subset hvoter))
      focused
  have hparty_le_global : partyTally ≤ globalTally := by
    exact fractionalActiveTally_le_of_voters_subset
      (voters₁ := voters) (voters₂ := allVoters) (ballots := ballots)
      (weight := weight) (active := step.beforeActive) (candidate := focused)
      hvoters_subset hweight_nonneg
  have hsum_eq :
      (∑ voter ∈ voters,
          fractionalSTVNextWeight allVoters ballots quota step weight voter) =
        ∑ voter ∈ voters,
          scaleOnSupport
            (Ballot.activeSupport voters ballots step.beforeActive focused)
            (fractionalSurplusFactor globalTally quota) weight voter := by
    refine Finset.sum_congr rfl ?_
    intro voter hvoter
    by_cases hsupport :
        voter ∈ Ballot.activeSupport voters ballots step.beforeActive focused
    · have hsupport_all :
          voter ∈
            Ballot.activeSupport allVoters ballots step.beforeActive focused :=
        activeSupport_subset_of_subset (ballots := ballots)
          (active := step.beforeActive) (candidate := focused)
          hvoters_subset hsupport
      simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
        globalTally, hsupport, hsupport_all]
    · have hsupport_all :
          voter ∉
            Ballot.activeSupport allVoters ballots step.beforeActive focused := by
        intro hsupport_all
        exact hsupport
          (Finset.mem_filter.mpr
            ⟨hvoter, (Finset.mem_filter.mp hsupport_all).2⟩)
      simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport,
        hsupport, hsupport_all]
  have hscaled :
      (∑ voter ∈ voters,
          scaleOnSupport
            (Ballot.activeSupport voters ballots step.beforeActive focused)
            (fractionalSurplusFactor globalTally quota) weight voter) =
        (∑ voter ∈ voters, weight voter) +
          (fractionalSurplusFactor globalTally quota - 1) * partyTally := by
    simpa [partyTally, fractionalActiveTally] using
      sum_scaleOnSupport_eq_sum_add_factor_sub_one_mul_sum
        (support :=
          Ballot.activeSupport voters ballots step.beforeActive focused)
        (voters := voters)
        (factor := fractionalSurplusFactor globalTally quota)
        (weight := weight)
        activeSupport_subset_voters
  have hfactor_bound :
      -quota ≤ (fractionalSurplusFactor globalTally quota - 1) * partyTally := by
    have hfactor_eq :
        (fractionalSurplusFactor globalTally quota - 1) * partyTally =
          -(quota / globalTally) * partyTally := by
      dsimp [fractionalSurplusFactor]
      field_simp [hglobal_ne]
      ring
    have hcoef_nonneg : 0 ≤ quota / globalTally :=
      div_nonneg hquota_pos.le hglobal_pos.le
    have hloss_le : (quota / globalTally) * partyTally ≤ quota := by
      have hmul :=
        mul_le_mul_of_nonneg_left hparty_le_global hcoef_nonneg
      have hcoef_mul : (quota / globalTally) * globalTally = quota := by
        field_simp [hglobal_ne]
      nlinarith
    rw [hfactor_eq]
    nlinarith
  rw [hsum_eq, hscaled]
  linarith

/--
If a solid coalition still has an active same-party candidate, an election of
an outside-party candidate does not change that coalition's total weight in
the global fractional STV update.
-/
theorem sum_fractionalSTVNextWeight_elect_eq_sum_of_solidCoalition_outside
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate}
    {quota : ℝ} {step : STVStep Candidate} {weight : Voter → ℝ}
    {focused : Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hpartyActive :
      ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive)
    (hfocus : step.focus = some focused)
    (hkind : step.kind = StepKind.elect)
    (hfocused_not_party : focused ∉ partyCandidates) :
    (∑ voter ∈ voters,
        fractionalSTVNextWeight allVoters ballots quota step weight voter) =
      ∑ voter ∈ voters, weight voter := by
  have hempty :
      Ballot.activeSupport voters ballots step.beforeActive focused = ∅ :=
    activeSupport_eq_empty_of_solidCoalitionBallots_outside
      hsolid hpartyActive hfocused_not_party
  refine Finset.sum_congr rfl ?_
  intro voter hvoter
  have hsupport_party :
      voter ∉ Ballot.activeSupport voters ballots step.beforeActive focused := by
    rw [hempty]
    simp
  have hsupport_all :
      voter ∉ Ballot.activeSupport allVoters ballots step.beforeActive focused := by
    intro hsupport_all
    exact hsupport_party
      (Finset.mem_filter.mpr
        ⟨hvoter, (Finset.mem_filter.mp hsupport_all).2⟩)
  simp [fractionalSTVNextWeight, hfocus, hkind, scaleOnSupport, hsupport_all]

/--
Source-level one-step law for the same-party voter weights used by a
fractional STV replay. Same-party focused elections meet quota; outside-party
focused elections have no support from this voter group.
-/
def FractionalSTVPartyWeightStepLaw {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (step : STVStep Candidate) (weight : Voter → ℝ) : Prop :=
  (∀ focused, step.focus = some focused →
      step.kind = StepKind.elect → focused ∈ partyCandidates →
        quota ≤
          fractionalActiveTally voters ballots weight step.beforeActive
            focused) ∧
    (∀ focused, step.focus = some focused →
      step.kind = StepKind.elect → focused ∉ partyCandidates →
        Ballot.activeSupport voters ballots step.beforeActive focused = ∅)

/--
Recursive fractional STV weight dynamics over a concrete trace prefix.
-/
noncomputable def fractionalSTVWeightAfterSteps {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    List (STVStep Candidate) → (Voter → ℝ) → Voter → ℝ
  | [], weight => weight
  | step :: steps, weight =>
      fractionalSTVWeightAfterSteps voters ballots quota steps
        (fractionalSTVNextWeight voters ballots quota step weight)

/--
Source-level trace law for fractional STV voter-weight dynamics, stated
recursively so it follows the same prefix fold as
`fractionalSTVWeightAfterSteps`.
-/
def FractionalSTVPartyWeightTraceLaw {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates : Finset Candidate) (quota : ℝ) :
    List (STVStep Candidate) → (Voter → ℝ) → Prop
  | [], _weight => True
  | step :: steps, weight =>
      FractionalSTVPartyWeightStepLaw voters ballots partyCandidates quota
        step weight ∧
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps (fractionalSTVNextWeight voters ballots quota step weight)

theorem fractionalSTVPartyWeightTraceLaw_take {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hlaw :
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps initialWeight)
    (n : ℕ) :
    FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
      (steps.take n) initialWeight := by
  induction steps generalizing n initialWeight with
  | nil =>
      simp [FractionalSTVPartyWeightTraceLaw]
  | cons step steps ih =>
      cases n with
      | zero =>
          simp [FractionalSTVPartyWeightTraceLaw]
      | succ n =>
          rcases hlaw with ⟨hstep, hrest⟩
          exact ⟨hstep, ih hrest n⟩

theorem fractionalSTVPartyWeightTraceLaw_of_getElem {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hstep :
      ∀ i : Fin steps.length,
        FractionalSTVPartyWeightStepLaw voters ballots partyCandidates quota
          (steps.get i)
          (fractionalSTVWeightAfterSteps voters ballots quota
            (steps.take i.1) initialWeight)) :
    FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
      steps initialWeight := by
  induction steps generalizing initialWeight with
  | nil =>
      simp [FractionalSTVPartyWeightTraceLaw]
  | cons step steps ih =>
      constructor
      · have h0 := hstep ⟨0, by simp⟩
        simpa [fractionalSTVWeightAfterSteps] using h0
      · apply ih
        intro i
        have hsucc := hstep ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
        simpa [fractionalSTVWeightAfterSteps, Nat.succ_eq_add_one]
          using hsucc

@[simp] theorem fractionalSTVWeightAfterSteps_nil {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (weight : Voter → ℝ) :
    fractionalSTVWeightAfterSteps voters ballots quota
      ([] : List (STVStep Candidate)) weight = weight := rfl

@[simp] theorem fractionalSTVWeightAfterSteps_cons {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (step : STVStep Candidate)
    (steps : List (STVStep Candidate)) (weight : Voter → ℝ) :
    fractionalSTVWeightAfterSteps voters ballots quota (step :: steps) weight =
      fractionalSTVWeightAfterSteps voters ballots quota steps
        (fractionalSTVNextWeight voters ballots quota step weight) := rfl

/--
Concrete executable fractional STV step generated from an active focused
candidate. It removes the focused candidate and labels the round as an
election exactly when the current fractional tally reaches quota; otherwise it
labels the round as an elimination. Tie-breaking/focus selection is supplied by
the caller, so this definition can be reused with different deterministic
tie-breakers.
-/
noncomputable def fractionalSTVStepFromFocus {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    (focused : Candidate) : STVStep Candidate where
  beforeActive := active
  afterActive := active.erase focused
  kind :=
    if quota ≤ fractionalActiveTally voters ballots weight active focused then
      StepKind.elect
    else
      StepKind.eliminate
  focus := some focused
  tally := fun _candidate => 0

@[simp] theorem fractionalSTVStepFromFocus_beforeActive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    (focused : Candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).beforeActive =
      active := rfl

@[simp] theorem fractionalSTVStepFromFocus_afterActive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    (focused : Candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).afterActive =
      active.erase focused := rfl

@[simp] theorem fractionalSTVStepFromFocus_focus
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    (focused : Candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).focus =
      some focused := rfl

/-- A generated focused step removes exactly its focused candidate. -/
theorem fractionalSTVStepFromFocus_removesFocusedCandidate
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    (focused : Candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).removesFocusedCandidate :=
  ⟨focused, rfl, rfl⟩

/-- A generated focused step has an active focused candidate when the supplied focus is active. -/
theorem fractionalSTVStepFromFocus_focus_active
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    {focused : Candidate} (hfocused : focused ∈ active) :
    ∃ selected,
      (fractionalSTVStepFromFocus voters ballots quota active weight focused).focus =
        some selected ∧
        selected ∈
          (fractionalSTVStepFromFocus voters ballots quota active weight focused).beforeActive :=
  ⟨focused, rfl, hfocused⟩

/-- Generated focused steps are ordinary elect/eliminate rounds. -/
theorem fractionalSTVStepFromFocus_kind_allowed
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (active : Finset Candidate) (weight : Voter → ℝ)
    (focused : Candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).kind =
        StepKind.elect ∨
      (fractionalSTVStepFromFocus voters ballots quota active weight focused).kind =
        StepKind.eliminate := by
  by_cases hquota :
      quota ≤ fractionalActiveTally voters ballots weight active focused
  · left
    simp [fractionalSTVStepFromFocus, hquota]
  · right
    simp [fractionalSTVStepFromFocus, hquota]

/--
If a generated focused step is labeled as an election, then the focused
candidate's current fractional tally meets quota.
-/
theorem fractionalSTVStepFromFocus_quota_if_elect
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {active : Finset Candidate} {weight : Voter → ℝ}
    {focused selected : Candidate}
    (hfocus :
      (fractionalSTVStepFromFocus voters ballots quota active weight focused).focus =
        some selected)
    (helect :
      (fractionalSTVStepFromFocus voters ballots quota active weight focused).kind =
        StepKind.elect) :
    quota ≤ fractionalActiveTally voters ballots weight active selected := by
  have hselected : focused = selected := by
    simpa [fractionalSTVStepFromFocus] using Option.some.inj hfocus
  subst selected
  by_contra hquota
  have hkind :
      (fractionalSTVStepFromFocus voters ballots quota active weight focused).kind =
        StepKind.eliminate := by
    simp [fractionalSTVStepFromFocus, hquota]
  rw [hkind] at helect
  contradiction

/--
Deterministic choice rule for an executable fractional STV run.

The rule receives the current active set and the current fractional tally
function. It may return `none` to stop; if it returns a candidate, that candidate
must be active. Concrete papers instantiate this with their tie-breaking or
selection convention.
-/
structure FractionalSTVChoiceRule (Candidate : Type*) where
  choose : Finset Candidate → (Candidate → ℝ) → Option Candidate
  choose_mem :
    ∀ {active : Finset Candidate} {tally : Candidate → ℝ} {focused},
      choose active tally = some focused → focused ∈ active

namespace FractionalSTVChoiceRule

/--
A choice rule is total when it selects an active candidate whenever the active
set is nonempty.
-/
def Total {Candidate : Type*} (choice : FractionalSTVChoiceRule Candidate) :
    Prop :=
  ∀ {active : Finset Candidate} {tally : Candidate → ℝ},
    active.Nonempty → ∃ focused, choice.choose active tally = some focused

/--
A choice rule is quota-respecting when, whenever some active candidate has
reached quota, the chosen candidate has also reached quota. This is the
paper-neutral "elect quota candidates before eliminations" condition for the
fractional STV simulator; tie-breaking among multiple eligible candidates
remains source-specific.
-/
def QuotaRespecting {Candidate : Type*}
    (choice : FractionalSTVChoiceRule Candidate) (quota : ℝ) : Prop :=
  ∀ {active : Finset Candidate} {tally : Candidate → ℝ} {focused},
    choice.choose active tally = some focused →
      (∃ candidate, candidate ∈ active ∧ quota ≤ tally candidate) →
        quota ≤ tally focused

/-- A choice rule cannot select a candidate from an empty active set. -/
theorem choose_eq_none_of_empty {Candidate : Type*}
    (choice : FractionalSTVChoiceRule Candidate) (tally : Candidate → ℝ) :
    choice.choose (∅ : Finset Candidate) tally = none := by
  cases hchoose : choice.choose (∅ : Finset Candidate) tally with
  | none => rfl
  | some focused =>
      have hmem : focused ∈ (∅ : Finset Candidate) :=
        choice.choose_mem hchoose
      simp at hmem

end FractionalSTVChoiceRule

/--
A quota-respecting source choice rule makes the generated focused step an
election whenever some active candidate has reached quota.
-/
theorem fractionalSTVStepFromFocus_kind_elect_of_quotaRespectingChoice
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : FractionalSTVChoiceRule Candidate}
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {active : Finset Candidate} {weight : Voter → ℝ}
    {focused : Candidate}
    (hrespect : choice.QuotaRespecting quota)
    (hchoose :
      choice.choose active (fractionalActiveTally voters ballots weight active) =
        some focused)
    (hexists :
      ∃ candidate, candidate ∈ active ∧
        quota ≤ fractionalActiveTally voters ballots weight active candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).kind =
      StepKind.elect := by
  have hquota :
      quota ≤ fractionalActiveTally voters ballots weight active focused :=
    hrespect hchoose hexists
  simp [fractionalSTVStepFromFocus, hquota]

/--
If no active candidate has reached quota, the generated focused step for an
active candidate is an elimination.
-/
theorem fractionalSTVStepFromFocus_kind_eliminate_of_no_active_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {active : Finset Candidate} {weight : Voter → ℝ}
    {focused : Candidate}
    (hfocused : focused ∈ active)
    (hnoquota :
      ∀ candidate, candidate ∈ active →
        ¬ quota ≤ fractionalActiveTally voters ballots weight active candidate) :
    (fractionalSTVStepFromFocus voters ballots quota active weight focused).kind =
      StepKind.eliminate := by
  have hfocused_noquota :
      ¬ quota ≤ fractionalActiveTally voters ballots weight active focused :=
    hnoquota focused hfocused
  simp [fractionalSTVStepFromFocus, hfocused_noquota]

/--
Executable fractional STV trace fold generated by a deterministic list of
focused candidates. If the next proposed focus is inactive, the run stops; if
it is active, the generated step removes it and the recursive fractional weight
update feeds the next round.
-/
noncomputable def fractionalSTVGeneratedSteps {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    List Candidate → Finset Candidate → (Voter → ℝ) → List (STVStep Candidate)
  | [], _active, _weight => []
  | focused :: rest, active, weight =>
      if focused ∈ active then
        let step :=
          fractionalSTVStepFromFocus voters ballots quota active weight focused
        step ::
          fractionalSTVGeneratedSteps voters ballots quota rest step.afterActive
            (fractionalSTVNextWeight voters ballots quota step weight)
      else
        []

/--
Compute the sequence of focused candidates selected by a deterministic
fractional STV choice rule for at most `rounds` rounds.

The recursion is over an explicit round budget. Each selected active focus is
then replayed by `fractionalSTVGeneratedSteps`, so all source-step facts are
derived from the concrete step generator rather than assumed as a replay
certificate.
-/
noncomputable def fractionalSTVChoiceRunFocuses {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ℕ → Finset Candidate → (Voter → ℝ) → List Candidate
  | 0, _active, _weight => []
  | rounds + 1, active, weight =>
      match choice.choose active
          (fractionalActiveTally voters ballots weight active) with
      | none => []
      | some focused =>
          if focused ∈ active then
            let step :=
              fractionalSTVStepFromFocus voters ballots quota active weight
                focused
            focused ::
            fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
                step.afterActive
                (fractionalSTVNextWeight voters ballots quota step weight)
          else
            []

/--
Compute the focused-candidate sequence for a seat-limited fractional STV run.

The runner stops when the finite round budget is exhausted, when the source
choice rule stops, or when `seatLimit` election rounds have occurred. This is
the reusable multiwinner STV simulator entry point: candidate selection remains
source-specific, while the transfer update and elect/eliminate classification
come from `fractionalSTVStepFromFocus`.
-/
noncomputable def fractionalSTVSeatRunFocuses {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ) :
    ℕ → ℕ → Finset Candidate → (Voter → ℝ) → List Candidate
  | 0, _elected, _active, _weight => []
  | rounds + 1, elected, active, weight =>
      if seatLimit ≤ elected then
        []
      else
        match choice.choose active
            (fractionalActiveTally voters ballots weight active) with
        | none => []
        | some focused =>
            if focused ∈ active then
              let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let nextElected :=
                if step.kind = StepKind.elect then elected + 1 else elected
              focused ::
                fractionalSTVSeatRunFocuses choice voters ballots quota
                  seatLimit rounds nextElected step.afterActive
                  (fractionalSTVNextWeight voters ballots quota step weight)
            else
              []

/--
Compute the focused-candidate sequence for a filled-seat fractional STV run.

This source-level runner follows the same concrete quota-election/elimination
steps as `fractionalSTVSeatRunFocuses`, but it stops the transfer trace as soon
as the currently active candidates fit into the remaining unfilled seats. Those
terminal active candidates are then read as the source rule's final filled
seats; they are not treated as additional quota-transfer rounds.
-/
noncomputable def fractionalSTVFilledSeatRunFocuses
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ) :
    ℕ → ℕ → Finset Candidate → (Voter → ℝ) → List Candidate
  | 0, _elected, _active, _weight => []
  | rounds + 1, elected, active, weight =>
      if seatLimit ≤ elected then
        []
      else if active.card ≤ seatLimit - elected then
        []
      else
        match choice.choose active
            (fractionalActiveTally voters ballots weight active) with
        | none => []
        | some focused =>
            if focused ∈ active then
              let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let nextElected :=
                if step.kind = StepKind.elect then elected + 1 else elected
              focused ::
                fractionalSTVFilledSeatRunFocuses choice voters ballots quota
                  seatLimit rounds nextElected step.afterActive
                  (fractionalSTVNextWeight voters ballots quota step weight)
            else
              []

/--
Compute focused candidates for a fractional STV run stopped by one party's
elected-candidate budget.

This runner is useful for two-party solid-coalition proofs: it follows the
same concrete candidate-level choice and transfer dynamics, but its stopping
counter only increments when an elected focused candidate belongs to the named
party.
-/
noncomputable def fractionalSTVPartySeatRunFocuses {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit : ℕ) :
    ℕ → ℕ → Finset Candidate → (Voter → ℝ) → List Candidate
  | 0, _partyElected, _active, _weight => []
  | rounds + 1, partyElected, active, weight =>
      if partySeatLimit ≤ partyElected then
        []
      else
        match choice.choose active
            (fractionalActiveTally voters ballots weight active) with
        | none => []
        | some focused =>
            if hfocused : focused ∈ active then
              let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let nextPartyElected :=
                if step.kind = StepKind.elect ∧ focused ∈ partyCandidates then
                  partyElected + 1
                else
                  partyElected
              focused ::
                fractionalSTVPartySeatRunFocuses choice voters ballots quota
                  partyCandidates partySeatLimit rounds nextPartyElected
                  step.afterActive
                  (fractionalSTVNextWeight voters ballots quota step weight)
            else
              []

/-- Terminal active set produced by `fractionalSTVGeneratedSteps`. -/
noncomputable def fractionalSTVGeneratedTerminalActive {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    List Candidate → Finset Candidate → (Voter → ℝ) → Finset Candidate
  | [], active, _weight => active
  | focused :: rest, active, weight =>
      if focused ∈ active then
        let step :=
          fractionalSTVStepFromFocus voters ballots quota active weight focused
        fractionalSTVGeneratedTerminalActive voters ballots quota rest step.afterActive
          (fractionalSTVNextWeight voters ballots quota step weight)
      else
        active

/--
The generated trace fold replays its active sets from the initial active set to
its computed terminal active set.
-/
theorem fractionalSTVGeneratedSteps_replayStepsFrom
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (focuses : List Candidate) (active : Finset Candidate)
      (weight : Voter → ℝ),
      STVTrace.replayStepsFrom
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight)
        active
        (fractionalSTVGeneratedTerminalActive voters ballots quota focuses active
          weight) := by
  intro focuses
  induction focuses with
  | nil =>
      intro active weight
      simp [fractionalSTVGeneratedSteps, fractionalSTVGeneratedTerminalActive,
        STVTrace.replayStepsFrom]
  | cons focused rest ih =>
      intro active weight
      by_cases hfocused : focused ∈ active
      · simp [fractionalSTVGeneratedSteps, fractionalSTVGeneratedTerminalActive,
          hfocused, STVTrace.replayStepsFrom]
        exact ih (active.erase focused)
          (fractionalSTVNextWeight voters ballots quota
            (fractionalSTVStepFromFocus voters ballots quota active weight
              focused) weight)
      · simp [fractionalSTVGeneratedSteps, fractionalSTVGeneratedTerminalActive,
          hfocused, STVTrace.replayStepsFrom]

/--
At generated round `i`, the active set has lost exactly `i` candidates from
the initial active set. This makes generated steps index-identifiable even
though the generic `STVStep` type has no explicit round number.
-/
theorem fractionalSTVGeneratedSteps_get_beforeActive_card_add_index
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (focuses : List Candidate) (active : Finset Candidate)
      (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight).length),
      ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).beforeActive.card +
        i.1 = active.card := by
  intro focuses
  induction focuses with
  | nil =>
      intro active weight i
      exact Fin.elim0 i
  | cons focused rest ih =>
      intro active weight i
      by_cases hfocused : focused ∈ active
      · cases i with
        | mk n hn =>
            cases n with
            | zero =>
                simp [fractionalSTVGeneratedSteps, hfocused]
            | succ n =>
                have hn_tail :
                    n <
                      (fractionalSTVGeneratedSteps voters ballots quota rest
                        (active.erase focused)
                        (fractionalSTVNextWeight voters ballots quota
                          (fractionalSTVStepFromFocus voters ballots quota
                            active weight focused) weight)).length := by
                  have hn_succ :
                      n.succ <
                        (fractionalSTVGeneratedSteps voters ballots quota rest
                          (active.erase focused)
                          (fractionalSTVNextWeight voters ballots quota
                            (fractionalSTVStepFromFocus voters ballots quota
                              active weight focused) weight)).length.succ := by
                    simpa [fractionalSTVGeneratedSteps, hfocused] using hn
                  exact Nat.succ_lt_succ_iff.mp hn_succ
                have htail :=
                  ih (active.erase focused)
                    (fractionalSTVNextWeight voters ballots quota
                      (fractionalSTVStepFromFocus voters ballots quota active
                        weight focused) weight)
                    ⟨n, hn_tail⟩
                have htail' :
                    ((fractionalSTVGeneratedSteps voters ballots quota rest
                      (active.erase focused)
                      (fractionalSTVNextWeight voters ballots quota
                        (fractionalSTVStepFromFocus voters ballots quota active
                          weight focused) weight)).get ⟨n, hn_tail⟩).beforeActive.card +
                      n = (active.erase focused).card := by
                  simpa using htail
                have herase :
                    (active.erase focused).card + 1 = active.card :=
                  Finset.card_erase_add_one hfocused
                have htarget :
                    ((fractionalSTVGeneratedSteps voters ballots quota rest
                      (active.erase focused)
                      (fractionalSTVNextWeight voters ballots quota
                        (fractionalSTVStepFromFocus voters ballots quota active
                          weight focused) weight)).get ⟨n, hn_tail⟩).beforeActive.card +
                      (n + 1) = active.card := by
                  omega
                simpa [fractionalSTVGeneratedSteps, hfocused,
                  Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using htarget
      · simp [fractionalSTVGeneratedSteps, hfocused] at i
        exact Fin.elim0 i

/-- Generated trace steps are injective as indexed list entries. -/
theorem fractionalSTVGeneratedSteps_get_injective
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (focuses : List Candidate) (active : Finset Candidate)
    (weight : Voter → ℝ) :
    Function.Injective
      (fun i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight).length =>
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i) := by
  intro i j hsteps
  apply Fin.ext
  have hi :=
    fractionalSTVGeneratedSteps_get_beforeActive_card_add_index
      voters ballots quota focuses active weight i
  have hj :=
    fractionalSTVGeneratedSteps_get_beforeActive_card_add_index
      voters ballots quota focuses active weight j
  have hcard :
      ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).beforeActive.card =
        ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get j).beforeActive.card := by
    exact congrArg (fun step => step.beforeActive.card) hsteps
  omega

/-- Every indexed step of a generated run removes its focused candidate. -/
theorem fractionalSTVGeneratedSteps_get_removesFocusedCandidate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (focuses : List Candidate) (active : Finset Candidate)
      (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight).length),
      ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).removesFocusedCandidate := by
  intro focuses
  induction focuses with
  | nil =>
      intro active weight i
      exact Fin.elim0 i
  | cons focused rest ih =>
      intro active weight i
      by_cases hfocused : focused ∈ active
      · cases i with
        | mk n hn =>
            cases n with
            | zero =>
                simpa [fractionalSTVGeneratedSteps, hfocused] using
                  fractionalSTVStepFromFocus_removesFocusedCandidate
                    voters ballots quota active weight focused
            | succ n =>
                have hn_tail :
                    n <
                      (fractionalSTVGeneratedSteps voters ballots quota rest
                        (active.erase focused)
                        (fractionalSTVNextWeight voters ballots quota
                          (fractionalSTVStepFromFocus voters ballots quota
                            active weight focused) weight)).length := by
                  have hn_succ :
                      n.succ <
                        (fractionalSTVGeneratedSteps voters ballots quota rest
                          (active.erase focused)
                          (fractionalSTVNextWeight voters ballots quota
                            (fractionalSTVStepFromFocus voters ballots quota
                              active weight focused) weight)).length.succ := by
                    simpa [fractionalSTVGeneratedSteps, hfocused] using hn
                  exact Nat.succ_lt_succ_iff.mp hn_succ
                simpa [fractionalSTVGeneratedSteps, hfocused] using
                  ih (active.erase focused)
                    (fractionalSTVNextWeight voters ballots quota
                      (fractionalSTVStepFromFocus voters ballots quota active
                        weight focused) weight)
                    ⟨n, hn_tail⟩
      · simp [fractionalSTVGeneratedSteps, hfocused] at i
        exact Fin.elim0 i

/-- Every indexed step of a generated run has an active focused candidate. -/
theorem fractionalSTVGeneratedSteps_get_focus_active
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (focuses : List Candidate) (active : Finset Candidate)
      (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight).length),
      ∃ focused,
        ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).focus =
          some focused ∧
          focused ∈
            ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).beforeActive := by
  intro focuses
  induction focuses with
  | nil =>
      intro active weight i
      exact Fin.elim0 i
  | cons focused rest ih =>
      intro active weight i
      by_cases hfocused : focused ∈ active
      · cases i with
        | mk n hn =>
            cases n with
            | zero =>
                simpa [fractionalSTVGeneratedSteps, hfocused] using
                  fractionalSTVStepFromFocus_focus_active
                    voters ballots quota active weight hfocused
            | succ n =>
                have hn_tail :
                    n <
                      (fractionalSTVGeneratedSteps voters ballots quota rest
                        (active.erase focused)
                        (fractionalSTVNextWeight voters ballots quota
                          (fractionalSTVStepFromFocus voters ballots quota
                            active weight focused) weight)).length := by
                  have hn_succ :
                      n.succ <
                        (fractionalSTVGeneratedSteps voters ballots quota rest
                          (active.erase focused)
                          (fractionalSTVNextWeight voters ballots quota
                            (fractionalSTVStepFromFocus voters ballots quota
                              active weight focused) weight)).length.succ := by
                    simpa [fractionalSTVGeneratedSteps, hfocused] using hn
                  exact Nat.succ_lt_succ_iff.mp hn_succ
                simpa [fractionalSTVGeneratedSteps, hfocused] using
                  ih (active.erase focused)
                    (fractionalSTVNextWeight voters ballots quota
                      (fractionalSTVStepFromFocus voters ballots quota active
                        weight focused) weight)
                    ⟨n, hn_tail⟩
      · simp [fractionalSTVGeneratedSteps, hfocused] at i
        exact Fin.elim0 i

/-- Every indexed step of a generated run is an election or elimination. -/
theorem fractionalSTVGeneratedSteps_get_kind_allowed
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (focuses : List Candidate) (active : Finset Candidate)
      (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota focuses active weight).length),
      ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).kind =
          StepKind.elect ∨
        ((fractionalSTVGeneratedSteps voters ballots quota focuses active weight).get i).kind =
          StepKind.eliminate := by
  intro focuses
  induction focuses with
  | nil =>
      intro active weight i
      exact Fin.elim0 i
  | cons focused rest ih =>
      intro active weight i
      by_cases hfocused : focused ∈ active
      · cases i with
        | mk n hn =>
            cases n with
            | zero =>
                simpa [fractionalSTVGeneratedSteps, hfocused] using
                  fractionalSTVStepFromFocus_kind_allowed
                    voters ballots quota active weight focused
            | succ n =>
                have hn_tail :
                    n <
                      (fractionalSTVGeneratedSteps voters ballots quota rest
                        (active.erase focused)
                        (fractionalSTVNextWeight voters ballots quota
                          (fractionalSTVStepFromFocus voters ballots quota
                            active weight focused) weight)).length := by
                  have hn_succ :
                      n.succ <
                        (fractionalSTVGeneratedSteps voters ballots quota rest
                          (active.erase focused)
                          (fractionalSTVNextWeight voters ballots quota
                            (fractionalSTVStepFromFocus voters ballots quota
                              active weight focused) weight)).length.succ := by
                    simpa [fractionalSTVGeneratedSteps, hfocused] using hn
                  exact Nat.succ_lt_succ_iff.mp hn_succ
                simpa [fractionalSTVGeneratedSteps, hfocused] using
                  ih (active.erase focused)
                    (fractionalSTVNextWeight voters ballots quota
                      (fractionalSTVStepFromFocus voters ballots quota active
                        weight focused) weight)
                    ⟨n, hn_tail⟩
      · simp [fractionalSTVGeneratedSteps, hfocused] at i
        exact Fin.elim0 i

/--
For every indexed generated step, an election label certifies that the current
prefix weight gives the focused candidate at least quota.
-/
theorem fractionalSTVGeneratedSteps_get_quota_if_elect
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (focuses : List Candidate) (active : Finset Candidate)
      (initialWeight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota focuses active
          initialWeight).length)
      (focused : Candidate),
      ((fractionalSTVGeneratedSteps voters ballots quota focuses active
        initialWeight).get i).focus = some focused →
      ((fractionalSTVGeneratedSteps voters ballots quota focuses active
        initialWeight).get i).kind = StepKind.elect →
        quota ≤
          fractionalActiveTally voters ballots
            (fractionalSTVWeightAfterSteps voters ballots quota
              ((fractionalSTVGeneratedSteps voters ballots quota focuses active
                initialWeight).take i.1) initialWeight)
            ((fractionalSTVGeneratedSteps voters ballots quota focuses active
              initialWeight).get i).beforeActive focused := by
  intro focuses
  induction focuses with
  | nil =>
      intro active initialWeight i focused hfocus helect
      exact Fin.elim0 i
  | cons first rest ih =>
      intro active initialWeight i focused hfocus helect
      by_cases hfirst : first ∈ active
      · cases i with
        | mk n hn =>
            cases n with
            | zero =>
                simpa [fractionalSTVGeneratedSteps, hfirst,
                  fractionalSTVWeightAfterSteps] using
                  fractionalSTVStepFromFocus_quota_if_elect
                    (voters := voters) (ballots := ballots) (quota := quota)
                    (active := active) (weight := initialWeight)
                    (focused := first) (selected := focused)
                    (by simpa [fractionalSTVGeneratedSteps, hfirst]
                      using hfocus)
                    (by simpa [fractionalSTVGeneratedSteps, hfirst]
                      using helect)
            | succ n =>
                have hn_tail :
                    n <
                      (fractionalSTVGeneratedSteps voters ballots quota rest
                        (active.erase first)
                        (fractionalSTVNextWeight voters ballots quota
                          (fractionalSTVStepFromFocus voters ballots quota
                            active initialWeight first)
                          initialWeight)).length := by
                  have hn_succ :
                      n.succ <
                        (fractionalSTVGeneratedSteps voters ballots quota rest
                          (active.erase first)
                          (fractionalSTVNextWeight voters ballots quota
                            (fractionalSTVStepFromFocus voters ballots quota
                              active initialWeight first)
                            initialWeight)).length.succ := by
                    simpa [fractionalSTVGeneratedSteps, hfirst] using hn
                  exact Nat.succ_lt_succ_iff.mp hn_succ
                have htail :=
                  ih (active.erase first)
                    (fractionalSTVNextWeight voters ballots quota
                      (fractionalSTVStepFromFocus voters ballots quota active
                        initialWeight first)
                      initialWeight) ⟨n, hn_tail⟩ focused
                    (by simpa [fractionalSTVGeneratedSteps, hfirst]
                      using hfocus)
                    (by simpa [fractionalSTVGeneratedSteps, hfirst]
                      using helect)
                simpa [fractionalSTVGeneratedSteps, hfirst,
                  fractionalSTVWeightAfterSteps, Nat.succ_eq_add_one] using htail
      · simp [fractionalSTVGeneratedSteps, hfirst] at i
        exact Fin.elim0 i

/--
The executable fractional STV weight fold preserves nonnegativity when each
election round elects a candidate with at least one positive quota of current
weight.
-/
theorem fractionalSTVWeightAfterSteps_nonneg {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {steps : List (STVStep Candidate)}
    {initialWeight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota)
    (hquota_if_elect :
      ∀ i : Fin steps.length, ∀ focused,
        (steps.get i).focus = some focused →
          (steps.get i).kind = StepKind.elect →
            quota ≤
              fractionalActiveTally voters ballots
                (fractionalSTVWeightAfterSteps voters ballots quota
                  (steps.take i.1) initialWeight)
                (steps.get i).beforeActive focused) :
    ∀ voter, voter ∈ voters →
      0 ≤
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter := by
  induction steps generalizing initialWeight with
  | nil =>
      simpa [fractionalSTVWeightAfterSteps] using hweight_nonneg
  | cons step steps ih =>
      dsimp [fractionalSTVWeightAfterSteps]
      apply ih
      · exact
          fractionalSTVNextWeight_nonneg
            (voters := voters) (ballots := ballots) (quota := quota)
            (step := step) (weight := initialWeight)
            hweight_nonneg hquota_pos (by
              intro focused hfocus hkind
              have h0 :=
                hquota_if_elect ⟨0, by simp⟩ focused hfocus hkind
              simpa [fractionalSTVWeightAfterSteps] using h0)
      · intro i focused hfocus hkind
        have hsucc :=
          hquota_if_elect
            ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
            focused hfocus hkind
        simpa [fractionalSTVWeightAfterSteps, Nat.succ_eq_add_one]
          using hsucc

/--
Prefix form of `fractionalSTVWeightAfterSteps_nonneg`: every executable
fractional STV weight prefix preserves nonnegativity under the same
quota-satisfying election condition.
-/
theorem fractionalSTVWeightAfterSteps_take_nonneg {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {steps : List (STVStep Candidate)}
    {initialWeight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota)
    (hquota_if_elect :
      ∀ i : Fin steps.length, ∀ focused,
        (steps.get i).focus = some focused →
          (steps.get i).kind = StepKind.elect →
            quota ≤
              fractionalActiveTally voters ballots
                (fractionalSTVWeightAfterSteps voters ballots quota
                  (steps.take i.1) initialWeight)
                (steps.get i).beforeActive focused)
    (n : ℕ) :
    ∀ voter, voter ∈ voters →
      0 ≤
        fractionalSTVWeightAfterSteps voters ballots quota (steps.take n)
          initialWeight voter := by
  induction steps generalizing initialWeight n with
  | nil =>
      intro voter hvoter
      simpa [fractionalSTVWeightAfterSteps] using hweight_nonneg voter hvoter
  | cons step steps ih =>
      cases n with
      | zero =>
          intro voter hvoter
          simpa [fractionalSTVWeightAfterSteps] using
            hweight_nonneg voter hvoter
      | succ n =>
          dsimp [fractionalSTVWeightAfterSteps]
          apply ih
          · exact
              fractionalSTVNextWeight_nonneg
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := initialWeight)
                hweight_nonneg hquota_pos (by
                  intro focused hfocus hkind
                  have h0 :=
                    hquota_if_elect ⟨0, by simp⟩ focused hfocus hkind
                  simpa [fractionalSTVWeightAfterSteps] using h0)
          · intro i focused hfocus hkind
            have hsucc :=
              hquota_if_elect
                ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
                focused hfocus hkind
            simpa [fractionalSTVWeightAfterSteps, Nat.succ_eq_add_one]
              using hsucc

/--
Indexed executable fractional STV trace certificate.

This is the simulator-facing version of `FractionalSTVExecutableTrace`: the
real-valued tally is indexed by the generated round, so it can be computed from
the recursive transfer state before being projected to any step-keyed transfer
rule abstraction.
-/
structure FractionalSTVIndexedExecutableTrace {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (trace : STVTrace Candidate) (voters : Finset Voter)
    (ballots : Voter → Ballot Candidate) (quota : ℝ)
    (initialActive terminalActive : Finset Candidate)
    (initialWeight : Voter → ℝ) where
  roundTally : Fin trace.steps.length → Candidate → ℝ
  quota_pos : 0 < quota
  step_removes :
    ∀ i : Fin trace.steps.length,
      (trace.steps.get i).removesFocusedCandidate
  step_focus_active :
    ∀ i : Fin trace.steps.length,
      ∃ focused, (trace.steps.get i).focus = some focused ∧
        focused ∈ (trace.steps.get i).beforeActive
  initialWeight_nonneg :
    ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter
  tally_eq :
    ∀ i : Fin trace.steps.length, ∀ candidate,
      candidate ∈ (trace.steps.get i).beforeActive →
        roundTally i candidate =
          fractionalActiveTally voters ballots
            (fractionalSTVWeightAfterSteps voters ballots quota
              (trace.steps.take i.1) initialWeight)
            (trace.steps.get i).beforeActive candidate
  kind_allowed :
    ∀ i : Fin trace.steps.length,
      (trace.steps.get i).kind = StepKind.elect ∨
        (trace.steps.get i).kind = StepKind.eliminate
  quota_if_elect :
    ∀ i : Fin trace.steps.length, ∀ focused,
      (trace.steps.get i).focus = some focused →
        (trace.steps.get i).kind = StepKind.elect →
          quota ≤
            fractionalActiveTally voters ballots
              (fractionalSTVWeightAfterSteps voters ballots quota
                (trace.steps.take i.1) initialWeight)
              (trace.steps.get i).beforeActive focused
  activeReplay : trace.replaysFrom initialActive terminalActive

/--
A replay in which every step removes an active focused candidate removes
exactly one candidate per step.
-/
theorem STVTrace.terminalActive_card_add_steps_length_eq_startActive_card_of_replayStepsFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hremove : ∀ step, step ∈ steps → step.removesFocusedCandidate)
    (hfocus_active : ∀ step, step ∈ steps →
      ∃ focused, step.focus = some focused ∧ focused ∈ step.beforeActive) :
    terminalActive.card + steps.length = startActive.card := by
  induction steps generalizing startActive with
  | nil =>
      simp only [replayStepsFrom] at hreplay
      simpa [hreplay]
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      rcases hfocus_active step (by simp) with ⟨focused, hfocus, hactive⟩
      rcases hremove step (by simp) with ⟨removed, hremoved, hafter⟩
      have hremoved_eq : removed = focused :=
        Option.some.inj (hremoved.symm.trans hfocus)
      subst removed
      have hstep_card : step.afterActive.card + 1 = step.beforeActive.card := by
        rw [hafter]
        exact Finset.card_erase_add_one hactive
      have hrest_card :
          terminalActive.card + rest.length = step.afterActive.card :=
        ih hrest
          (fun step' hstep' => hremove step' (by simp [hstep']))
          (fun step' hstep' => hfocus_active step' (by simp [hstep']))
      have hbefore_card : step.beforeActive.card = startActive.card :=
        congrArg Finset.card hbefore
      calc
        terminalActive.card + (step :: rest).length =
            (terminalActive.card + rest.length) + 1 := by
              simp [Nat.add_assoc]
        _ = step.afterActive.card + 1 := by rw [hrest_card]
        _ = step.beforeActive.card := hstep_card
        _ = startActive.card := hbefore_card

/--
An indexed executable fractional-STV trace has one active-candidate removal
per recorded step, so its terminal and initial active-set cardinalities differ
by exactly its trace length.
-/
theorem FractionalSTVIndexedExecutableTrace.terminalActive_card_add_steps_length_eq_initialActive_card
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    (run : FractionalSTVIndexedExecutableTrace trace voters ballots quota
      initialActive terminalActive initialWeight) :
    terminalActive.card + trace.steps.length = initialActive.card := by
  apply
    STVTrace.terminalActive_card_add_steps_length_eq_startActive_card_of_replayStepsFrom_removesFocusedCandidate
      run.activeReplay
  · intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact run.step_removes ⟨n, hn⟩
  · intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact run.step_focus_active ⟨n, hn⟩

/--
If each trace step is an election or elimination, then every step contributes
one round-outcome label.
-/
theorem STVTrace.roundOutcomeSequence_length_eq_steps_length_of_kind_allowed
    {Candidate : Type*} (steps : List (STVStep Candidate))
    (hkind : ∀ i : Fin steps.length,
      (steps.get i).kind = StepKind.elect ∨
        (steps.get i).kind = StepKind.eliminate) :
    (({ steps := steps } : STVTrace Candidate).roundOutcomeSequence).length =
      steps.length := by
  induction steps with
  | nil =>
      simp [roundOutcomeSequence]
  | cons step rest ih =>
      have hhead : step.kind = StepKind.elect ∨
          step.kind = StepKind.eliminate := by
        simpa using hkind ⟨0, by simp⟩
      have htail : ∀ i : Fin rest.length,
          (rest.get i).kind = StepKind.elect ∨
            (rest.get i).kind = StepKind.eliminate := by
        intro i
        simpa using hkind
          ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
      have htail_length := ih htail
      cases hhead with
      | inl helect =>
          have hround : STVStep.roundOutcome? step = some RoundOutcome.win := by
            simp [STVStep.roundOutcome?, helect]
          have htail_length' :
              (rest.filterMap STVStep.roundOutcome?).length = rest.length := by
            simpa [STVTrace.roundOutcomeSequence] using htail_length
          calc
            (({ steps := step :: rest } : STVTrace Candidate).roundOutcomeSequence).length =
                (RoundOutcome.win :: rest.filterMap STVStep.roundOutcome?).length := by
                  simp only [STVTrace.roundOutcomeSequence]
                  rw [List.filterMap_cons_some hround]
            _ = (rest.filterMap STVStep.roundOutcome?).length + 1 := by simp
            _ = rest.length + 1 := by rw [htail_length']
            _ = (step :: rest).length := by simp
      | inr heliminate =>
          have hround : STVStep.roundOutcome? step = some RoundOutcome.lose := by
            simp [STVStep.roundOutcome?, heliminate]
          have htail_length' :
              (rest.filterMap STVStep.roundOutcome?).length = rest.length := by
            simpa [STVTrace.roundOutcomeSequence] using htail_length
          calc
            (({ steps := step :: rest } : STVTrace Candidate).roundOutcomeSequence).length =
                (RoundOutcome.lose :: rest.filterMap STVStep.roundOutcome?).length := by
                  simp only [STVTrace.roundOutcomeSequence]
                  rw [List.filterMap_cons_some hround]
            _ = (rest.filterMap STVStep.roundOutcome?).length + 1 := by simp
            _ = rest.length + 1 := by rw [htail_length']
            _ = (step :: rest).length := by simp

/-- Candidate-level trace generated by the executable fractional STV simulator. -/
noncomputable def fractionalSTVGeneratedTrace {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (focuses : List Candidate) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : STVTrace Candidate where
  steps :=
    fractionalSTVGeneratedSteps voters ballots quota focuses initialActive
      initialWeight

/--
Candidate-level trace produced by running a deterministic fractional STV choice
rule for at most `rounds` rounds.
-/
noncomputable def fractionalSTVChoiceRunTrace {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : STVTrace Candidate :=
  fractionalSTVGeneratedTrace voters ballots quota
    (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
      initialActive initialWeight)
    initialActive initialWeight

/--
Candidate-level trace produced by running the seat-limited fractional STV
simulator.
-/
noncomputable def fractionalSTVSeatRunTrace {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : STVTrace Candidate :=
  fractionalSTVGeneratedTrace voters ballots quota
    (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit rounds
      initialElected initialActive initialWeight)
    initialActive initialWeight

/--
Candidate-level trace produced by the filled-seat fractional STV simulator.

The trace contains only concrete quota-election/elimination transfer rounds.
Terminal active candidates are interpreted separately as the source rule's
remaining filled seats.
-/
noncomputable def fractionalSTVFilledSeatRunTrace
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : STVTrace Candidate :=
  fractionalSTVGeneratedTrace voters ballots quota
    (fractionalSTVFilledSeatRunFocuses choice voters ballots quota seatLimit
      rounds initialElected initialActive initialWeight)
    initialActive initialWeight

/--
Candidate-level trace produced by running the party-seat-limited fractional STV
simulator.
-/
noncomputable def fractionalSTVPartySeatRunTrace
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit rounds initialPartyElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : STVTrace Candidate :=
  fractionalSTVGeneratedTrace voters ballots quota
    (fractionalSTVPartySeatRunFocuses choice voters ballots quota
      partyCandidates partySeatLimit rounds initialPartyElected initialActive
      initialWeight)
    initialActive initialWeight

/--
Terminal active set produced by running a deterministic fractional STV choice
rule for at most `rounds` rounds.
-/
noncomputable def fractionalSTVChoiceRunTerminalActive
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : Finset Candidate :=
  fractionalSTVGeneratedTerminalActive voters ballots quota
    (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
      initialActive initialWeight)
    initialActive initialWeight

/--
Terminal active set produced by running the seat-limited fractional STV
simulator.
-/
noncomputable def fractionalSTVSeatRunTerminalActive
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : Finset Candidate :=
  fractionalSTVGeneratedTerminalActive voters ballots quota
    (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit rounds
      initialElected initialActive initialWeight)
    initialActive initialWeight

/--
Terminal active set produced by the filled-seat fractional STV simulator.
These are precisely the candidates available for the final source-level fill
when the trace stops before the seat limit is reached.
-/
noncomputable def fractionalSTVFilledSeatRunTerminalActive
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : Finset Candidate :=
  fractionalSTVGeneratedTerminalActive voters ballots quota
    (fractionalSTVFilledSeatRunFocuses choice voters ballots quota seatLimit
      rounds initialElected initialActive initialWeight)
    initialActive initialWeight

/--
Terminal active set produced by running the party-seat-limited fractional STV
simulator.
-/
noncomputable def fractionalSTVPartySeatRunTerminalActive
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit rounds initialPartyElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) : Finset Candidate :=
  fractionalSTVGeneratedTerminalActive voters ballots quota
    (fractionalSTVPartySeatRunFocuses choice voters ballots quota
      partyCandidates partySeatLimit rounds initialPartyElected initialActive
      initialWeight)
    initialActive initialWeight

/--
If a deterministic choice rule selects some active candidate whenever any
candidate remains active, then a run with at least as many rounds as initially
active candidates exhausts the active set.
-/
theorem fractionalSTVChoiceRunTerminalActive_eq_empty_of_total
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ)
    (htotal : choice.Total) :
    ∀ (rounds : ℕ) (active : Finset Candidate) (weight : Voter → ℝ),
      active.card ≤ rounds →
        fractionalSTVChoiceRunTerminalActive choice voters ballots quota
          rounds active weight = ∅ := by
  intro rounds
  induction rounds with
  | zero =>
      intro active weight hrounds
      have hcard : active.card = 0 := Nat.eq_zero_of_le_zero hrounds
      have hactive : active = ∅ := Finset.card_eq_zero.mp hcard
      subst active
      simp [fractionalSTVChoiceRunTerminalActive,
        fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedTerminalActive]
  | succ rounds ih =>
      intro active weight hrounds
      by_cases hactive_empty : active = ∅
      · subst active
        have hchoose :
            choice.choose (∅ : Finset Candidate)
              (fractionalActiveTally voters ballots weight ∅) = none :=
          FractionalSTVChoiceRule.choose_eq_none_of_empty choice
            (fractionalActiveTally voters ballots weight ∅)
        simp [fractionalSTVChoiceRunTerminalActive,
          fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedTerminalActive,
          hchoose]
      · have hactive_nonempty : active.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hactive_empty
        rcases htotal hactive_nonempty with ⟨focused, hchoose⟩
        have hfocused : focused ∈ active := choice.choose_mem hchoose
        let step :=
          fractionalSTVStepFromFocus voters ballots quota active weight focused
        have hcard_erase : (active.erase focused).card ≤ rounds := by
          have hcard_eq :
              (active.erase focused).card + 1 = active.card :=
            Finset.card_erase_add_one hfocused
          omega
        have hih :
            fractionalSTVChoiceRunTerminalActive choice voters ballots quota
              rounds step.afterActive
              (fractionalSTVNextWeight voters ballots quota step weight) = ∅ := by
          simpa [step] using
            ih (active.erase focused)
              (fractionalSTVNextWeight voters ballots quota step weight)
              hcard_erase
        change
          fractionalSTVGeneratedTerminalActive voters ballots quota
            (fractionalSTVChoiceRunFocuses choice voters ballots quota
              (rounds + 1) active weight)
            active weight = ∅
        rw [fractionalSTVChoiceRunFocuses, hchoose]
        simp only [hfocused, if_true]
        simpa [fractionalSTVChoiceRunTerminalActive,
          fractionalSTVGeneratedTerminalActive, hfocused, step] using hih

/--
Every generated round of a deterministic fractional-STV choice run uses the
choice rule on that round's concrete active set and fractional tally.  The
tally is computed from the actual prefix of transfer updates, rather than from
an externally supplied round certificate.
-/
theorem fractionalSTVChoiceRun_get_choose_eq_focus
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (rounds : ℕ) (active : Finset Candidate) (initialWeight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota
          (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
            active initialWeight) active initialWeight).length),
      choice.choose
          ((fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
              active initialWeight) active initialWeight).get i).beforeActive
          (fractionalActiveTally voters ballots
            (fractionalSTVWeightAfterSteps voters ballots quota
              ((fractionalSTVGeneratedSteps voters ballots quota
                (fractionalSTVChoiceRunFocuses choice voters ballots quota
                  rounds active initialWeight) active initialWeight).take i.1)
              initialWeight)
            ((fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
                active initialWeight) active initialWeight).get i).beforeActive) =
        ((fractionalSTVGeneratedSteps voters ballots quota
          (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
            active initialWeight) active initialWeight).get i).focus := by
  intro rounds
  induction rounds with
  | zero =>
      intro active initialWeight i
      simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps] at i
      exact Fin.elim0 i
  | succ rounds ih =>
      intro active initialWeight i
      cases hchoose :
          choice.choose active
            (fractionalActiveTally voters ballots initialWeight active) with
      | none =>
          simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps,
            hchoose] at i
          exact Fin.elim0 i
      | some focused =>
          have hfocused : focused ∈ active := choice.choose_mem hchoose
          let step :=
            fractionalSTVStepFromFocus voters ballots quota active initialWeight
              focused
          cases i with
          | mk n hn =>
              cases n with
              | zero =>
                  simpa [fractionalSTVChoiceRunFocuses,
                    fractionalSTVGeneratedSteps, fractionalSTVWeightAfterSteps,
                    hchoose, hfocused, step] using hchoose
              | succ n =>
                  have hn_tail :
                      n <
                        (fractionalSTVGeneratedSteps voters ballots quota
                          (fractionalSTVChoiceRunFocuses choice voters ballots
                            quota rounds step.afterActive
                            (fractionalSTVNextWeight voters ballots quota step
                              initialWeight))
                          step.afterActive
                          (fractionalSTVNextWeight voters ballots quota step
                            initialWeight)).length := by
                    have hn_succ :
                        n.succ <
                          (fractionalSTVGeneratedSteps voters ballots quota
                            (fractionalSTVChoiceRunFocuses choice voters ballots
                              quota rounds step.afterActive
                              (fractionalSTVNextWeight voters ballots quota step
                                initialWeight))
                            step.afterActive
                            (fractionalSTVNextWeight voters ballots quota step
                              initialWeight)).length.succ := by
                      simpa [fractionalSTVChoiceRunFocuses,
                        fractionalSTVGeneratedSteps, hchoose, hfocused, step]
                        using hn
                    exact Nat.succ_lt_succ_iff.mp hn_succ
                  have htail :=
                    ih step.afterActive
                      (fractionalSTVNextWeight voters ballots quota step
                        initialWeight)
                      ⟨n, hn_tail⟩
                  simpa [fractionalSTVChoiceRunFocuses,
                    fractionalSTVGeneratedSteps, fractionalSTVWeightAfterSteps,
                    hchoose, hfocused, step] using htail

/--
Trace-facing form of `fractionalSTVChoiceRun_get_choose_eq_focus`: every
indexed step focus is exactly the result of the choice rule applied to its
actual fractional-STV round state.
-/
theorem fractionalSTVChoiceRunTrace_get_focus_eq_choose
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (i : Fin
      (fractionalSTVChoiceRunTrace choice voters ballots quota rounds
        initialActive initialWeight).steps.length) :
    ((fractionalSTVChoiceRunTrace choice voters ballots quota rounds
      initialActive initialWeight).steps.get i).focus =
      choice.choose
        ((fractionalSTVChoiceRunTrace choice voters ballots quota rounds
          initialActive initialWeight).steps.get i).beforeActive
        (fractionalActiveTally voters ballots
          (fractionalSTVWeightAfterSteps voters ballots quota
            ((fractionalSTVChoiceRunTrace choice voters ballots quota rounds
              initialActive initialWeight).steps.take i.1) initialWeight)
          ((fractionalSTVChoiceRunTrace choice voters ballots quota rounds
            initialActive initialWeight).steps.get i).beforeActive) := by
  simpa [fractionalSTVChoiceRunTrace, fractionalSTVGeneratedTrace] using
    (fractionalSTVChoiceRun_get_choose_eq_focus choice voters ballots quota
      rounds initialActive initialWeight i).symm

/--
Every focus emitted by a deterministic choice run produces one concrete STV
step: a returned candidate is active by `choose_mem`, so the generated-step
fold cannot truncate that focus sequence.
-/
theorem fractionalSTVChoiceRun_generatedSteps_length_eq_focuses_length
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) :
    ∀ (rounds : ℕ) (active : Finset Candidate) (initialWeight : Voter → ℝ),
      (fractionalSTVGeneratedSteps voters ballots quota
        (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
          active initialWeight) active initialWeight).length =
        (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
          active initialWeight).length := by
  intro rounds
  induction rounds with
  | zero =>
      intro active initialWeight
      simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps]
  | succ rounds ih =>
      intro active initialWeight
      cases hchoose :
          choice.choose active
            (fractionalActiveTally voters ballots initialWeight active) with
      | none =>
          simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps,
            hchoose]
      | some focused =>
          have hfocused : focused ∈ active := choice.choose_mem hchoose
          let step :=
            fractionalSTVStepFromFocus voters ballots quota active initialWeight
              focused
          have htail :=
            ih step.afterActive
              (fractionalSTVNextWeight voters ballots quota step initialWeight)
          simpa [fractionalSTVChoiceRunFocuses,
            fractionalSTVGeneratedSteps, hchoose, hfocused, step] using
            congrArg Nat.succ htail

/--
Trace-facing form of `fractionalSTVChoiceRun_generatedSteps_length_eq_focuses_length`.
-/
theorem fractionalSTVChoiceRunTrace_steps_length_eq_focuses_length
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) :
    (fractionalSTVChoiceRunTrace choice voters ballots quota rounds
      initialActive initialWeight).steps.length =
      (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
        initialActive initialWeight).length := by
  simpa [fractionalSTVChoiceRunTrace, fractionalSTVGeneratedTrace] using
    fractionalSTVChoiceRun_generatedSteps_length_eq_focuses_length choice
      voters ballots quota rounds initialActive initialWeight

/--
Every deterministic choice-run step is an election or elimination, so the
trace's round-outcome sequence has one entry for each emitted focus.
-/
theorem fractionalSTVChoiceRunTrace_roundOutcomeSequence_length_eq_focuses_length
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) :
    (fractionalSTVChoiceRunTrace choice voters ballots quota rounds
      initialActive initialWeight).roundOutcomeSequence.length =
      (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
        initialActive initialWeight).length := by
  calc
    (fractionalSTVChoiceRunTrace choice voters ballots quota rounds
      initialActive initialWeight).roundOutcomeSequence.length =
        (fractionalSTVChoiceRunTrace choice voters ballots quota rounds
          initialActive initialWeight).steps.length := by
      apply STVTrace.roundOutcomeSequence_length_eq_steps_length_of_kind_allowed
      simpa [fractionalSTVChoiceRunTrace, fractionalSTVGeneratedTrace] using
        fractionalSTVGeneratedSteps_get_kind_allowed voters ballots quota
          (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
            initialActive initialWeight) initialActive initialWeight
    _ = (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
          initialActive initialWeight).length :=
      fractionalSTVChoiceRunTrace_steps_length_eq_focuses_length choice voters
        ballots quota rounds initialActive initialWeight

/--
Round-indexed real-valued tally generated by the executable fractional STV
simulator.
-/
noncomputable def fractionalSTVGeneratedRoundTally {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (focuses : List Candidate) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (i : Fin
      (fractionalSTVGeneratedSteps voters ballots quota focuses initialActive
        initialWeight).length)
    (candidate : Candidate) : ℝ :=
  fractionalActiveTally voters ballots
    (fractionalSTVWeightAfterSteps voters ballots quota
      ((fractionalSTVGeneratedSteps voters ballots quota focuses initialActive
        initialWeight).take i.1) initialWeight)
    ((fractionalSTVGeneratedSteps voters ballots quota focuses initialActive
      initialWeight).get i).beforeActive candidate

/--
Step-keyed transfer rule induced by a generated fractional STV trace.

The rule recovers the generated round index from the concrete `STVStep`. The
generated trace has injective indexed steps, so this step-keyed rule agrees
with the simulator's round tally on every generated step.
-/
noncomputable def fractionalSTVGeneratedTransferRule
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (focuses : List Candidate)
    (initialActive : Finset Candidate) (initialWeight : Voter → ℝ) :
    FractionalSTVTransferRule Candidate := by
  classical
  exact
    { fractionalTally := fun step candidate =>
        if h :
            ∃ i : Fin
              (fractionalSTVGeneratedSteps voters ballots quota focuses
                initialActive initialWeight).length,
              (fractionalSTVGeneratedSteps voters ballots quota focuses
                initialActive initialWeight).get i = step then
          fractionalSTVGeneratedRoundTally voters ballots quota focuses
            initialActive initialWeight (Classical.choose h) candidate
        else
          0 }

/--
The generated transfer rule agrees with the simulator's round tally at each
generated step.
-/
theorem fractionalSTVGeneratedTransferRule_tally_eq
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (focuses : List Candidate)
    (initialActive : Finset Candidate) (initialWeight : Voter → ℝ)
    (i : Fin
      (fractionalSTVGeneratedSteps voters ballots quota focuses initialActive
        initialWeight).length)
    (candidate : Candidate) :
    (fractionalSTVGeneratedTransferRule voters ballots quota focuses
      initialActive initialWeight).fractionalTally
        ((fractionalSTVGeneratedSteps voters ballots quota focuses
          initialActive initialWeight).get i) candidate =
      fractionalSTVGeneratedRoundTally voters ballots quota focuses
      initialActive initialWeight i candidate := by
  classical
  let steps :=
    fractionalSTVGeneratedSteps voters ballots quota focuses initialActive
      initialWeight
  have hex : ∃ j : Fin steps.length, steps.get j = steps.get i := ⟨i, rfl⟩
  have hchoose :
      steps.get (Classical.choose hex) = steps.get i :=
    Classical.choose_spec hex
  have hidx : Classical.choose hex = i :=
    fractionalSTVGeneratedSteps_get_injective voters ballots quota focuses
      initialActive initialWeight hchoose
  simp [fractionalSTVGeneratedTransferRule, fractionalSTVGeneratedRoundTally,
    steps, hidx]

/--
For a quota-respecting choice-run simulator, any generated elimination round
certifies that no active candidate has reached quota at that round.
-/
theorem fractionalSTVChoiceRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ (rounds : ℕ) (active : Finset Candidate) (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota
          (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
            active weight) active weight).length)
      (candidate : Candidate),
        candidate ∈
            ((fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
                active weight) active weight).get i).beforeActive →
          ((fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
              active weight) active weight).get i).kind =
              StepKind.eliminate →
            fractionalSTVGeneratedRoundTally voters ballots quota
              (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
                active weight) active weight i candidate < quota := by
  intro rounds
  induction rounds with
  | zero =>
      intro active weight i
      simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps] at i
      exact Fin.elim0 i
  | succ rounds ih =>
      intro active weight i candidate hcandidate heliminate
      cases hchoose :
          choice.choose active
            (fractionalActiveTally voters ballots weight active) with
      | none =>
          simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps,
            hchoose] at i
          exact Fin.elim0 i
      | some focused =>
          by_cases hfocused : focused ∈ active
          · cases i with
            | mk n hn =>
                cases n with
                | zero =>
                    have hcandidate_active : candidate ∈ active := by
                      simpa [fractionalSTVChoiceRunFocuses,
                        fractionalSTVGeneratedSteps, hchoose, hfocused] using
                        hcandidate
                    by_contra hnot_lt
                    have hnot_lt_active :
                        ¬ fractionalActiveTally voters ballots weight active
                            candidate < quota := by
                      intro hlt
                      exact hnot_lt (by
                        simpa [fractionalSTVGeneratedRoundTally,
                          fractionalSTVChoiceRunFocuses,
                          fractionalSTVGeneratedSteps, hchoose, hfocused]
                          using hlt)
                    have hquota :
                        quota ≤
                          fractionalActiveTally voters ballots weight active
                            candidate :=
                      not_lt.mp hnot_lt_active
                    have helect :
                        (fractionalSTVStepFromFocus voters ballots quota active
                          weight focused).kind = StepKind.elect :=
                      fractionalSTVStepFromFocus_kind_elect_of_quotaRespectingChoice
                        (choice := choice) hrespect hchoose
                        ⟨candidate, hcandidate_active, hquota⟩
                    have helim_first :
                        (fractionalSTVStepFromFocus voters ballots quota active
                          weight focused).kind = StepKind.eliminate := by
                      simpa [fractionalSTVChoiceRunFocuses,
                        fractionalSTVGeneratedSteps, hchoose, hfocused] using
                        heliminate
                    rw [helect] at helim_first
                    contradiction
                | succ n =>
                    have hn_tail :
                        n <
                          (fractionalSTVGeneratedSteps voters ballots quota
                            (fractionalSTVChoiceRunFocuses choice voters
                              ballots quota rounds (active.erase focused)
                              (fractionalSTVNextWeight voters ballots quota
                                (fractionalSTVStepFromFocus voters ballots quota
                                  active weight focused) weight))
                            (active.erase focused)
                            (fractionalSTVNextWeight voters ballots quota
                              (fractionalSTVStepFromFocus voters ballots quota
                                active weight focused) weight)).length := by
                      have hn_succ :
                          n.succ <
                            (fractionalSTVGeneratedSteps voters ballots quota
                              (fractionalSTVChoiceRunFocuses choice voters
                                ballots quota rounds (active.erase focused)
                                (fractionalSTVNextWeight voters ballots quota
                                  (fractionalSTVStepFromFocus voters ballots quota
                                    active weight focused) weight))
                              (active.erase focused)
                              (fractionalSTVNextWeight voters ballots quota
                                (fractionalSTVStepFromFocus voters ballots quota
                                  active weight focused) weight)).length.succ := by
                        simpa [fractionalSTVChoiceRunFocuses,
                          fractionalSTVGeneratedSteps, hchoose, hfocused] using hn
                      exact Nat.succ_lt_succ_iff.mp hn_succ
                    have htail :=
                      ih (active.erase focused)
                        (fractionalSTVNextWeight voters ballots quota
                          (fractionalSTVStepFromFocus voters ballots quota
                            active weight focused) weight)
                        ⟨n, hn_tail⟩ candidate
                    have htail_result :=
                      htail
                        (by
                          simpa [fractionalSTVChoiceRunFocuses,
                            fractionalSTVGeneratedSteps, hchoose, hfocused]
                            using hcandidate)
                        (by
                          simpa [fractionalSTVChoiceRunFocuses,
                            fractionalSTVGeneratedSteps, hchoose, hfocused]
                            using heliminate)
                    simpa [fractionalSTVGeneratedRoundTally,
                      fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps,
                      hchoose, hfocused] using htail_result
          · simp [fractionalSTVChoiceRunFocuses, fractionalSTVGeneratedSteps,
              hchoose, hfocused] at i
            exact Fin.elim0 i

/--
For a quota-respecting seat-limited simulator, any generated elimination round
certifies that no active candidate has reached quota at that round.
-/
theorem fractionalSTVSeatRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ (rounds elected : ℕ) (active : Finset Candidate) (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota
          (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit
            rounds elected active weight) active weight).length)
      (candidate : Candidate),
        candidate ∈
            ((fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit
                rounds elected active weight) active weight).get i).beforeActive →
          ((fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit
              rounds elected active weight) active weight).get i).kind =
              StepKind.eliminate →
            fractionalSTVGeneratedRoundTally voters ballots quota
              (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit
                rounds elected active weight) active weight i candidate <
              quota := by
  intro rounds
  induction rounds with
  | zero =>
      intro elected active weight i
      simp [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps] at i
      exact Fin.elim0 i
  | succ rounds ih =>
      intro elected active weight i candidate hcandidate heliminate
      by_cases hstop : seatLimit ≤ elected
      · simp [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
          hstop] at i
        exact Fin.elim0 i
      · cases hchoose :
            choice.choose active
              (fractionalActiveTally voters ballots weight active) with
        | none =>
            simp [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
              hstop, hchoose] at i
            exact Fin.elim0 i
        | some focused =>
            by_cases hfocused : focused ∈ active
            · let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let nextElected :=
                if step.kind = StepKind.elect then elected + 1 else elected
              cases i with
              | mk n hn =>
                  cases n with
                  | zero =>
                      have hcandidate_active : candidate ∈ active := by
                        simpa [fractionalSTVSeatRunFocuses,
                          fractionalSTVGeneratedSteps, hstop, hchoose,
                          hfocused, step, nextElected] using hcandidate
                      by_contra hnot_lt
                      have hnot_lt_active :
                          ¬ fractionalActiveTally voters ballots weight active
                              candidate < quota := by
                        intro hlt
                        exact hnot_lt (by
                          simpa [fractionalSTVGeneratedRoundTally,
                            fractionalSTVSeatRunFocuses,
                            fractionalSTVGeneratedSteps, hstop, hchoose,
                            hfocused, step, nextElected] using hlt)
                      have hquota :
                          quota ≤
                            fractionalActiveTally voters ballots weight active
                              candidate :=
                        not_lt.mp hnot_lt_active
                      have helect :
                          step.kind = StepKind.elect :=
                        fractionalSTVStepFromFocus_kind_elect_of_quotaRespectingChoice
                          (choice := choice) hrespect hchoose
                          ⟨candidate, hcandidate_active, hquota⟩
                      have helim_first : step.kind = StepKind.eliminate := by
                        simpa [fractionalSTVSeatRunFocuses,
                          fractionalSTVGeneratedSteps, hstop, hchoose,
                          hfocused, step, nextElected] using heliminate
                      rw [helect] at helim_first
                      contradiction
                  | succ n =>
                      have hn_tail :
                          n <
                            (fractionalSTVGeneratedSteps voters ballots quota
                              (fractionalSTVSeatRunFocuses choice voters
                                ballots quota seatLimit rounds nextElected
                                step.afterActive
                                (fractionalSTVNextWeight voters ballots quota
                                  step weight))
                              step.afterActive
                              (fractionalSTVNextWeight voters ballots quota
                                step weight)).length := by
                        have hn_succ :
                            n.succ <
                              (fractionalSTVGeneratedSteps voters ballots quota
                                (fractionalSTVSeatRunFocuses choice voters
                                  ballots quota seatLimit rounds nextElected
                                  step.afterActive
                                  (fractionalSTVNextWeight voters ballots quota
                                    step weight))
                                step.afterActive
                                (fractionalSTVNextWeight voters ballots quota
                                  step weight)).length.succ := by
                          simpa [fractionalSTVSeatRunFocuses,
                            fractionalSTVGeneratedSteps, hstop, hchoose,
                            hfocused, step, nextElected] using hn
                        exact Nat.succ_lt_succ_iff.mp hn_succ
                      have htail :=
                        ih nextElected step.afterActive
                          (fractionalSTVNextWeight voters ballots quota
                            step weight)
                          ⟨n, hn_tail⟩ candidate
                      have htail_result :=
                        htail
                          (by
                            simpa [fractionalSTVSeatRunFocuses,
                              fractionalSTVGeneratedSteps, hstop, hchoose,
                              hfocused, step, nextElected] using hcandidate)
                          (by
                            simpa [fractionalSTVSeatRunFocuses,
                              fractionalSTVGeneratedSteps, hstop, hchoose,
                              hfocused, step, nextElected] using heliminate)
                      simpa [fractionalSTVGeneratedRoundTally,
                        fractionalSTVSeatRunFocuses,
                        fractionalSTVGeneratedSteps, hstop, hchoose, hfocused,
                        step, nextElected] using htail_result
            · simp [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
                hstop, hchoose, hfocused] at i
              exact Fin.elim0 i

/--
For a quota-respecting filled-seat simulator, any generated elimination round
certifies that no active candidate has reached quota at that round.
-/
theorem fractionalSTVFilledSeatRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ (rounds elected : ℕ) (active : Finset Candidate) (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota
          (fractionalSTVFilledSeatRunFocuses choice voters ballots quota
            seatLimit rounds elected active weight) active weight).length)
      (candidate : Candidate),
        candidate ∈
            ((fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVFilledSeatRunFocuses choice voters ballots quota
                seatLimit rounds elected active weight) active weight).get i).beforeActive →
          ((fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVFilledSeatRunFocuses choice voters ballots quota
              seatLimit rounds elected active weight) active weight).get i).kind =
              StepKind.eliminate →
            fractionalSTVGeneratedRoundTally voters ballots quota
              (fractionalSTVFilledSeatRunFocuses choice voters ballots quota
                seatLimit rounds elected active weight) active weight i candidate <
              quota := by
  intro rounds
  induction rounds with
  | zero =>
      intro elected active weight i
      simp [fractionalSTVFilledSeatRunFocuses, fractionalSTVGeneratedSteps] at i
      exact Fin.elim0 i
  | succ rounds ih =>
      intro elected active weight i candidate hcandidate heliminate
      by_cases hstop : seatLimit ≤ elected
      · simp [fractionalSTVFilledSeatRunFocuses, fractionalSTVGeneratedSteps,
          hstop] at i
        exact Fin.elim0 i
      · by_cases hfill : active.card ≤ seatLimit - elected
        · simp [fractionalSTVFilledSeatRunFocuses,
            fractionalSTVGeneratedSteps, hstop, hfill] at i
          exact Fin.elim0 i
        · cases hchoose :
              choice.choose active
                (fractionalActiveTally voters ballots weight active) with
          | none =>
              simp [fractionalSTVFilledSeatRunFocuses,
                fractionalSTVGeneratedSteps, hstop, hfill, hchoose] at i
              exact Fin.elim0 i
          | some focused =>
              by_cases hfocused : focused ∈ active
              · let step :=
                  fractionalSTVStepFromFocus voters ballots quota active weight
                    focused
                let nextElected :=
                  if step.kind = StepKind.elect then elected + 1 else elected
                cases i with
                | mk n hn =>
                    cases n with
                    | zero =>
                        have hcandidate_active : candidate ∈ active := by
                          simpa [fractionalSTVFilledSeatRunFocuses,
                            fractionalSTVGeneratedSteps, hstop, hfill, hchoose,
                            hfocused, step, nextElected] using hcandidate
                        by_contra hnot_lt
                        have hnot_lt_active :
                            ¬ fractionalActiveTally voters ballots weight active
                                candidate < quota := by
                          intro hlt
                          exact hnot_lt (by
                            simpa [fractionalSTVGeneratedRoundTally,
                              fractionalSTVFilledSeatRunFocuses,
                              fractionalSTVGeneratedSteps, hstop, hfill,
                              hchoose, hfocused, step, nextElected] using hlt)
                        have hquota :
                            quota ≤
                              fractionalActiveTally voters ballots weight active
                                candidate :=
                          not_lt.mp hnot_lt_active
                        have helect :
                            step.kind = StepKind.elect :=
                          fractionalSTVStepFromFocus_kind_elect_of_quotaRespectingChoice
                            (choice := choice) hrespect hchoose
                            ⟨candidate, hcandidate_active, hquota⟩
                        have helim_first : step.kind = StepKind.eliminate := by
                          simpa [fractionalSTVFilledSeatRunFocuses,
                            fractionalSTVGeneratedSteps, hstop, hfill, hchoose,
                            hfocused, step, nextElected] using heliminate
                        rw [helect] at helim_first
                        contradiction
                    | succ n =>
                        have hn_tail :
                            n <
                              (fractionalSTVGeneratedSteps voters ballots quota
                                (fractionalSTVFilledSeatRunFocuses choice voters
                                  ballots quota seatLimit rounds nextElected
                                  step.afterActive
                                  (fractionalSTVNextWeight voters ballots quota
                                    step weight))
                                step.afterActive
                                (fractionalSTVNextWeight voters ballots quota
                                  step weight)).length := by
                          have hn_succ :
                              n.succ <
                                (fractionalSTVGeneratedSteps voters ballots quota
                                  (fractionalSTVFilledSeatRunFocuses choice voters
                                    ballots quota seatLimit rounds nextElected
                                    step.afterActive
                                    (fractionalSTVNextWeight voters ballots quota
                                      step weight))
                                  step.afterActive
                                  (fractionalSTVNextWeight voters ballots quota
                                    step weight)).length.succ := by
                            simpa [fractionalSTVFilledSeatRunFocuses,
                              fractionalSTVGeneratedSteps, hstop, hfill,
                              hchoose, hfocused, step, nextElected] using hn
                          exact Nat.succ_lt_succ_iff.mp hn_succ
                        have htail :=
                          ih nextElected step.afterActive
                            (fractionalSTVNextWeight voters ballots quota
                              step weight)
                            ⟨n, hn_tail⟩ candidate
                        have htail_result :=
                          htail
                            (by
                              simpa [fractionalSTVFilledSeatRunFocuses,
                                fractionalSTVGeneratedSteps, hstop, hfill,
                                hchoose, hfocused, step, nextElected] using
                                hcandidate)
                            (by
                              simpa [fractionalSTVFilledSeatRunFocuses,
                                fractionalSTVGeneratedSteps, hstop, hfill,
                                hchoose, hfocused, step, nextElected] using
                                heliminate)
                        simpa [fractionalSTVGeneratedRoundTally,
                          fractionalSTVFilledSeatRunFocuses,
                          fractionalSTVGeneratedSteps, hstop, hfill, hchoose,
                          hfocused, step, nextElected] using htail_result
              · simp [fractionalSTVFilledSeatRunFocuses,
                  fractionalSTVGeneratedSteps, hstop, hfill, hchoose,
                  hfocused] at i
                exact Fin.elim0 i

/--
For a quota-respecting party-seat-limited simulator, any generated elimination
round certifies that no active candidate has reached quota at that round.
-/
theorem fractionalSTVPartySeatRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit : ℕ)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ (rounds partyElected : ℕ) (active : Finset Candidate)
      (weight : Voter → ℝ)
      (i : Fin
        (fractionalSTVGeneratedSteps voters ballots quota
          (fractionalSTVPartySeatRunFocuses choice voters ballots quota
            partyCandidates partySeatLimit rounds partyElected active weight)
          active weight).length)
      (candidate : Candidate),
        candidate ∈
            ((fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVPartySeatRunFocuses choice voters ballots quota
                partyCandidates partySeatLimit rounds partyElected active weight)
              active weight).get i).beforeActive →
          ((fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVPartySeatRunFocuses choice voters ballots quota
              partyCandidates partySeatLimit rounds partyElected active weight)
            active weight).get i).kind = StepKind.eliminate →
            fractionalSTVGeneratedRoundTally voters ballots quota
              (fractionalSTVPartySeatRunFocuses choice voters ballots quota
                partyCandidates partySeatLimit rounds partyElected active weight)
              active weight i candidate < quota := by
  intro rounds
  induction rounds with
  | zero =>
      intro partyElected active weight i
      simp [fractionalSTVPartySeatRunFocuses, fractionalSTVGeneratedSteps] at i
      exact Fin.elim0 i
  | succ rounds ih =>
      intro partyElected active weight i candidate hcandidate heliminate
      by_cases hstop : partySeatLimit ≤ partyElected
      · simp [fractionalSTVPartySeatRunFocuses, fractionalSTVGeneratedSteps,
          hstop] at i
        exact Fin.elim0 i
      · cases hchoose :
            choice.choose active
              (fractionalActiveTally voters ballots weight active) with
        | none =>
            simp [fractionalSTVPartySeatRunFocuses,
              fractionalSTVGeneratedSteps, hstop, hchoose] at i
            exact Fin.elim0 i
        | some focused =>
            by_cases hfocused : focused ∈ active
            · let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let partyElection :=
                step.kind = StepKind.elect ∧ focused ∈ partyCandidates
              let nextPartyElected :=
                if partyElection then partyElected + 1 else partyElected
              cases i with
              | mk n hn =>
                  cases n with
                  | zero =>
                      have hcandidate_active : candidate ∈ active := by
                        simpa [fractionalSTVPartySeatRunFocuses,
                          fractionalSTVGeneratedSteps, hstop, hchoose,
                          hfocused, step, partyElection, nextPartyElected]
                          using hcandidate
                      by_contra hnot_lt
                      have hnot_lt_active :
                          ¬ fractionalActiveTally voters ballots weight active
                              candidate < quota := by
                        intro hlt
                        exact hnot_lt (by
                          simpa [fractionalSTVGeneratedRoundTally,
                            fractionalSTVPartySeatRunFocuses,
                            fractionalSTVGeneratedSteps, hstop, hchoose,
                            hfocused, step, partyElection, nextPartyElected]
                            using hlt)
                      have hquota :
                          quota ≤
                            fractionalActiveTally voters ballots weight active
                              candidate :=
                        not_lt.mp hnot_lt_active
                      have helect :
                          step.kind = StepKind.elect :=
                        fractionalSTVStepFromFocus_kind_elect_of_quotaRespectingChoice
                          (choice := choice) hrespect hchoose
                          ⟨candidate, hcandidate_active, hquota⟩
                      have helim_first : step.kind = StepKind.eliminate := by
                        simpa [fractionalSTVPartySeatRunFocuses,
                          fractionalSTVGeneratedSteps, hstop, hchoose,
                          hfocused, step, partyElection, nextPartyElected]
                          using heliminate
                      rw [helect] at helim_first
                      contradiction
                  | succ n =>
                      have hn_tail :
                          n <
                            (fractionalSTVGeneratedSteps voters ballots quota
                              (fractionalSTVPartySeatRunFocuses choice voters
                                ballots quota partyCandidates partySeatLimit
                                rounds nextPartyElected step.afterActive
                                (fractionalSTVNextWeight voters ballots quota
                                  step weight))
                              step.afterActive
                              (fractionalSTVNextWeight voters ballots quota
                                step weight)).length := by
                        have hn_succ :
                            n.succ <
                              (fractionalSTVGeneratedSteps voters ballots quota
                                (fractionalSTVPartySeatRunFocuses choice voters
                                  ballots quota partyCandidates partySeatLimit
                                  rounds nextPartyElected step.afterActive
                                  (fractionalSTVNextWeight voters ballots quota
                                    step weight))
                                step.afterActive
                                (fractionalSTVNextWeight voters ballots quota
                                  step weight)).length.succ := by
                          simpa [fractionalSTVPartySeatRunFocuses,
                            fractionalSTVGeneratedSteps, hstop, hchoose,
                            hfocused, step, partyElection, nextPartyElected]
                            using hn
                        exact Nat.succ_lt_succ_iff.mp hn_succ
                      have htail :=
                        ih nextPartyElected step.afterActive
                          (fractionalSTVNextWeight voters ballots quota
                            step weight)
                          ⟨n, hn_tail⟩ candidate
                      have htail_result :=
                        htail
                          (by
                            simpa [fractionalSTVPartySeatRunFocuses,
                              fractionalSTVGeneratedSteps, hstop, hchoose,
                              hfocused, step, partyElection, nextPartyElected]
                              using hcandidate)
                          (by
                            simpa [fractionalSTVPartySeatRunFocuses,
                              fractionalSTVGeneratedSteps, hstop, hchoose,
                              hfocused, step, partyElection, nextPartyElected]
                              using heliminate)
                      simpa [fractionalSTVGeneratedRoundTally,
                        fractionalSTVPartySeatRunFocuses,
                        fractionalSTVGeneratedSteps, hstop, hchoose, hfocused,
                        step, partyElection, nextPartyElected] using htail_result
            · simp [fractionalSTVPartySeatRunFocuses,
                fractionalSTVGeneratedSteps, hstop, hchoose, hfocused] at i
              exact Fin.elim0 i

/--
The generated focused-run simulator constructs an indexed executable fractional
STV trace.
-/
noncomputable def fractionalSTVIndexedExecutableTrace_of_generated
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (focuses : List Candidate) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter) :
    FractionalSTVIndexedExecutableTrace
      (fractionalSTVGeneratedTrace voters ballots quota focuses initialActive
        initialWeight)
      voters ballots quota initialActive
      (fractionalSTVGeneratedTerminalActive voters ballots quota focuses
        initialActive initialWeight)
      initialWeight where
  roundTally :=
    fractionalSTVGeneratedRoundTally voters ballots quota focuses initialActive
      initialWeight
  quota_pos := hquota_pos
  step_removes :=
    fractionalSTVGeneratedSteps_get_removesFocusedCandidate voters ballots quota
      focuses initialActive initialWeight
  step_focus_active :=
    fractionalSTVGeneratedSteps_get_focus_active voters ballots quota focuses
      initialActive initialWeight
  initialWeight_nonneg := hinitialWeight_nonneg
  tally_eq := by
    intro i candidate _hcandidate
    rfl
  kind_allowed :=
    fractionalSTVGeneratedSteps_get_kind_allowed voters ballots quota focuses
      initialActive initialWeight
  quota_if_elect :=
    fractionalSTVGeneratedSteps_get_quota_if_elect voters ballots quota focuses
      initialActive initialWeight
  activeReplay :=
    fractionalSTVGeneratedSteps_replayStepsFrom voters ballots quota focuses
      initialActive initialWeight

/--
The deterministic choice-rule simulator constructs an indexed executable
fractional STV trace. This is the source-primitive entry point for papers whose
STV convention is given by a concrete tie-breaking/selection rule rather than a
pre-supplied replay certificate.
-/
noncomputable def fractionalSTVIndexedExecutableTrace_of_choiceRun
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter) :
    FractionalSTVIndexedExecutableTrace
      (fractionalSTVChoiceRunTrace choice voters ballots quota rounds
        initialActive initialWeight)
      voters ballots quota initialActive
      (fractionalSTVChoiceRunTerminalActive choice voters ballots quota rounds
        initialActive initialWeight)
      initialWeight :=
  fractionalSTVIndexedExecutableTrace_of_generated voters ballots quota
    (fractionalSTVChoiceRunFocuses choice voters ballots quota rounds
      initialActive initialWeight)
    initialActive initialWeight hquota_pos hinitialWeight_nonneg

/--
The seat-limited fractional STV simulator constructs an indexed executable
fractional STV trace.
-/
noncomputable def fractionalSTVIndexedExecutableTrace_of_seatRun
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter) :
    FractionalSTVIndexedExecutableTrace
      (fractionalSTVSeatRunTrace choice voters ballots quota seatLimit rounds
        initialElected initialActive initialWeight)
      voters ballots quota initialActive
      (fractionalSTVSeatRunTerminalActive choice voters ballots quota seatLimit
        rounds initialElected initialActive initialWeight)
      initialWeight :=
  fractionalSTVIndexedExecutableTrace_of_generated voters ballots quota
    (fractionalSTVSeatRunFocuses choice voters ballots quota seatLimit rounds
      initialElected initialActive initialWeight)
    initialActive initialWeight hquota_pos hinitialWeight_nonneg

/--
The filled-seat fractional STV simulator constructs an indexed executable
fractional STV trace for its transfer prefix.
-/
noncomputable def fractionalSTVIndexedExecutableTrace_of_filledSeatRun
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter) :
    FractionalSTVIndexedExecutableTrace
      (fractionalSTVFilledSeatRunTrace choice voters ballots quota seatLimit
        rounds initialElected initialActive initialWeight)
      voters ballots quota initialActive
      (fractionalSTVFilledSeatRunTerminalActive choice voters ballots quota
        seatLimit rounds initialElected initialActive initialWeight)
      initialWeight :=
  fractionalSTVIndexedExecutableTrace_of_generated voters ballots quota
    (fractionalSTVFilledSeatRunFocuses choice voters ballots quota seatLimit
      rounds initialElected initialActive initialWeight)
    initialActive initialWeight hquota_pos hinitialWeight_nonneg

/--
The party-seat-limited fractional STV simulator constructs an indexed
executable fractional STV trace.
-/
noncomputable def fractionalSTVIndexedExecutableTrace_of_partySeatRun
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit rounds initialPartyElected : ℕ)
    (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter) :
    FractionalSTVIndexedExecutableTrace
      (fractionalSTVPartySeatRunTrace choice voters ballots quota
        partyCandidates partySeatLimit rounds initialPartyElected initialActive
        initialWeight)
      voters ballots quota initialActive
      (fractionalSTVPartySeatRunTerminalActive choice voters ballots quota
        partyCandidates partySeatLimit rounds initialPartyElected initialActive
        initialWeight)
      initialWeight :=
  fractionalSTVIndexedExecutableTrace_of_generated voters ballots quota
    (fractionalSTVPartySeatRunFocuses choice voters ballots quota
      partyCandidates partySeatLimit rounds initialPartyElected initialActive
      initialWeight)
    initialActive initialWeight hquota_pos hinitialWeight_nonneg

/--
Quota-respecting seat-run simulator certificate: every generated elimination
round has all active candidates below quota in the certificate's round tally.
-/
theorem fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate) (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ i : Fin
        (fractionalSTVSeatRunTrace choice voters ballots quota seatLimit
          rounds initialElected initialActive initialWeight).steps.length,
      ∀ candidate,
        candidate ∈
            ((fractionalSTVSeatRunTrace choice voters ballots quota seatLimit
              rounds initialElected initialActive initialWeight).steps.get i).beforeActive →
          ((fractionalSTVSeatRunTrace choice voters ballots quota seatLimit
            rounds initialElected initialActive initialWeight).steps.get i).kind =
              StepKind.eliminate →
            (fractionalSTVIndexedExecutableTrace_of_seatRun choice voters
              ballots quota seatLimit rounds initialElected initialActive
              initialWeight hquota_pos hinitialWeight_nonneg).roundTally i
                candidate < quota := by
  intro i candidate hcandidate hkind
  simpa [fractionalSTVSeatRunTrace,
    fractionalSTVIndexedExecutableTrace_of_seatRun,
    fractionalSTVIndexedExecutableTrace_of_generated] using
    fractionalSTVSeatRun_get_noquota_if_eliminate choice voters ballots quota
      seatLimit hrespect rounds initialElected initialActive initialWeight i
      candidate hcandidate hkind

/--
Quota-respecting filled-seat simulator certificate: every generated
elimination round has all active candidates below quota in the certificate's
round tally.
-/
theorem fractionalSTVIndexedExecutableTrace_of_filledSeatRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds initialElected : ℕ)
    (initialActive : Finset Candidate) (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ i : Fin
        (fractionalSTVFilledSeatRunTrace choice voters ballots quota seatLimit
          rounds initialElected initialActive initialWeight).steps.length,
      ∀ candidate,
        candidate ∈
            ((fractionalSTVFilledSeatRunTrace choice voters ballots quota
              seatLimit rounds initialElected initialActive
              initialWeight).steps.get i).beforeActive →
          ((fractionalSTVFilledSeatRunTrace choice voters ballots quota
            seatLimit rounds initialElected initialActive
            initialWeight).steps.get i).kind =
              StepKind.eliminate →
            (fractionalSTVIndexedExecutableTrace_of_filledSeatRun choice voters
              ballots quota seatLimit rounds initialElected initialActive
              initialWeight hquota_pos hinitialWeight_nonneg).roundTally i
                candidate < quota := by
  intro i candidate hcandidate hkind
  simpa [fractionalSTVFilledSeatRunTrace,
    fractionalSTVIndexedExecutableTrace_of_filledSeatRun,
    fractionalSTVIndexedExecutableTrace_of_generated] using
    fractionalSTVFilledSeatRun_get_noquota_if_eliminate choice voters ballots
      quota seatLimit hrespect rounds initialElected initialActive
      initialWeight i candidate hcandidate hkind

/--
Quota-respecting party-seat-limited simulator certificate: every generated
elimination round has all active candidates below quota in the certificate's
round tally.
-/
theorem fractionalSTVIndexedExecutableTrace_of_partySeatRun_get_noquota_if_eliminate
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit rounds initialPartyElected : ℕ)
    (initialActive : Finset Candidate) (initialWeight : Voter → ℝ)
    (hquota_pos : 0 < quota)
    (hinitialWeight_nonneg :
      ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter)
    (hrespect : choice.QuotaRespecting quota) :
    ∀ i : Fin
        (fractionalSTVPartySeatRunTrace choice voters ballots quota
          partyCandidates partySeatLimit rounds initialPartyElected
          initialActive initialWeight).steps.length,
      ∀ candidate,
        candidate ∈
            ((fractionalSTVPartySeatRunTrace choice voters ballots quota
              partyCandidates partySeatLimit rounds initialPartyElected
              initialActive initialWeight).steps.get i).beforeActive →
          ((fractionalSTVPartySeatRunTrace choice voters ballots quota
            partyCandidates partySeatLimit rounds initialPartyElected
            initialActive initialWeight).steps.get i).kind =
              StepKind.eliminate →
            (fractionalSTVIndexedExecutableTrace_of_partySeatRun choice voters
              ballots quota partyCandidates partySeatLimit rounds
              initialPartyElected initialActive initialWeight hquota_pos
              hinitialWeight_nonneg).roundTally i candidate < quota := by
  intro i candidate hcandidate hkind
  simpa [fractionalSTVPartySeatRunTrace,
    fractionalSTVIndexedExecutableTrace_of_partySeatRun,
    fractionalSTVIndexedExecutableTrace_of_generated] using
    fractionalSTVPartySeatRun_get_noquota_if_eliminate choice voters ballots
      quota partyCandidates partySeatLimit hrespect rounds
      initialPartyElected initialActive initialWeight i candidate hcandidate
      hkind

/--
Under two solid coalitions, the executable global fractional STV weight fold
restricts to the party-specific executable fold on voters in the first
coalition.
-/
theorem fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters otherVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {quota : ℝ} {steps : List (STVStep Candidate)}
    {initialAllWeight initialWeight : Voter → ℝ}
    (hpartition : allVoters = voters ∪ otherVoters)
    (hvoterDisjoint : Disjoint voters otherVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherVoters ballots otherPartyCandidates)
    (hpartyActive :
      ∀ i : Fin steps.length,
        ∃ same, same ∈ partyCandidates ∧ same ∈ (steps.get i).beforeActive)
    (hotherActive :
      ∀ i : Fin steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (steps.get i).beforeActive)
    (hinitialWeight :
      ∀ voter, voter ∈ voters → initialAllWeight voter = initialWeight voter) :
    ∀ voter, voter ∈ voters →
      fractionalSTVWeightAfterSteps allVoters ballots quota steps
          initialAllWeight voter =
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter := by
  induction steps generalizing initialAllWeight initialWeight with
  | nil =>
      intro voter hvoter
      simpa [fractionalSTVWeightAfterSteps] using hinitialWeight voter hvoter
  | cons step steps ih =>
      intro voter hvoter
      dsimp [fractionalSTVWeightAfterSteps]
      exact ih
        (by
          intro i
          exact hpartyActive
            ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩)
        (by
          intro i
          exact hotherActive
            ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩)
        (by
          intro voter hvoter
          exact
            fractionalSTVNextWeight_eq_on_solidCoalition_left
              (allVoters := allVoters) (voters := voters)
              (otherVoters := otherVoters) (ballots := ballots)
              (partyCandidates := partyCandidates)
              (otherPartyCandidates := otherPartyCandidates)
              (quota := quota) (step := step)
              (allWeight := initialAllWeight) (weight := initialWeight)
              hpartition hvoterDisjoint hcandidateDisjoint hsolid hotherSolid
              (hpartyActive ⟨0, by simp⟩) (hotherActive ⟨0, by simp⟩)
              hinitialWeight voter hvoter)
        voter hvoter

/--
Membership-indexed variant of
`fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left`.
-/
theorem fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters voters otherVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {quota : ℝ} {steps : List (STVStep Candidate)}
    {initialAllWeight initialWeight : Voter → ℝ}
    (hpartition : allVoters = voters ∪ otherVoters)
    (hvoterDisjoint : Disjoint voters otherVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hotherSolid : SolidCoalitionBallots otherVoters ballots otherPartyCandidates)
    (hpartyActive :
      ∀ step, step ∈ steps →
        ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive)
    (hotherActive :
      ∀ step, step ∈ steps →
        ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive)
    (hinitialWeight :
      ∀ voter, voter ∈ voters → initialAllWeight voter = initialWeight voter) :
    ∀ voter, voter ∈ voters →
      fractionalSTVWeightAfterSteps allVoters ballots quota steps
          initialAllWeight voter =
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter := by
  exact
    fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left
      (allVoters := allVoters) (voters := voters)
      (otherVoters := otherVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates) (quota := quota)
      (steps := steps) (initialAllWeight := initialAllWeight)
      (initialWeight := initialWeight) hpartition hvoterDisjoint
      hcandidateDisjoint hsolid hotherSolid
      (by
        intro i
        exact hpartyActive (steps.get i) (List.get_mem steps i))
      (by
        intro i
        exact hotherActive (steps.get i) (List.get_mem steps i))
      hinitialWeight

/--
One-step party-weight accounting: the fractional transfer update subtracts one
quota exactly on same-party election rounds, and otherwise preserves the
party voter group's total weight.
-/
theorem sum_fractionalSTVNextWeight_eq_sum_sub_partyElectStepIndicator
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {step : STVStep Candidate} {weight : Voter → ℝ}
    (hquota_pos : 0 < quota)
    (hlaw :
      FractionalSTVPartyWeightStepLaw voters ballots partyCandidates quota
        step weight) :
    (∑ voter ∈ voters,
        fractionalSTVNextWeight voters ballots quota step weight voter) =
      (∑ voter ∈ voters, weight voter) -
        (match step.focus with
        | none => 0
        | some focused =>
            if step.kind = StepKind.elect ∧ focused ∈ partyCandidates then
              quota
            else
              0) := by
  rcases hlaw with ⟨hsame_quota, houtside_empty⟩
  cases hfocus : step.focus with
  | none =>
      simp [fractionalSTVNextWeight, hfocus]
  | some focused =>
      by_cases hparty : focused ∈ partyCandidates
      · cases hkind : step.kind with
        | elect =>
            have hquota_le :
                quota ≤
                  fractionalActiveTally voters ballots weight
                    step.beforeActive focused :=
              hsame_quota focused hfocus hkind hparty
            have htally_pos :
                0 <
                  fractionalActiveTally voters ballots weight
                    step.beforeActive focused :=
              lt_of_lt_of_le hquota_pos hquota_le
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_elect_eq_sum_sub_quota
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight)
                hfocus hkind htally_pos.ne'
        | eliminate =>
            have hne : step.kind ≠ StepKind.elect := by simp [hkind]
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_of_kind_ne_elect
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight) hne
        | transfer =>
            have hne : step.kind ≠ StepKind.elect := by simp [hkind]
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_of_kind_ne_elect
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight) hne
        | finish =>
            have hne : step.kind ≠ StepKind.elect := by simp [hkind]
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_of_kind_ne_elect
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight) hne
      · cases hkind : step.kind with
        | elect =>
            have hempty :
                Ballot.activeSupport voters ballots step.beforeActive
                  focused = ∅ :=
              houtside_empty focused hfocus hkind hparty
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_elect_eq_sum_of_activeSupport_eq_empty
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight)
                hfocus hkind hempty
        | eliminate =>
            have hne : step.kind ≠ StepKind.elect := by simp [hkind]
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_of_kind_ne_elect
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight) hne
        | transfer =>
            have hne : step.kind ≠ StepKind.elect := by simp [hkind]
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_of_kind_ne_elect
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight) hne
        | finish =>
            have hne : step.kind ≠ StepKind.elect := by simp [hkind]
            simpa [hfocus, hkind, hparty] using
              sum_fractionalSTVNextWeight_of_kind_ne_elect
                (voters := voters) (ballots := ballots) (quota := quota)
                (step := step) (weight := weight) hne

/--
Number of concrete trace steps that elect a candidate belonging to a party.

This is a trace-level final-seat accounting primitive: the deterministic
party-state fold increments `quotaWinners` exactly on these steps, and the
fractional weight fold removes exactly one quota of mass on these steps.
-/
def partyElectStepCount {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) : List (STVStep Candidate) → ℕ
  | [] => 0
  | step :: steps =>
      (match step.focus with
      | none => 0
      | some focused =>
          if step.kind = StepKind.elect ∧ focused ∈ partyCandidates then
            1
          else
            0) + partyElectStepCount partyCandidates steps

@[simp] theorem partyElectStepCount_nil {Candidate : Type*}
    [DecidableEq Candidate] (partyCandidates : Finset Candidate) :
    partyElectStepCount partyCandidates ([] : List (STVStep Candidate)) = 0 :=
  rfl

@[simp] theorem partyElectStepCount_cons {Candidate : Type*}
    [DecidableEq Candidate] (partyCandidates : Finset Candidate)
    (step : STVStep Candidate) (steps : List (STVStep Candidate)) :
    partyElectStepCount partyCandidates (step :: steps) =
      (match step.focus with
      | none => 0
      | some focused =>
          if step.kind = StepKind.elect ∧ focused ∈ partyCandidates then
            1
          else
            0) + partyElectStepCount partyCandidates steps :=
  rfl

/-- A prefix has no more same-party election steps than the full trace. -/
theorem partyElectStepCount_take_le {Candidate : Type*}
    [DecidableEq Candidate] (partyCandidates : Finset Candidate) :
    ∀ (steps : List (STVStep Candidate)) (n : ℕ),
      partyElectStepCount partyCandidates (steps.take n) ≤
        partyElectStepCount partyCandidates steps
  | [], _ => by simp
  | step :: steps, 0 => by simp
  | step :: steps, n + 1 => by
      dsimp [List.take, partyElectStepCount]
      exact Nat.add_le_add_left
        (partyElectStepCount_take_le partyCandidates steps n) _

/-- Number of concrete trace steps labeled as election steps. -/
def electStepCount {Candidate : Type*} : List (STVStep Candidate) → ℕ
  | [] => 0
  | step :: steps =>
      (if step.kind = StepKind.elect then 1 else 0) + electStepCount steps

@[simp] theorem electStepCount_nil {Candidate : Type*} :
    electStepCount ([] : List (STVStep Candidate)) = 0 :=
  rfl

@[simp] theorem electStepCount_cons {Candidate : Type*}
    (step : STVStep Candidate) (steps : List (STVStep Candidate)) :
    electStepCount (step :: steps) =
      (if step.kind = StepKind.elect then 1 else 0) + electStepCount steps :=
  rfl

/--
Terminal candidates that the source filled-seat STV rule reads as final seats.

If the transfer prefix has already filled the seat limit with quota election
rounds, no terminal active candidates are filled. Otherwise the terminal active
candidates are the remaining filled seats.
-/
def terminalFillActive {Candidate : Type*} (seatLimit : ℕ)
    (steps : List (STVStep Candidate)) (terminalActive : Finset Candidate) :
    Finset Candidate :=
  if electStepCount steps < seatLimit then terminalActive else ∅

/--
Final same-party seat count for the source filled-seat STV interpretation:
same-party quota election rounds plus terminal active same-party candidates
that fill the remaining seats.
-/
def partyFilledSeatCount {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (seatLimit : ℕ)
    (steps : List (STVStep Candidate)) (terminalActive : Finset Candidate) :
    ℕ :=
  partyElectStepCount partyCandidates steps +
    (activePartyCandidates (terminalFillActive seatLimit steps terminalActive)
      partyCandidates).card

/--
The two active-party filters partition an active set covered by two disjoint
candidate parties.
-/
theorem activePartyCandidates_card_add_eq_card_of_subset_union_of_disjoint
    {Candidate : Type*} [DecidableEq Candidate]
    {active partyCandidates otherPartyCandidates : Finset Candidate}
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hactive_subset : active ⊆ partyCandidates ∪ otherPartyCandidates) :
    (activePartyCandidates active partyCandidates).card +
        (activePartyCandidates active otherPartyCandidates).card =
      active.card := by
  have hdisjoint :
      Disjoint (activePartyCandidates active partyCandidates)
        (activePartyCandidates active otherPartyCandidates) := by
    refine Finset.disjoint_left.mpr ?_
    intro candidate hparty hother
    exact (Finset.disjoint_left.mp hcandidateDisjoint)
      (Finset.mem_filter.mp hparty).2 (Finset.mem_filter.mp hother).2
  have hunion :
      activePartyCandidates active partyCandidates ∪
          activePartyCandidates active otherPartyCandidates =
        active := by
    ext candidate
    constructor
    · intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · exact (Finset.mem_filter.mp hmem).1
      · exact (Finset.mem_filter.mp hmem).1
    · intro hmem
      rcases Finset.mem_union.mp (hactive_subset hmem) with hparty | hother
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hmem, hparty⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hmem, hother⟩)
  calc
    (activePartyCandidates active partyCandidates).card +
        (activePartyCandidates active otherPartyCandidates).card
        =
          (activePartyCandidates active partyCandidates ∪
            activePartyCandidates active otherPartyCandidates).card := by
            rw [Finset.card_union_of_disjoint hdisjoint]
    _ = active.card := by rw [hunion]

/--
Filled-seat STV accounting for a recursive source run.

If the source choice rule is total, the round budget is at least the current
number of active candidates, and the active set has enough candidates to fill
the remaining seats, then quota-election steps plus terminal active fills
complete exactly the seat limit. The `elected` parameter records seats filled
before this recursive suffix.
-/
theorem add_electStepCount_add_terminalActive_card_fractionalSTVFilledSeatRun_eq_seatLimit_of_total
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ)
    (htotal : choice.Total) :
    ∀ (rounds elected : ℕ) (active : Finset Candidate)
      (weight : Voter → ℝ),
      elected ≤ seatLimit →
        seatLimit - elected ≤ active.card →
          active.card ≤ rounds →
            let focuses :=
              fractionalSTVFilledSeatRunFocuses choice voters ballots quota
                seatLimit rounds elected active weight
            let steps :=
              fractionalSTVGeneratedSteps voters ballots quota focuses active
                weight
            let terminalActive :=
              fractionalSTVGeneratedTerminalActive voters ballots quota focuses
                active weight
            elected + electStepCount steps +
                (if elected + electStepCount steps < seatLimit then
                  terminalActive.card
                else
                  0) =
              seatLimit := by
  intro rounds
  induction rounds with
  | zero =>
      intro elected active weight helected hremaining hrounds
      have hactive_card : active.card = 0 := Nat.eq_zero_of_le_zero hrounds
      have hremaining_zero : seatLimit - elected = 0 :=
        Nat.eq_zero_of_le_zero (by simpa [hactive_card] using hremaining)
      have heq : elected = seatLimit := by omega
      subst heq
      simp [fractionalSTVFilledSeatRunFocuses, fractionalSTVGeneratedSteps]
  | succ rounds ih =>
      intro elected active weight helected hremaining hrounds
      by_cases hstop : seatLimit ≤ elected
      · have heq : elected = seatLimit := le_antisymm helected hstop
        subst heq
        simp [fractionalSTVFilledSeatRunFocuses, fractionalSTVGeneratedSteps]
      · have helected_lt : elected < seatLimit := Nat.lt_of_not_ge hstop
        by_cases hfill : active.card ≤ seatLimit - elected
        · have hfill_eq : active.card = seatLimit - elected :=
            le_antisymm hfill hremaining
          have hif : elected < seatLimit := helected_lt
          simp [fractionalSTVFilledSeatRunFocuses, fractionalSTVGeneratedSteps,
            fractionalSTVGeneratedTerminalActive, hstop, hfill, hif]
          omega
        · have hactive_nonempty : active.Nonempty := by
            have hpos : 0 < seatLimit - elected := Nat.sub_pos_of_lt helected_lt
            exact Finset.card_pos.mp (lt_of_lt_of_le hpos hremaining)
          rcases htotal
              (active := active)
              (tally := fractionalActiveTally voters ballots weight active)
              hactive_nonempty with
            ⟨focused, hchoose⟩
          have hfocused : focused ∈ active := choice.choose_mem hchoose
          let step :=
            fractionalSTVStepFromFocus voters ballots quota active weight focused
          let nextElected :=
            if step.kind = StepKind.elect then elected + 1 else elected
          have hnextElected_le : nextElected ≤ seatLimit := by
            by_cases helect : step.kind = StepKind.elect
            · simp [nextElected, helect]
              omega
            · simpa [nextElected, helect] using helected
          have hafter_card :
              step.afterActive.card + 1 = active.card := by
            simpa [step] using Finset.card_erase_add_one hfocused
          have hafter_rounds : step.afterActive.card ≤ rounds := by
            omega
          have hnextRemaining :
              seatLimit - nextElected ≤ step.afterActive.card := by
            by_cases helect : step.kind = StepKind.elect
            · have hsub :
                  seatLimit - (elected + 1) + 1 = seatLimit - elected := by
                omega
              simp [nextElected, helect]
              omega
            · have hstrict : seatLimit - elected < active.card := by
                omega
              simp [nextElected, helect]
              omega
          have htail :=
            ih nextElected step.afterActive
              (fractionalSTVNextWeight voters ballots quota step weight)
              hnextElected_le hnextRemaining hafter_rounds
          by_cases helect : step.kind = StepKind.elect
          · rw [fractionalSTVFilledSeatRunFocuses]
            simp only [hstop, if_false, hfill, hchoose, hfocused, if_true]
            simpa [fractionalSTVGeneratedSteps,
              fractionalSTVGeneratedTerminalActive, step, nextElected,
              hfocused, helect, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using htail
          · rw [fractionalSTVFilledSeatRunFocuses]
            simp only [hstop, if_false, hfill, hchoose, hfocused, if_true]
            simpa [fractionalSTVGeneratedSteps,
              fractionalSTVGeneratedTerminalActive, step, nextElected,
              hfocused, helect, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using htail

/--
A zero-initial generated filled-seat run with enough active candidates and a
round budget equal to the initial active set fills exactly the requested number
of seats, counting terminal active candidates as the source rule's final fills.
-/
theorem electStepCount_add_terminalFillActive_card_fractionalSTVFilledSeatRunTrace_eq_seatLimit_of_total
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (htotal : choice.Total) (hseats : seatLimit ≤ initialActive.card) :
    electStepCount
          (fractionalSTVFilledSeatRunTrace choice voters ballots quota
            seatLimit initialActive.card 0 initialActive initialWeight).steps +
        (terminalFillActive seatLimit
          (fractionalSTVFilledSeatRunTrace choice voters ballots quota
            seatLimit initialActive.card 0 initialActive initialWeight).steps
          (fractionalSTVFilledSeatRunTerminalActive choice voters ballots quota
            seatLimit initialActive.card 0 initialActive initialWeight)).card =
      seatLimit := by
  have h :=
    add_electStepCount_add_terminalActive_card_fractionalSTVFilledSeatRun_eq_seatLimit_of_total
      choice voters ballots quota seatLimit htotal initialActive.card 0
      initialActive initialWeight (Nat.zero_le seatLimit) (by simpa using hseats)
      le_rfl
  let steps :=
    (fractionalSTVFilledSeatRunTrace choice voters ballots quota seatLimit
      initialActive.card 0 initialActive initialWeight).steps
  let terminalActive :=
    fractionalSTVFilledSeatRunTerminalActive choice voters ballots quota
      seatLimit initialActive.card 0 initialActive initialWeight
  change
    electStepCount steps +
        (terminalFillActive seatLimit steps terminalActive).card =
      seatLimit
  have h' :
      electStepCount steps +
          (if electStepCount steps < seatLimit then terminalActive.card else 0) =
        seatLimit := by
    simpa [fractionalSTVFilledSeatRunTrace,
      fractionalSTVFilledSeatRunTerminalActive, fractionalSTVGeneratedTrace,
      steps, terminalActive] using h
  by_cases hlt : electStepCount steps < seatLimit
  · simpa [terminalFillActive, hlt] using h'
  · simpa [terminalFillActive, hlt] using h'

/--
Total-weight accounting for a concrete fractional STV trace: every election
round removes exactly one quota of total weight, while every non-election round
preserves total weight.
-/
theorem sum_fractionalSTVWeightAfterSteps_eq_sum_sub_electStepCount
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {steps : List (STVStep Candidate)}
    {initialWeight : Voter → ℝ}
    (hquota_pos : 0 < quota)
    (hfocus :
      ∀ i : Fin steps.length,
        ∃ focused, (steps.get i).focus = some focused ∧
          focused ∈ (steps.get i).beforeActive)
    (hquota_if_elect :
      ∀ i : Fin steps.length, ∀ focused,
        (steps.get i).focus = some focused →
          (steps.get i).kind = StepKind.elect →
            quota ≤
              fractionalActiveTally voters ballots
                (fractionalSTVWeightAfterSteps voters ballots quota
                  (steps.take i.1) initialWeight)
                (steps.get i).beforeActive focused) :
    (∑ voter ∈ voters,
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter) =
      (∑ voter ∈ voters, initialWeight voter) -
        (electStepCount steps : ℝ) * quota := by
  induction steps generalizing initialWeight with
  | nil =>
      simp [fractionalSTVWeightAfterSteps, electStepCount]
  | cons step steps ih =>
      let nextWeight := fractionalSTVNextWeight voters ballots quota step
        initialWeight
      have htail :
          (∑ voter ∈ voters,
              fractionalSTVWeightAfterSteps voters ballots quota steps
                nextWeight voter) =
            (∑ voter ∈ voters, nextWeight voter) -
              (electStepCount steps : ℝ) * quota := by
        apply ih
        · intro i
          rcases hfocus ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩ with
            ⟨focused, hfocused, hactive⟩
          exact ⟨focused, hfocused, hactive⟩
        · intro i focused hfocused hkind
          have hsucc :=
            hquota_if_elect
              ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
              focused hfocused hkind
          simpa [fractionalSTVWeightAfterSteps, nextWeight,
            Nat.succ_eq_add_one] using hsucc
      have hstep_sum :
          (∑ voter ∈ voters, nextWeight voter) =
            (∑ voter ∈ voters, initialWeight voter) -
              (if step.kind = StepKind.elect then quota else 0) := by
        by_cases helect : step.kind = StepKind.elect
        · rcases hfocus ⟨0, by simp⟩ with
            ⟨focused, hfocused, _hactive⟩
          have hquota_le :=
            hquota_if_elect ⟨0, by simp⟩ focused hfocused helect
          have htally_pos :
              0 <
                fractionalActiveTally voters ballots initialWeight
                  step.beforeActive focused := by
            simpa [fractionalSTVWeightAfterSteps] using
              lt_of_lt_of_le hquota_pos hquota_le
          have hsum :=
            sum_fractionalSTVNextWeight_elect_eq_sum_sub_quota
              (voters := voters) (ballots := ballots) (quota := quota)
              (step := step) (weight := initialWeight)
              hfocused helect htally_pos.ne'
          simpa [nextWeight, helect] using hsum
        · have hsum :=
            sum_fractionalSTVNextWeight_of_kind_ne_elect
              (voters := voters) (ballots := ballots) (quota := quota)
              (step := step) (weight := initialWeight) helect
          simpa [nextWeight, helect] using hsum
      dsimp [fractionalSTVWeightAfterSteps, electStepCount]
      rw [htail, hstep_sum]
      by_cases helect : step.kind = StepKind.elect
      · simp [helect, Nat.cast_add, Nat.cast_one]
        ring
      · simp [helect]

/--
Droop-quota residual bound for a filled fractional STV run: if exactly `seats`
election rounds have occurred, then the total terminal weight is below one
Droop quota.
-/
theorem sum_fractionalSTVWeightAfterSteps_lt_STVQuota_of_electStepCount_eq
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {votersFin : Finset Voter} {ballots : Voter → Ballot Candidate}
    {steps : List (STVStep Candidate)}
    {initialWeight : Voter → ℝ} {seats voters : ℕ}
    (hinitialMass :
      (voters : ℝ) = ∑ voter ∈ votersFin, initialWeight voter)
    (helectCount : electStepCount steps = seats)
    (hfocus :
      ∀ i : Fin steps.length,
        ∃ focused, (steps.get i).focus = some focused ∧
          focused ∈ (steps.get i).beforeActive)
    (hquota_if_elect :
      ∀ i : Fin steps.length, ∀ focused,
        (steps.get i).focus = some focused →
          (steps.get i).kind = StepKind.elect →
            (STVQuota seats voters : ℝ) ≤
              fractionalActiveTally votersFin ballots
                (fractionalSTVWeightAfterSteps votersFin ballots
                  (STVQuota seats voters : ℝ)
                  (steps.take i.1) initialWeight)
                (steps.get i).beforeActive focused) :
    (∑ voter ∈ votersFin,
        fractionalSTVWeightAfterSteps votersFin ballots
          (STVQuota seats voters : ℝ) steps initialWeight voter) <
      (STVQuota seats voters : ℝ) := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  have hsum :=
    sum_fractionalSTVWeightAfterSteps_eq_sum_sub_electStepCount
      (voters := votersFin) (ballots := ballots)
      (quota := (STVQuota seats voters : ℝ)) (steps := steps)
      (initialWeight := initialWeight) hquota_pos hfocus hquota_if_elect
  have hquota_capacity :
      (voters : ℝ) < ((seats : ℝ) + 1) * (STVQuota seats voters : ℝ) := by
    have hdiv := voters_div_STVQuota_lt_seats_succ seats voters
    exact (_root_.div_lt_iff₀ hquota_pos).mp hdiv
  calc
    (∑ voter ∈ votersFin,
        fractionalSTVWeightAfterSteps votersFin ballots
          (STVQuota seats voters : ℝ) steps initialWeight voter)
        = (voters : ℝ) - (seats : ℝ) * (STVQuota seats voters : ℝ) := by
          rw [hsum, ← hinitialMass, helectCount]
    _ < (STVQuota seats voters : ℝ) := by
          nlinarith

/-- A party-specific election count is bounded by the total election count. -/
theorem partyElectStepCount_le_electStepCount {Candidate : Type*}
    [DecidableEq Candidate] (partyCandidates : Finset Candidate) :
    ∀ steps : List (STVStep Candidate),
      partyElectStepCount partyCandidates steps ≤ electStepCount steps
  | [] => by simp
  | step :: steps => by
      have htail := partyElectStepCount_le_electStepCount partyCandidates steps
      dsimp [partyElectStepCount, electStepCount]
      cases hfocus : step.focus with
      | none =>
          by_cases helect : step.kind = StepKind.elect
          · simpa [hfocus, helect] using
              Nat.le_trans htail (Nat.le_add_left _ _)
          · simp [helect, htail]
      | some focused =>
          by_cases helect : step.kind = StepKind.elect
          · by_cases hparty : focused ∈ partyCandidates
            · simp [helect, hparty, htail]
            · simpa [helect, hparty] using
                Nat.le_trans htail (Nat.le_add_left _ _)
          · simp [helect, htail]

/--
Election steps counted by two disjoint parties are bounded by the total number
of election steps in the trace.
-/
theorem partyElectStepCount_add_le_electStepCount_of_disjoint {Candidate : Type*}
    [DecidableEq Candidate] {partyCandidates otherPartyCandidates : Finset Candidate}
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates) :
    ∀ steps : List (STVStep Candidate),
      partyElectStepCount partyCandidates steps +
          partyElectStepCount otherPartyCandidates steps ≤
        electStepCount steps
  | [] => by simp
  | step :: steps => by
      have htail :=
        partyElectStepCount_add_le_electStepCount_of_disjoint
          (partyCandidates := partyCandidates)
          (otherPartyCandidates := otherPartyCandidates)
          hcandidateDisjoint steps
      dsimp [partyElectStepCount, electStepCount]
      cases hfocus : step.focus with
      | none =>
          by_cases helect : step.kind = StepKind.elect
          · simp [helect]
            omega
          · simpa [helect] using htail
      | some focused =>
          by_cases helect : step.kind = StepKind.elect
          · by_cases hparty : focused ∈ partyCandidates
            · have hnot_other : focused ∉ otherPartyCandidates := by
                exact (Finset.disjoint_left.mp hcandidateDisjoint) hparty
              simp [helect, hparty, hnot_other]
              omega
            · by_cases hother : focused ∈ otherPartyCandidates
              · simp [helect, hparty, hother]
                omega
              · simp [helect, hparty, hother]
                omega
          · simp [helect]
            omega

/--
If every election step focuses on a candidate in one of two disjoint parties,
then the two party election counters add up to the total election counter.
-/
theorem partyElectStepCount_add_eq_electStepCount_of_disjoint_of_elect_focus_mem
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates) :
    ∀ steps : List (STVStep Candidate),
      (∀ step, step ∈ steps → step.kind = StepKind.elect →
        ∃ focused, step.focus = some focused ∧
          (focused ∈ partyCandidates ∨
            focused ∈ otherPartyCandidates)) →
        partyElectStepCount partyCandidates steps +
            partyElectStepCount otherPartyCandidates steps =
          electStepCount steps
  | [], _hcover => by simp
  | step :: steps, hcover => by
      have htailCover :
          ∀ step', step' ∈ steps → step'.kind = StepKind.elect →
            ∃ focused, step'.focus = some focused ∧
              (focused ∈ partyCandidates ∨
                focused ∈ otherPartyCandidates) := by
        intro step' hstep' hkind
        exact hcover step' (by simp [hstep']) hkind
      have htail :=
        partyElectStepCount_add_eq_electStepCount_of_disjoint_of_elect_focus_mem
          (partyCandidates := partyCandidates)
          (otherPartyCandidates := otherPartyCandidates)
          hcandidateDisjoint steps htailCover
      dsimp [partyElectStepCount, electStepCount]
      cases hfocus : step.focus with
      | none =>
          by_cases helect : step.kind = StepKind.elect
          · rcases hcover step (by simp) helect with
              ⟨focused, hfocused, _hmem⟩
            simp [hfocus] at hfocused
          · simpa [hfocus, helect] using htail
      | some focused =>
          by_cases helect : step.kind = StepKind.elect
          · rcases hcover step (by simp) helect with
              ⟨focused', hfocused', hmem⟩
            have hfocused_eq : focused' = focused :=
              Option.some.inj (hfocused'.symm.trans hfocus)
            subst focused'
            rcases hmem with hparty | hother
            · have hnot_other : focused ∉ otherPartyCandidates :=
                (Finset.disjoint_left.mp hcandidateDisjoint) hparty
              simp [helect, hparty, hnot_other]
              omega
            · have hnot_party : focused ∉ partyCandidates := by
                have hsymm : Disjoint otherPartyCandidates partyCandidates :=
                  hcandidateDisjoint.symm
                exact (Finset.disjoint_left.mp hsymm) hother
              simp [helect, hnot_party, hother]
              omega
          · simpa [hfocus, helect] using htail

/--
The two party filled-seat counts decompose the total filled-seat count whenever
elected focuses and terminal fill candidates are covered by the two disjoint
candidate parties.
-/
theorem partyFilledSeatCount_add_eq_electStepCount_add_terminalFillActive_card
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatLimit : ℕ} {steps : List (STVStep Candidate)}
    {terminalActive : Finset Candidate}
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (helectFocusMem :
      ∀ step, step ∈ steps → step.kind = StepKind.elect →
        ∃ focused, step.focus = some focused ∧
          (focused ∈ partyCandidates ∨
            focused ∈ otherPartyCandidates))
    (hterminal_subset :
      terminalFillActive seatLimit steps terminalActive ⊆
        partyCandidates ∪ otherPartyCandidates) :
    partyFilledSeatCount partyCandidates seatLimit steps terminalActive +
        partyFilledSeatCount otherPartyCandidates seatLimit steps terminalActive =
      electStepCount steps +
        (terminalFillActive seatLimit steps terminalActive).card := by
  have helect :
      partyElectStepCount partyCandidates steps +
          partyElectStepCount otherPartyCandidates steps =
        electStepCount steps :=
    partyElectStepCount_add_eq_electStepCount_of_disjoint_of_elect_focus_mem
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hcandidateDisjoint steps helectFocusMem
  have hterminal :
      (activePartyCandidates
          (terminalFillActive seatLimit steps terminalActive)
          partyCandidates).card +
          (activePartyCandidates
            (terminalFillActive seatLimit steps terminalActive)
            otherPartyCandidates).card =
        (terminalFillActive seatLimit steps terminalActive).card :=
    activePartyCandidates_card_add_eq_card_of_subset_union_of_disjoint
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hcandidateDisjoint hterminal_subset
  simp [partyFilledSeatCount]
  omega

/--
The seat-limited generated simulator cannot produce more election steps than
the remaining seat budget.
-/
theorem add_electStepCount_fractionalSTVSeatRun_le_seatLimit
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ) :
    ∀ (rounds elected : ℕ) (active : Finset Candidate) (weight : Voter → ℝ),
      elected ≤ seatLimit →
        elected +
          electStepCount
            (fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVSeatRunFocuses choice voters ballots quota
                seatLimit rounds elected active weight)
              active weight) ≤ seatLimit := by
  intro rounds
  induction rounds with
  | zero =>
      intro elected active weight helected
      simpa [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps]
        using helected
  | succ rounds ih =>
      intro elected active weight helected
      by_cases hstop : seatLimit ≤ elected
      · simpa [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps, hstop]
          using helected
      · cases hchoose :
            choice.choose active
              (fractionalActiveTally voters ballots weight active) with
        | none =>
            simpa [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
              hstop, hchoose] using helected
        | some focused =>
            by_cases hfocused : focused ∈ active
            · let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let nextElected :=
                if step.kind = StepKind.elect then elected + 1 else elected
              have hnext : nextElected ≤ seatLimit := by
                by_cases helect : step.kind = StepKind.elect
                · have helected_lt : elected < seatLimit := Nat.lt_of_not_ge hstop
                  simp [nextElected, helect]
                  omega
                · simpa [nextElected, helect] using helected
              have htail :=
                ih nextElected step.afterActive
                  (fractionalSTVNextWeight voters ballots quota step weight)
                  hnext
              by_cases helect : step.kind = StepKind.elect
              · simpa [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
                  hstop, hchoose, hfocused, step, nextElected, helect,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
              · simpa [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
                  hstop, hchoose, hfocused, step, nextElected, helect,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
            · simpa [fractionalSTVSeatRunFocuses, fractionalSTVGeneratedSteps,
                hstop, hchoose, hfocused] using helected

/-- Election steps of a zero-initial seat-limited generated run are bounded by the limit. -/
theorem electStepCount_fractionalSTVSeatRunTrace_le_seatLimit
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) :
    electStepCount
        (fractionalSTVSeatRunTrace choice voters ballots quota seatLimit rounds
          0 initialActive initialWeight).steps ≤ seatLimit := by
  have h :=
    add_electStepCount_fractionalSTVSeatRun_le_seatLimit choice voters ballots
      quota seatLimit rounds 0 initialActive initialWeight
      (Nat.zero_le seatLimit)
  simpa [fractionalSTVSeatRunTrace, fractionalSTVGeneratedTrace] using h

/--
The party election steps of a seat-limited generated run are bounded by the
remaining seat budget.
-/
theorem add_partyElectStepCount_fractionalSTVSeatRun_le_seatLimit
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit : ℕ) (partyCandidates : Finset Candidate) :
    ∀ (rounds elected : ℕ) (active : Finset Candidate) (weight : Voter → ℝ),
      elected ≤ seatLimit →
        elected +
          partyElectStepCount partyCandidates
            (fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVSeatRunFocuses choice voters ballots quota
                seatLimit rounds elected active weight)
              active weight) ≤ seatLimit := by
  intro rounds elected active weight helected
  have hparty_le :
      partyElectStepCount partyCandidates
          (fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVSeatRunFocuses choice voters ballots quota
              seatLimit rounds elected active weight)
            active weight) ≤
        electStepCount
          (fractionalSTVGeneratedSteps voters ballots quota
            (fractionalSTVSeatRunFocuses choice voters ballots quota
              seatLimit rounds elected active weight)
            active weight) :=
    partyElectStepCount_le_electStepCount partyCandidates _
  have htotal :=
    add_electStepCount_fractionalSTVSeatRun_le_seatLimit choice voters ballots
      quota seatLimit rounds elected active weight helected
  omega

/-- Party election steps of a zero-initial seat-limited generated run are bounded by the limit. -/
theorem partyElectStepCount_fractionalSTVSeatRunTrace_le_seatLimit
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seatLimit rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) (partyCandidates : Finset Candidate) :
    partyElectStepCount partyCandidates
        (fractionalSTVSeatRunTrace choice voters ballots quota seatLimit rounds
          0 initialActive initialWeight).steps ≤ seatLimit := by
  have h :=
    add_partyElectStepCount_fractionalSTVSeatRun_le_seatLimit choice voters
      ballots quota seatLimit partyCandidates rounds 0 initialActive
      initialWeight (Nat.zero_le seatLimit)
  simpa [fractionalSTVSeatRunTrace, fractionalSTVGeneratedTrace] using h

/--
The party-seat-limited generated simulator cannot produce more same-party
election steps than the remaining same-party seat budget.
-/
theorem add_partyElectStepCount_fractionalSTVPartySeatRun_le_partySeatLimit
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit : ℕ) :
    ∀ (rounds partyElected : ℕ) (active : Finset Candidate)
      (weight : Voter → ℝ),
      partyElected ≤ partySeatLimit →
        partyElected +
          partyElectStepCount partyCandidates
            (fractionalSTVGeneratedSteps voters ballots quota
              (fractionalSTVPartySeatRunFocuses choice voters ballots quota
                partyCandidates partySeatLimit rounds partyElected active weight)
              active weight) ≤ partySeatLimit := by
  intro rounds
  induction rounds with
  | zero =>
      intro partyElected active weight helected
      simpa [fractionalSTVPartySeatRunFocuses, fractionalSTVGeneratedSteps]
        using helected
  | succ rounds ih =>
      intro partyElected active weight helected
      by_cases hstop : partySeatLimit ≤ partyElected
      · simpa [fractionalSTVPartySeatRunFocuses, fractionalSTVGeneratedSteps,
          hstop] using helected
      · cases hchoose :
            choice.choose active
              (fractionalActiveTally voters ballots weight active) with
        | none =>
            simpa [fractionalSTVPartySeatRunFocuses,
              fractionalSTVGeneratedSteps, hstop, hchoose] using helected
        | some focused =>
            by_cases hfocused : focused ∈ active
            · let step :=
                fractionalSTVStepFromFocus voters ballots quota active weight
                  focused
              let partyElection :=
                step.kind = StepKind.elect ∧ focused ∈ partyCandidates
              let nextPartyElected :=
                if partyElection then partyElected + 1 else partyElected
              have hnext : nextPartyElected ≤ partySeatLimit := by
                by_cases hpartyElection : partyElection
                · have helected_lt :
                      partyElected < partySeatLimit := Nat.lt_of_not_ge hstop
                  simp [nextPartyElected, hpartyElection]
                  omega
                · simpa [nextPartyElected, hpartyElection] using helected
              have htail :=
                ih nextPartyElected step.afterActive
                  (fractionalSTVNextWeight voters ballots quota step weight)
                  hnext
              by_cases hpartyElection : partyElection
              · rcases hpartyElection with ⟨helect, hparty⟩
                simpa [fractionalSTVPartySeatRunFocuses,
                  fractionalSTVGeneratedSteps, hstop, hchoose, hfocused, step,
                  partyElection, nextPartyElected, helect, hparty,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
              · have hnot_indicator :
                    ¬ (step.kind = StepKind.elect ∧
                        focused ∈ partyCandidates) := hpartyElection
                simpa [fractionalSTVPartySeatRunFocuses,
                  fractionalSTVGeneratedSteps, hstop, hchoose, hfocused, step,
                  partyElection, nextPartyElected, hnot_indicator,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
            · simpa [fractionalSTVPartySeatRunFocuses,
                fractionalSTVGeneratedSteps, hstop, hchoose, hfocused]
                using helected

/--
Same-party election steps of a zero-initial party-seat-limited generated run
are bounded by its party seat limit.
-/
theorem partyElectStepCount_fractionalSTVPartySeatRunTrace_le_partySeatLimit
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (partyCandidates : Finset Candidate)
    (partySeatLimit rounds : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ) :
    partyElectStepCount partyCandidates
        (fractionalSTVPartySeatRunTrace choice voters ballots quota
          partyCandidates partySeatLimit rounds 0 initialActive
          initialWeight).steps ≤ partySeatLimit := by
  have h :=
    add_partyElectStepCount_fractionalSTVPartySeatRun_le_partySeatLimit
      choice voters ballots quota partyCandidates partySeatLimit rounds 0
      initialActive initialWeight (Nat.zero_le partySeatLimit)
  simpa [fractionalSTVPartySeatRunTrace, fractionalSTVGeneratedTrace] using h

/--
Trace-prefix party-weight accounting: under the recursive fractional transfer
dynamics, the party voter group's total weight after a prefix is the initial
weight minus one quota for each same-party election step in that prefix.
-/
theorem sum_fractionalSTVWeightAfterSteps_eq_sum_sub_partyElectStepCount
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hquota_pos : 0 < quota)
    (hlaw :
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps initialWeight) :
    (∑ voter ∈ voters,
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter) =
      (∑ voter ∈ voters, initialWeight voter) -
        (partyElectStepCount partyCandidates steps : ℝ) * quota := by
  induction steps generalizing initialWeight with
  | nil =>
      simp [fractionalSTVWeightAfterSteps, partyElectStepCount]
  | cons step steps ih =>
      rcases hlaw with ⟨hstep, hrest⟩
      dsimp [fractionalSTVWeightAfterSteps, partyElectStepCount]
      rw [ih hrest]
      have hstep_sum :
          (∑ voter ∈ voters,
              fractionalSTVNextWeight voters ballots quota step
                initialWeight voter) =
            (∑ voter ∈ voters, initialWeight voter) -
              (match step.focus with
              | none => 0
              | some focused =>
                  if step.kind = StepKind.elect ∧
                      focused ∈ partyCandidates then
                    quota
                  else
                    0) :=
        sum_fractionalSTVNextWeight_eq_sum_sub_partyElectStepIndicator
          (voters := voters) (ballots := ballots)
          (partyCandidates := partyCandidates) (quota := quota)
          (step := step) (weight := initialWeight) hquota_pos hstep
      rw [hstep_sum]
      cases hfocus : step.focus with
      | none =>
          simp
      | some focused =>
          by_cases hparty : focused ∈ partyCandidates
          · cases hkind : step.kind
            all_goals
              simp [hparty, Nat.cast_add, Nat.cast_one]
              try ring
          · cases hkind : step.kind
            all_goals simp [hparty]

theorem sum_fractionalSTVWeightAfterSteps_lt_quota_of_residual_lt
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hquota_pos : 0 < quota)
    (hinitial :
      initialVotes = ∑ voter ∈ voters, initialWeight voter)
    (hlaw :
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps initialWeight)
    (hresidual :
      initialVotes - (partyElectStepCount partyCandidates steps : ℝ) * quota <
        quota) :
    (∑ voter ∈ voters,
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter) < quota := by
  rw [sum_fractionalSTVWeightAfterSteps_eq_sum_sub_partyElectStepCount
    hquota_pos hlaw]
  rw [← hinitial]
  exact hresidual

/--
Terminal concrete party weight below quota implies the residual inequality
used by the same-party quota process.
-/
theorem residual_lt_quota_of_sum_fractionalSTVWeightAfterSteps_lt
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hquota_pos : 0 < quota)
    (hinitial :
      initialVotes = ∑ voter ∈ voters, initialWeight voter)
    (hlaw :
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps initialWeight)
    (hterminal :
      (∑ voter ∈ voters,
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter) < quota) :
    initialVotes - (partyElectStepCount partyCandidates steps : ℝ) * quota <
      quota := by
  have hsum :
      (∑ voter ∈ voters,
          fractionalSTVWeightAfterSteps voters ballots quota steps
            initialWeight voter) =
        (∑ voter ∈ voters, initialWeight voter) -
          (partyElectStepCount partyCandidates steps : ℝ) * quota :=
    sum_fractionalSTVWeightAfterSteps_eq_sum_sub_partyElectStepCount
      (voters := voters) (ballots := ballots)
      (partyCandidates := partyCandidates) (quota := quota)
      (steps := steps) (initialWeight := initialWeight) hquota_pos hlaw
  calc
    initialVotes - (partyElectStepCount partyCandidates steps : ℝ) * quota
        =
        (∑ voter ∈ voters, initialWeight voter) -
          (partyElectStepCount partyCandidates steps : ℝ) * quota := by
          rw [hinitial]
    _ =
        ∑ voter ∈ voters,
          fractionalSTVWeightAfterSteps voters ballots quota steps
            initialWeight voter := by
          rw [hsum]
    _ < quota := hterminal

/--
If every voter in a group has a first active candidate in a party, then the
party's active fractional tally mass equals the total current weight of those
voters.
-/
theorem partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {active partyCandidates : Finset Candidate}
    (hnext :
      ∀ voter, voter ∈ voters →
        ∃ candidate,
          candidate ∈ activePartyCandidates active partyCandidates ∧
            Ballot.nextActive (ballots voter) active = some candidate) :
    partyFractionalTallyMass partyCandidates
        (fractionalActiveTally voters ballots weight active) active =
      ∑ voter ∈ voters, weight voter := by
  classical
  dsimp [partyFractionalTallyMass, fractionalActiveTally,
    Ballot.activeSupport]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro voter hvoter
  rcases hnext voter hvoter with ⟨candidate, hcandidate, hnextActive⟩
  calc
    (∑ x ∈ activePartyCandidates active partyCandidates,
        if Ballot.nextActive (ballots voter) active = some x then
          weight voter
        else
          0) =
        (if Ballot.nextActive (ballots voter) active = some candidate then
          weight voter
        else
          0) := by
        apply Finset.sum_eq_single_of_mem candidate
        · exact hcandidate
        · intro other _hother hother_ne
          have hnot :
              ¬ Ballot.nextActive (ballots voter) active = some other := by
            intro hother_next
            exact hother_ne
              (Option.some.inj (hother_next.symm.trans hnextActive))
          simp [hnot]
    _ = weight voter := by
        simp [hnextActive]

/--
Solid-coalition ballots give the weighted active-tally mass identity whenever
the party still has an active candidate.
-/
theorem partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights_of_solidCoalition
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {active partyCandidates : Finset Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hpartyActive : ∃ same, same ∈ partyCandidates ∧ same ∈ active) :
    partyFractionalTallyMass partyCandidates
        (fractionalActiveTally voters ballots weight active) active =
      ∑ voter ∈ voters, weight voter := by
  exact partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights
    (voters := voters) (ballots := ballots) (weight := weight)
    (active := active) (partyCandidates := partyCandidates) (by
      intro voter hvoter
      rcases SolidCoalitionBallots.nextActive_mem_party
          hsolid hvoter hpartyActive with
        ⟨same, hsame_party, hsame_active, hnext⟩
      exact ⟨same, by
        simp [activePartyCandidates, hsame_active, hsame_party], hnext⟩)

/--
Concrete source law for one fractional STV step, before projecting to any
party: the step removes an active focused candidate, active tallies are
nonnegative, each ordinary round is an election or elimination, and an election
focus meets quota.
-/
def FractionalSTVConcreteStepLaw {Candidate : Type*}
    [DecidableEq Candidate] (fractionalTally : Candidate → ℝ) (quota : ℝ)
    (step : STVStep Candidate) : Prop :=
  step.removesFocusedCandidate ∧
    ∃ focused, step.focus = some focused ∧
      focused ∈ step.beforeActive ∧
      (∀ candidate, candidate ∈ step.beforeActive →
        0 ≤ fractionalTally candidate) ∧
      (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) ∧
      (step.kind = StepKind.elect → quota ≤ fractionalTally focused)

/--
Weighted-ballot step facts construct the concrete fractional STV step law for
the active-support tally induced by the current voter weights.
-/
theorem fractionalSTVConcreteStepLaw_of_weightedActiveTally
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {quota : ℝ} {step : STVStep Candidate}
    (hremove : step.removesFocusedCandidate)
    {focused : Candidate} (hfocus : step.focus = some focused)
    (hfocused_active : focused ∈ step.beforeActive)
    (hweight_nonneg : ∀ voter, voter ∈ voters → 0 ≤ weight voter)
    (hkind_allowed : step.kind = StepKind.elect ∨
      step.kind = StepKind.eliminate)
    (hquota_if_elect :
      step.kind = StepKind.elect →
        quota ≤
          fractionalActiveTally voters ballots weight step.beforeActive
            focused) :
    FractionalSTVConcreteStepLaw
      (fractionalActiveTally voters ballots weight step.beforeActive)
      quota step := by
  exact ⟨hremove, focused, hfocus, hfocused_active,
    (by
      intro candidate _hactive
      exact fractionalActiveTally_nonneg
        (voters := voters) (ballots := ballots) (weight := weight)
        (active := step.beforeActive) hweight_nonneg candidate),
    hkind_allowed, hquota_if_elect⟩

/--
Weighted-ballot step facts construct the concrete fractional STV step law for
an arbitrary fractional tally that agrees with the weighted active-support
tally on active candidates.
-/
theorem fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {fractionalTally : Candidate → ℝ}
    {quota : ℝ} {step : STVStep Candidate}
    (hremove : step.removesFocusedCandidate)
    {focused : Candidate} (hfocus : step.focus = some focused)
    (hfocused_active : focused ∈ step.beforeActive)
    (hweight_nonneg : ∀ voter, voter ∈ voters → 0 ≤ weight voter)
    (htally_eq :
      ∀ candidate, candidate ∈ step.beforeActive →
        fractionalTally candidate =
          fractionalActiveTally voters ballots weight step.beforeActive
            candidate)
    (hkind_allowed : step.kind = StepKind.elect ∨
      step.kind = StepKind.eliminate)
    (hquota_if_elect :
      step.kind = StepKind.elect →
        quota ≤
          fractionalActiveTally voters ballots weight step.beforeActive
            focused) :
    FractionalSTVConcreteStepLaw fractionalTally quota step := by
  refine ⟨hremove, focused, hfocus, hfocused_active, ?_,
    hkind_allowed, ?_⟩
  · intro candidate hcandidate
    rw [htally_eq candidate hcandidate]
    exact fractionalActiveTally_nonneg
      (voters := voters) (ballots := ballots) (weight := weight)
      (active := step.beforeActive) hweight_nonneg candidate
  · intro helect
    rw [htally_eq focused hfocused_active]
    exact hquota_if_elect helect

namespace FractionalSTVIndexedExecutableTrace

/--
An indexed executable trace discharges the concrete candidate-level source
step law at every generated round.
-/
theorem concreteStepLaw {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    (run :
      FractionalSTVIndexedExecutableTrace trace voters ballots quota
        initialActive terminalActive initialWeight) :
    ∀ i : Fin trace.steps.length,
      FractionalSTVConcreteStepLaw
        (run.roundTally i) quota (trace.steps.get i) := by
  intro i
  rcases run.step_focus_active i with ⟨focused, hfocus, hfocused_active⟩
  exact fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
    (voters := voters) (ballots := ballots)
    (weight :=
      fractionalSTVWeightAfterSteps voters ballots quota
        (trace.steps.take i.1) initialWeight)
    (fractionalTally := run.roundTally i)
    (quota := quota) (step := trace.steps.get i)
    (run.step_removes i) hfocus hfocused_active
    (fractionalSTVWeightAfterSteps_take_nonneg
      (voters := voters) (ballots := ballots) (quota := quota)
      (steps := trace.steps) (initialWeight := initialWeight)
      run.initialWeight_nonneg run.quota_pos run.quota_if_elect i.1)
    (run.tally_eq i) (run.kind_allowed i)
    (run.quota_if_elect i focused hfocus)

/--
If the initial active set is covered by two candidate parties, then every
indexed focus in an executable fractional STV trace belongs to one of them.
-/
theorem focus_mem_of_initialActive_subset_union {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (run :
      FractionalSTVIndexedExecutableTrace trace voters ballots quota
        initialActive terminalActive initialWeight)
    (hinitial_subset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (i : Fin trace.steps.length) :
    ∃ focused, (trace.steps.get i).focus = some focused ∧
      (focused ∈ partyCandidates ∨ focused ∈ otherPartyCandidates) := by
  rcases run.step_focus_active i with ⟨focused, hfocus, hfocused_active⟩
  have hremove_mem :
      ∀ step, step ∈ trace.steps → step.removesFocusedCandidate := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact run.step_removes ⟨n, hn⟩
  have hbefore_subset :
      (trace.steps.get i).beforeActive ⊆ initialActive :=
    STVTrace.beforeActive_subset_startActive_of_replaysFrom_removesFocusedCandidate
      run.activeReplay hremove_mem i
  have hfocused_initial : focused ∈ initialActive :=
    hbefore_subset hfocused_active
  have hfocused_union :
      focused ∈ partyCandidates ∪ otherPartyCandidates :=
    hinitial_subset hfocused_initial
  exact ⟨focused, hfocus, by simpa using hfocused_union⟩

/--
List-level form: under an initial two-party candidate cover, every election
step in an executable fractional STV trace focuses on one of the two parties.
-/
theorem elect_focus_mem_of_initialActive_subset_union {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (run :
      FractionalSTVIndexedExecutableTrace trace voters ballots quota
        initialActive terminalActive initialWeight)
    (hinitial_subset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.elect →
      ∃ focused, step.focus = some focused ∧
        (focused ∈ partyCandidates ∨
          focused ∈ otherPartyCandidates) := by
  intro step hstep _helect
  rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
  subst hget
  exact focus_mem_of_initialActive_subset_union
    (partyCandidates := partyCandidates)
    (otherPartyCandidates := otherPartyCandidates)
    run hinitial_subset ⟨n, hn⟩

end FractionalSTVIndexedExecutableTrace

/--
Concrete candidate-level STV step laws plus solid-coalition tally agreement
construct the source-level party weight trace law.

This is the reusable bridge from the executable fractional transfer
implementation to the party-isolated accounting law used by STV quota proofs.
-/
theorem fractionalSTVPartyWeightTraceLaw_of_concreteStepLaw_solidCoalition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (hpartyActive :
      ∀ i : Fin steps.length,
        ∃ same, same ∈ partyCandidates ∧ same ∈ (steps.get i).beforeActive)
    (htallyEq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ activePartyCandidates (steps.get i).beforeActive
            partyCandidates →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally voters ballots
              (fractionalSTVWeightAfterSteps voters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate) :
    FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
      steps initialWeight := by
  apply fractionalSTVPartyWeightTraceLaw_of_getElem
  intro i
  constructor
  · intro focused hfocus helect hfocused_party
    rcases htraceSteps i with
      ⟨_hremove, concreteFocused, hconcreteFocus, hfocused_active,
        _hnonneg, _hkind_allowed, hquota_if_elect⟩
    have hfocused_eq : concreteFocused = focused :=
      Option.some.inj (hconcreteFocus.symm.trans hfocus)
    subst concreteFocused
    have hactive_party :
        focused ∈ activePartyCandidates (steps.get i).beforeActive
          partyCandidates := by
      exact Finset.mem_filter.mpr ⟨hfocused_active, hfocused_party⟩
    have hquota_rule : quota ≤ fractionalTally (steps.get i) focused :=
      hquota_if_elect helect
    rw [htallyEq i focused hactive_party] at hquota_rule
    exact hquota_rule
  · intro focused _hfocus _helect hfocused_not_party
    exact activeSupport_eq_empty_of_solidCoalitionBallots_outside
      hsolid (hpartyActive i) hfocused_not_party

/--
Indexed concrete candidate-level STV step laws plus solid-coalition tally
agreement construct the source-level party weight trace law.

This is the simulator-facing variant of
`fractionalSTVPartyWeightTraceLaw_of_concreteStepLaw_solidCoalition`: the
real-valued tally is indexed by round instead of keyed by the `STVStep` value.
-/
theorem fractionalSTVPartyWeightTraceLaw_of_indexedConcreteStepLaw_solidCoalition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    {roundTally : Fin steps.length → Candidate → ℝ}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw (roundTally i) quota (steps.get i))
    (hpartyActive :
      ∀ i : Fin steps.length,
        ∃ same, same ∈ partyCandidates ∧ same ∈ (steps.get i).beforeActive)
    (htallyEq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ activePartyCandidates (steps.get i).beforeActive
            partyCandidates →
          roundTally i candidate =
            fractionalActiveTally voters ballots
              (fractionalSTVWeightAfterSteps voters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate) :
    FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
      steps initialWeight := by
  apply fractionalSTVPartyWeightTraceLaw_of_getElem
  intro i
  constructor
  · intro focused hfocus helect hfocused_party
    rcases htraceSteps i with
      ⟨_hremove, concreteFocused, hconcreteFocus, hfocused_active,
        _hnonneg, _hkind_allowed, hquota_if_elect⟩
    have hfocused_eq : concreteFocused = focused :=
      Option.some.inj (hconcreteFocus.symm.trans hfocus)
    subst concreteFocused
    have hactive_party :
        focused ∈ activePartyCandidates (steps.get i).beforeActive
          partyCandidates := by
      exact Finset.mem_filter.mpr ⟨hfocused_active, hfocused_party⟩
    have hquota_rule : quota ≤ roundTally i focused :=
      hquota_if_elect helect
    rw [htallyEq i focused hactive_party] at hquota_rule
    exact hquota_rule
  · intro focused _hfocus _helect hfocused_not_party
    exact activeSupport_eq_empty_of_solidCoalitionBallots_outside
      hsolid (hpartyActive i) hfocused_not_party

/--
Executable fractional STV trace certificate.

The concrete implementation content is the recursive weight fold
`fractionalSTVWeightAfterSteps`: each trace step's real-valued tally is required
to be exactly the first-active tally induced by the weights obtained by
executing all previous steps.  The remaining fields state the ordinary
candidate-level round facts supplied by the trace generator or tie-breaker.
-/
structure FractionalSTVExecutableTrace {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (voters : Finset Voter)
    (ballots : Voter → Ballot Candidate) (quota : ℝ)
    (initialActive terminalActive : Finset Candidate)
    (initialWeight : Voter → ℝ) where
  quota_pos : 0 < quota
  step_removes :
    ∀ i : Fin trace.steps.length,
      (trace.steps.get i).removesFocusedCandidate
  step_focus_active :
    ∀ i : Fin trace.steps.length,
      ∃ focused, (trace.steps.get i).focus = some focused ∧
        focused ∈ (trace.steps.get i).beforeActive
  initialWeight_nonneg :
    ∀ voter, voter ∈ voters → 0 ≤ initialWeight voter
  tally_eq :
    ∀ i : Fin trace.steps.length, ∀ candidate,
      candidate ∈ (trace.steps.get i).beforeActive →
        rule.fractionalTally (trace.steps.get i) candidate =
          fractionalActiveTally voters ballots
            (fractionalSTVWeightAfterSteps voters ballots quota
              (trace.steps.take i.1) initialWeight)
            (trace.steps.get i).beforeActive candidate
  kind_allowed :
    ∀ i : Fin trace.steps.length,
      (trace.steps.get i).kind = StepKind.elect ∨
        (trace.steps.get i).kind = StepKind.eliminate
  quota_if_elect :
    ∀ i : Fin trace.steps.length, ∀ focused,
      (trace.steps.get i).focus = some focused →
        (trace.steps.get i).kind = StepKind.elect →
          quota ≤
            fractionalActiveTally voters ballots
              (fractionalSTVWeightAfterSteps voters ballots quota
                (trace.steps.take i.1) initialWeight)
              (trace.steps.get i).beforeActive focused
  activeReplay : trace.replaysFrom initialActive terminalActive

namespace FractionalSTVExecutableTrace

/--
An executable fractional trace discharges the candidate-level concrete source
step law for every indexed trace step.
-/
theorem concreteStepLaw {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    (run :
      FractionalSTVExecutableTrace rule trace voters ballots quota
        initialActive terminalActive initialWeight) :
    ∀ i : Fin trace.steps.length,
      FractionalSTVConcreteStepLaw
        (rule.fractionalTally (trace.steps.get i)) quota
        (trace.steps.get i) := by
  intro i
  rcases run.step_focus_active i with ⟨focused, hfocus, hfocused_active⟩
  exact fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
    (voters := voters) (ballots := ballots)
    (weight :=
      fractionalSTVWeightAfterSteps voters ballots quota
        (trace.steps.take i.1) initialWeight)
    (fractionalTally := rule.fractionalTally (trace.steps.get i))
    (quota := quota) (step := trace.steps.get i)
    (run.step_removes i) hfocus hfocused_active
    (fractionalSTVWeightAfterSteps_take_nonneg
      (voters := voters) (ballots := ballots) (quota := quota)
      (steps := trace.steps) (initialWeight := initialWeight)
      run.initialWeight_nonneg run.quota_pos run.quota_if_elect i.1)
    (run.tally_eq i) (run.kind_allowed i)
    (run.quota_if_elect i focused hfocus)

/-- Active-set replay prefixes for every indexed step of an executable trace. -/
theorem prefixReplay {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    (run :
      FractionalSTVExecutableTrace rule trace voters ballots quota
        initialActive terminalActive initialWeight) :
    ∀ i : Fin trace.steps.length,
      STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
        (trace.steps.get i).beforeActive := by
  intro i
  exact STVTrace.replaysFrom_take_get_beforeActive run.activeReplay i

/--
Restrict an executable fractional STV trace certificate to a finite prefix.

The caller supplies the active-set replay endpoint for the prefix; all
candidate-level executable facts are inherited from the original trace.
-/
theorem of_take {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive prefixTerminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    (run :
      FractionalSTVExecutableTrace rule trace voters ballots quota
        initialActive terminalActive initialWeight)
    (n : ℕ)
    (hreplay :
      STVTrace.replayStepsFrom (trace.steps.take n) initialActive
        prefixTerminalActive) :
    FractionalSTVExecutableTrace rule
      ({ steps := trace.steps.take n } : STVTrace Candidate)
      voters ballots quota initialActive prefixTerminalActive initialWeight where
  quota_pos := run.quota_pos
  step_removes := by
    intro i
    have hlen : (trace.steps.take n).length ≤ trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    simpa [List.get_eq_getElem, List.getElem_take] using
      run.step_removes ⟨i.1, hi⟩
  step_focus_active := by
    intro i
    have hlen : (trace.steps.take n).length ≤ trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    simpa [List.get_eq_getElem, List.getElem_take] using
      run.step_focus_active ⟨i.1, hi⟩
  initialWeight_nonneg := run.initialWeight_nonneg
  tally_eq := by
    intro i candidate hcandidate
    have hlen : (trace.steps.take n).length ≤ trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    have hcandidate' :
        candidate ∈ (trace.steps.get ⟨i.1, hi⟩).beforeActive := by
      simpa [List.get_eq_getElem, List.getElem_take] using hcandidate
    have htally := run.tally_eq ⟨i.1, hi⟩ candidate hcandidate'
    have hi_le_n : i.1 ≤ n := by
      have hi_min : i.1 < min n trace.steps.length := by
        simpa [List.length_take] using i.2
      exact Nat.le_of_lt (lt_of_lt_of_le hi_min (Nat.min_le_left _ _))
    simpa [List.get_eq_getElem, List.getElem_take, List.take_take,
      Nat.min_eq_left hi_le_n] using htally
  kind_allowed := by
    intro i
    have hlen : (trace.steps.take n).length ≤ trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    simpa [List.get_eq_getElem, List.getElem_take] using
      run.kind_allowed ⟨i.1, hi⟩
  quota_if_elect := by
    intro i focused hfocus hkind
    have hlen : (trace.steps.take n).length ≤ trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    have hfocus' :
        (trace.steps.get ⟨i.1, hi⟩).focus = some focused := by
      simpa [List.get_eq_getElem, List.getElem_take] using hfocus
    have hkind' :
        (trace.steps.get ⟨i.1, hi⟩).kind = StepKind.elect := by
      simpa [List.get_eq_getElem, List.getElem_take] using hkind
    have hquota := run.quota_if_elect ⟨i.1, hi⟩ focused hfocus' hkind'
    have hi_le_n : i.1 ≤ n := by
      have hi_min : i.1 < min n trace.steps.length := by
        simpa [List.length_take] using i.2
      exact Nat.le_of_lt (lt_of_lt_of_le hi_min (Nat.min_le_left _ _))
    simpa [List.get_eq_getElem, List.getElem_take, List.take_take,
      Nat.min_eq_left hi_le_n] using hquota
  activeReplay := hreplay

end FractionalSTVExecutableTrace

/--
No-quota elimination facts restrict from a trace to any finite prefix.

This is the routine index transport used by source-step prefix arguments: if
the full candidate-level trace has every active same-party candidate below
quota on elimination rounds, the same fact holds for `steps.take n`.
-/
theorem noquotaOnEliminate_take_of_noquotaOnEliminate
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {steps : List (STVStep Candidate)} {partyCandidates : Finset Candidate}
    {quota : ℝ} {n : ℕ}
    (hnoquota :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (steps.get i) candidate < quota) :
    ∀ i : Fin (steps.take n).length,
      ((steps.take n).get i).kind = StepKind.eliminate →
        ∀ candidate,
          candidate ∈
              activePartyCandidates ((steps.take n).get i).beforeActive
                partyCandidates →
            rule.fractionalTally ((steps.take n).get i) candidate < quota := by
  intro i hkind candidate hcandidate
  have hlen : (steps.take n).length ≤ steps.length := by
    simp [List.length_take]
  have hi : i.1 < steps.length := lt_of_lt_of_le i.2 hlen
  have hkind_full :
      (steps.get ⟨i.1, hi⟩).kind = StepKind.eliminate := by
    simpa [List.get_eq_getElem, List.getElem_take] using hkind
  have hcandidate_full :
      candidate ∈
          activePartyCandidates (steps.get ⟨i.1, hi⟩).beforeActive
            partyCandidates := by
    simpa [List.get_eq_getElem, List.getElem_take] using hcandidate
  simpa [List.get_eq_getElem, List.getElem_take] using
    hnoquota ⟨i.1, hi⟩ hkind_full candidate hcandidate_full

/--
Turn an indexed simulator certificate into a rule-keyed executable trace when
the concrete transfer rule agrees with the simulator's round tally on
active candidates.
-/
def fractionalSTVExecutableTrace_of_indexedRoundTallyEq
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {trace : STVTrace Candidate} {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {quota : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ}
    (run :
      FractionalSTVIndexedExecutableTrace trace voters ballots quota
        initialActive terminalActive initialWeight)
    (htally_eq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            run.roundTally i candidate) :
    FractionalSTVExecutableTrace rule trace voters ballots quota
      initialActive terminalActive initialWeight where
  quota_pos := run.quota_pos
  step_removes := run.step_removes
  step_focus_active := run.step_focus_active
  initialWeight_nonneg := run.initialWeight_nonneg
  tally_eq := by
    intro i candidate hcandidate
    exact (htally_eq i candidate hcandidate).trans
      (run.tally_eq i candidate hcandidate)
  kind_allowed := run.kind_allowed
  quota_if_elect := run.quota_if_elect
  activeReplay := run.activeReplay

/--
Two-party executable fractional STV source certificate.

This packages the source-model facts normally produced by an executable STV
run: the global recursive transfer trace, the voter/candidate partition,
solid-coalition inputs, initial party weights, and final party residual/count
facts.  Paper-facing theorems should consume this kind of object instead of a
pre-built replay/process certificate.
-/
structure FractionalSTVTwoPartyExecutableTrace {Voter Candidate : Type*}
    [DecidableEq Voter] [DecidableEq Candidate]
    (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (allVoters partyVoters otherPartyVoters :
      Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (quota partyInitialVotes otherPartyInitialVotes : ℝ)
    (initialActive terminalActive : Finset Candidate)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    (partyFinalSeats otherPartyFinalSeats : ℕ) where
  executableTrace :
    FractionalSTVExecutableTrace rule trace allVoters ballots quota
      initialActive terminalActive initialWeight
  voterPartition : allVoters = partyVoters ∪ otherPartyVoters
  voterDisjoint : Disjoint partyVoters otherPartyVoters
  candidateDisjoint : Disjoint partyCandidates otherPartyCandidates
  partySolid : SolidCoalitionBallots partyVoters ballots partyCandidates
  otherPartySolid :
    SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates
  partyInitialActive : partyCandidates ⊆ initialActive
  otherPartyInitialActive : otherPartyCandidates ⊆ initialActive
  partyInitialWeight_eq :
    ∀ voter, voter ∈ partyVoters →
      initialWeight voter = partyInitialWeight voter
  otherPartyInitialWeight_eq :
    ∀ voter, voter ∈ otherPartyVoters →
      initialWeight voter = otherPartyInitialWeight voter
  partyInitialMass :
    partyInitialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter
  otherPartyInitialMass :
    otherPartyInitialVotes =
      ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter
  partyActive :
    ∀ i : Fin trace.steps.length,
      ∃ same, same ∈ partyCandidates ∧
        same ∈ (trace.steps.get i).beforeActive
  otherPartyActive :
    ∀ i : Fin trace.steps.length,
      ∃ same, same ∈ otherPartyCandidates ∧
        same ∈ (trace.steps.get i).beforeActive
  partyResidualBelowQuota :
    partyInitialVotes -
        (partyElectStepCount partyCandidates trace.steps : ℝ) * quota <
      quota
  otherPartyResidualBelowQuota :
    otherPartyInitialVotes -
        (partyElectStepCount otherPartyCandidates trace.steps : ℝ) * quota <
      quota
  partyElectCount_le_finalSeats :
    partyElectStepCount partyCandidates trace.steps ≤ partyFinalSeats
  otherPartyElectCount_le_finalSeats :
    partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartyFinalSeats

/--
The party projection state represented by a source STV step: remaining
candidates and vote mass agree with the active same-party candidates and their
fractional tallies.
-/
def FractionalPartySTVProjectionStateLaw {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (fractionalTally : Candidate → ℝ)
    (step : STVStep Candidate) (before : PartyQuotaState) : Prop :=
  before.remainingCandidates =
      (activePartyCandidates step.beforeActive partyCandidates).card ∧
    before.voteMass =
      partyFractionalTallyMass partyCandidates fractionalTally
        step.beforeActive

/--
Solid-coalition weighted ballots construct the party projection-state law once
the party process state is known to track active same-party candidate count and
current total same-party voter weight.
-/
theorem fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {partyCandidates : Finset Candidate}
    {step : STVStep Candidate} {before : PartyQuotaState}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hpartyActive :
      ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive)
    (hremaining :
      before.remainingCandidates =
        (activePartyCandidates step.beforeActive partyCandidates).card)
    (hmass : before.voteMass = ∑ voter ∈ voters, weight voter) :
    FractionalPartySTVProjectionStateLaw partyCandidates
      (fractionalActiveTally voters ballots weight step.beforeActive)
      step before := by
  refine ⟨hremaining, ?_⟩
  rw [hmass]
  exact
    (partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights_of_solidCoalition
      (voters := voters) (ballots := ballots) (weight := weight)
      (active := step.beforeActive) (partyCandidates := partyCandidates)
      hsolid hpartyActive).symm

/--
Variant of `fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass`
for an arbitrary fractional tally that agrees with the weighted active-support
tally on active same-party candidates.
-/
theorem fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass_of_tally_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {weight : Voter → ℝ} {partyCandidates : Finset Candidate}
    {fractionalTally : Candidate → ℝ}
    {step : STVStep Candidate} {before : PartyQuotaState}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates)
    (hpartyActive :
      ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive)
    (htally_eq :
      ∀ candidate,
        candidate ∈ activePartyCandidates step.beforeActive partyCandidates →
          fractionalTally candidate =
            fractionalActiveTally voters ballots weight step.beforeActive
              candidate)
    (hremaining :
      before.remainingCandidates =
        (activePartyCandidates step.beforeActive partyCandidates).card)
    (hmass : before.voteMass = ∑ voter ∈ voters, weight voter) :
    FractionalPartySTVProjectionStateLaw partyCandidates fractionalTally
      step before := by
  refine ⟨hremaining, ?_⟩
  have hweighted :
      partyFractionalTallyMass partyCandidates
          (fractionalActiveTally voters ballots weight step.beforeActive)
          step.beforeActive =
        ∑ voter ∈ voters, weight voter :=
    partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights_of_solidCoalition
      (voters := voters) (ballots := ballots) (weight := weight)
      (active := step.beforeActive) (partyCandidates := partyCandidates)
      hsolid hpartyActive
  rw [hmass, ← hweighted]
  dsimp [partyFractionalTallyMass]
  refine Finset.sum_congr rfl ?_
  intro candidate hcandidate
  exact (htally_eq candidate hcandidate).symm

/--
Global concrete STV step validity plus a party projection-state identity
constructs the party source-step law.
-/
theorem fractionalPartySTVSourceStepLaw_of_concreteStepLaw
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {fractionalTally : Candidate → ℝ}
    {quota : ℝ} {step : STVStep Candidate} {before : PartyQuotaState}
    (hstep : FractionalSTVConcreteStepLaw fractionalTally quota step)
    (hprojection :
      FractionalPartySTVProjectionStateLaw partyCandidates fractionalTally
        step before) :
    FractionalPartySTVSourceStepLaw partyCandidates fractionalTally quota
      step before := by
  rcases hstep with
    ⟨hremove, focused, hfocus, hfocused_active, htally_nonneg,
      hkind_allowed, hquota_if_elect⟩
  rcases hprojection with ⟨hremaining, hmass⟩
  exact ⟨hremove, focused, hfocus, hfocused_active, htally_nonneg,
    hremaining, hmass, fun _hfocused_party =>
      ⟨hkind_allowed, hquota_if_elect⟩⟩

/--
The deterministic party-state update tracks the concrete active same-party
candidate count across one ordinary focused-removal STV step.
-/
theorem remainingCandidates_partyTransferPreservationNextState_eq_activePartyCandidates
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {fractionalTally : Candidate → ℝ}
    {quota : ℝ} {step : STVStep Candidate} {before : PartyQuotaState}
    (hremove : step.removesFocusedCandidate)
    {focused : Candidate} (hfocus : step.focus = some focused)
    (hfocused_active : focused ∈ step.beforeActive)
    (hkind_allowed :
      step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate)
    (hremaining :
      before.remainingCandidates =
        (activePartyCandidates step.beforeActive partyCandidates).card) :
    (partyTransferPreservationNextState partyCandidates fractionalTally
      quota step before).remainingCandidates =
      (activePartyCandidates step.afterActive partyCandidates).card := by
  by_cases hparty : focused ∈ partyCandidates
  · have hcard :
        (step.afterActive ∩ partyCandidates).card + 1 =
          (step.beforeActive ∩ partyCandidates).card :=
      STVStep.card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
        hremove hfocus hparty hfocused_active
    have hremaining_inter :
        before.remainingCandidates =
          (step.beforeActive ∩ partyCandidates).card := by
      simpa [activePartyCandidates_eq_inter] using hremaining
    cases hkind : step.kind with
    | elect =>
        simp [partyTransferPreservationNextState, hfocus, hparty, hkind,
          activePartyCandidates_eq_inter, hremaining_inter]
        omega
    | eliminate =>
        simp [partyTransferPreservationNextState, hfocus, hparty, hkind,
          activePartyCandidates_eq_inter, hremaining_inter]
        omega
    | transfer =>
        rcases hkind_allowed with helect | heliminate
        · simp [hkind] at helect
        · simp [hkind] at heliminate
    | finish =>
        rcases hkind_allowed with helect | heliminate
        · simp [hkind] at helect
        · simp [hkind] at heliminate
  · have hactiveParty :
        activePartyCandidates step.afterActive partyCandidates =
          activePartyCandidates step.beforeActive partyCandidates := by
      rcases hremove with ⟨removed, hremoved_focus, hafter⟩
      have hremoved_eq : removed = focused :=
        Option.some.inj (hremoved_focus.symm.trans hfocus)
      subst removed
      ext candidate
      by_cases hcandidate : candidate = focused
      · subst candidate
        simp [activePartyCandidates, hafter, hparty]
      · simp [activePartyCandidates, hafter, hcandidate]
    simp [partyTransferPreservationNextState, hfocus, hparty, hactiveParty,
      hremaining]

/--
The source-step law implies the primitive transfer step law consumed by the
party-quota replay.  The nontrivial part is deriving the focused candidate's
tally bound from the party vote-mass identity and nonnegative active tallies.
-/
theorem primitiveTransferStepLaw_of_sourceStepLaw {Candidate : Type*}
    [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {fractionalTally : Candidate → ℝ}
    {quota : ℝ} {step : STVStep Candidate} {before : PartyQuotaState}
    (hlaw :
      FractionalPartySTVSourceStepLaw partyCandidates fractionalTally quota
        step before) :
    FractionalPartySTVPrimitiveTransferStepLaw partyCandidates
      fractionalTally quota step before := by
  rcases hlaw with
    ⟨hremove, focused, hfocus, hfocused_active, htally_nonneg,
      hremaining, hmass, hfocused_party_law⟩
  refine ⟨hremove, focused, hfocus, ?_⟩
  by_cases hfocused_party : focused ∈ partyCandidates
  · have hfocused_active_party :
        focused ∈ activePartyCandidates step.beforeActive partyCandidates := by
      simp [activePartyCandidates, hfocused_active, hfocused_party]
    have hremaining_pos : 0 < before.remainingCandidates := by
      rw [hremaining]
      exact Finset.card_pos.mpr ⟨focused, hfocused_active_party⟩
    have hfocused_tally_nonneg : 0 ≤ fractionalTally focused :=
      htally_nonneg focused hfocused_active
    have hfocused_tally_le_mass :
        fractionalTally focused ≤ before.voteMass := by
      rw [hmass, partyFractionalTallyMass]
      exact Finset.single_le_sum
        (by
          intro candidate hcandidate
          exact htally_nonneg candidate
            ((Finset.mem_filter.mp hcandidate).1))
        hfocused_active_party
    rcases hfocused_party_law hfocused_party with
      ⟨hkind_allowed, hquota_if_elect⟩
    cases hkind : step.kind with
    | elect =>
        simp [hfocused_party]
        exact ⟨hremaining_pos, hfocused_tally_nonneg,
          hquota_if_elect hkind, hfocused_tally_le_mass⟩
    | eliminate =>
        simp [hfocused_party]
        exact ⟨hremaining_pos, hfocused_tally_nonneg,
          hfocused_tally_le_mass⟩
    | transfer =>
        rcases hkind_allowed with helect | heliminate
        · simp [hkind] at helect
        · simp [hkind] at heliminate
    | finish =>
        rcases hkind_allowed with helect | heliminate
        · simp [hkind] at helect
        · simp [hkind] at heliminate
  · simp [hfocused_party]

/--
A primitive step law constructs the corresponding transfer-preservation step
for the deterministic party-state update.
-/
theorem transferPreservationStep_of_primitiveStepLaw {Candidate : Type*}
    [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {fractionalTally : Candidate → ℝ}
    {quota : ℝ} {step : STVStep Candidate} {before : PartyQuotaState}
    (hlaw :
      FractionalPartySTVPrimitiveTransferStepLaw
        partyCandidates fractionalTally quota step before) :
    FractionalPartySTVTransferPreservationStep
      partyCandidates fractionalTally quota step before
      (partyTransferPreservationNextState
        partyCandidates fractionalTally quota step before) := by
  rcases hlaw with ⟨hremove, focused, hfocus, hfocused_law⟩
  refine ⟨hremove, ?_⟩
  by_cases hfocused_party : focused ∈ partyCandidates
  · have hsame_party_law := by
      simpa [hfocused_party] using hfocused_law
    cases hkind : step.kind with
    | elect =>
        simp [hkind] at hsame_party_law
        rcases hsame_party_law with
          ⟨hremaining, htally_nonneg, hquota_le, htally_le_mass⟩
        left
        refine ⟨rfl, focused, hfocus, hfocused_party, ?_⟩
        refine ⟨fractionalTally focused - quota, htally_nonneg, hquota_le,
          htally_le_mass, rfl, ?_, ?_, ?_, ?_⟩
        · linarith
        · simp [partyTransferPreservationNextState, hfocus, hfocused_party,
            hkind, Nat.sub_add_cancel (Nat.succ_le_of_lt hremaining)]
        · simp [partyTransferPreservationNextState, hfocus, hfocused_party,
            hkind]
        · simp [partyTransferPreservationNextState, hfocus, hfocused_party,
            hkind]
    | eliminate =>
        simp [hkind] at hsame_party_law
        rcases hsame_party_law with
          ⟨hremaining, htally_nonneg, htally_le_mass⟩
        right
        left
        refine ⟨rfl, focused, hfocus, hfocused_party, ?_⟩
        refine ⟨htally_nonneg, htally_le_mass, ?_, ?_, ?_⟩
        · simp [partyTransferPreservationNextState, hfocus, hfocused_party,
            hkind, Nat.sub_add_cancel (Nat.succ_le_of_lt hremaining)]
        · simp [partyTransferPreservationNextState, hfocus, hfocused_party,
            hkind]
        · simp [partyTransferPreservationNextState, hfocus, hfocused_party,
            hkind]
    | transfer =>
        simp [hkind] at hsame_party_law
    | finish =>
        simp [hkind] at hsame_party_law
  · right
    right
    exact ⟨focused, hfocus, hfocused_party, by
      simp [partyTransferPreservationNextState, hfocus, hfocused_party]⟩

/--
A transfer-preservation step is either a genuine same-party quota-process step
or an outside-party stutter step.
-/
theorem partyQuotaStep_or_eq_of_transferPreservationStep {Candidate : Type*}
    [DecidableEq Candidate] {partyCandidates : Finset Candidate}
    {fractionalTally : Candidate → ℝ} {quota : ℝ}
    {step : STVStep Candidate} {before after : PartyQuotaState}
    (hstep :
      FractionalPartySTVTransferPreservationStep
        partyCandidates fractionalTally quota step before after) :
    PartyQuotaStep quota before after ∨ after = before := by
  rcases hstep with ⟨_hremove, helect | heliminate | houtside⟩
  · rcases helect with
      ⟨_hkind, focused, _hfocus, _hfocused_party, helectStep⟩
    exact Or.inl <| Or.inl <|
      partyQuotaElectStep_of_fractionalPartySTVElectStep
        (fractionalPartySTVElectStep_of_withTally helectStep)
  · rcases heliminate with
      ⟨_hkind, focused, _hfocus, _hfocused_party, heliminateStep⟩
    exact Or.inl <| Or.inr <|
      partyQuotaEliminateStep_of_fractionalPartySTVEliminateStep
        (fractionalPartySTVEliminateStep_of_withTally heliminateStep)
  · rcases houtside with ⟨_focused, _hfocus, _houtside, hsame⟩
    exact Or.inr hsame

/--
Replay path for the source-shaped transfer preservation condition over a shared
list of fractional STV steps.
-/
inductive FractionalPartySTVTransferPreservationPath {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ) :
    List (STVStep Candidate) → PartyQuotaState → PartyQuotaState → Prop
  | nil (state : PartyQuotaState) :
      FractionalPartySTVTransferPreservationPath
        partyCandidates quota fractionalTally [] state state
  | cons {step : STVStep Candidate} {steps : List (STVStep Candidate)}
      {before middle after : PartyQuotaState}
      (hstep :
        FractionalPartySTVTransferPreservationStep
          partyCandidates (fractionalTally step) quota step before middle)
      (hrest :
        FractionalPartySTVTransferPreservationPath
          partyCandidates quota fractionalTally steps middle after) :
      FractionalPartySTVTransferPreservationPath
        partyCandidates quota fractionalTally (step :: steps) before after

/--
Terminal party state obtained by folding the deterministic primitive
party-state transition over a concrete STV trace.
-/
def partyTransferPreservationTerminalState {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ) :
    List (STVStep Candidate) → PartyQuotaState → PartyQuotaState
  | [], state => state
  | step :: steps, state =>
      partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps
        (partyTransferPreservationNextState partyCandidates
          (fractionalTally step) quota step state)

/--
Along a replayed concrete active-set prefix, the deterministic party-state fold
tracks the concrete number of active same-party candidates.
-/
theorem remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {state : PartyQuotaState}
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart :
      state.remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hsteps :
      ∀ step, step ∈ steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate)) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps state).remainingCandidates =
      (activePartyCandidates terminalActive partyCandidates).card := by
  induction steps generalizing startActive state with
  | nil =>
      simp [STVTrace.replayStepsFrom] at hreplay
      rw [hreplay]
      exact hstart
  | cons step steps ih =>
      simp only [STVTrace.replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest_replay⟩
      rcases hsteps step (by simp) with
        ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
      have hstart_step :
          state.remainingCandidates =
            (activePartyCandidates step.beforeActive partyCandidates).card := by
        rw [← hbefore] at hstart
        exact hstart
      have hnext_remaining :
          (partyTransferPreservationNextState partyCandidates
            (fractionalTally step) quota step state).remainingCandidates =
            (activePartyCandidates step.afterActive partyCandidates).card :=
        remainingCandidates_partyTransferPreservationNextState_eq_activePartyCandidates
          (partyCandidates := partyCandidates)
          (fractionalTally := fractionalTally step) (quota := quota)
          (step := step) (before := state) hremove hfocus
          hfocused_active hkind_allowed hstart_step
      have hrest_steps :
          ∀ step', step' ∈ steps →
            ∃ focused, step'.focus = some focused ∧
              focused ∈ step'.beforeActive ∧
              step'.removesFocusedCandidate ∧
              (step'.kind = StepKind.elect ∨
                step'.kind = StepKind.eliminate) := by
        intro step' hstep'
        exact hsteps step' (by simp [hstep'])
      simpa [partyTransferPreservationTerminalState] using
        ih hrest_replay hnext_remaining hrest_steps

/--
The deterministic party-state fold records exactly the same-party election
steps in `quotaWinners`, in addition to any winners already in the start state.
-/
theorem quotaWinners_partyTransferPreservationTerminalState
    {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ)
    (steps : List (STVStep Candidate)) (state : PartyQuotaState) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps state).quotaWinners =
      state.quotaWinners + partyElectStepCount partyCandidates steps := by
  induction steps generalizing state with
  | nil =>
      simp [partyTransferPreservationTerminalState, partyElectStepCount]
  | cons step steps ih =>
      dsimp [partyTransferPreservationTerminalState, partyElectStepCount]
      rw [ih]
      cases hfocus : step.focus with
      | none =>
          simp [partyTransferPreservationNextState, hfocus]
      | some focused =>
          by_cases hparty : focused ∈ partyCandidates
          · cases hkind : step.kind <;>
              simp [partyTransferPreservationNextState, hfocus, hparty,
                hkind, Nat.add_assoc]
          · cases hkind : step.kind <;>
              simp [partyTransferPreservationNextState, hfocus, hparty]

/--
For the standard party start state, terminal `quotaWinners` is exactly the
number of same-party election steps in the concrete trace.
-/
theorem quotaWinners_partyTransferPreservationTerminalState_startState
    {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota initialVotes : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ)
    (steps : List (STVStep Candidate)) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).quotaWinners =
      partyElectStepCount partyCandidates steps := by
  simpa [PartyQuotaStartState] using
    quotaWinners_partyTransferPreservationTerminalState
      partyCandidates quota fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)

/--
If the final party seat count contains the same-party election steps of the
trace, it contains the quota winners recorded by the party-state fold.
-/
theorem quotaWinners_terminalState_le_of_partyElectStepCount_le
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {finalSeats : ℕ}
    (hcount : partyElectStepCount partyCandidates steps ≤ finalSeats) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).quotaWinners ≤
      finalSeats := by
  rw [quotaWinners_partyTransferPreservationTerminalState_startState]
  exact hcount

/--
The deterministic party-state fold removes exactly one quota of vote mass for
each same-party election step and preserves vote mass at all other steps.
-/
theorem voteMass_partyTransferPreservationTerminalState
    {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ)
    (steps : List (STVStep Candidate)) (state : PartyQuotaState) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps state).voteMass =
      state.voteMass - (partyElectStepCount partyCandidates steps : ℝ) *
        quota := by
  induction steps generalizing state with
  | nil =>
      simp [partyTransferPreservationTerminalState, partyElectStepCount]
  | cons step steps ih =>
      dsimp [partyTransferPreservationTerminalState, partyElectStepCount]
      rw [ih]
      cases hfocus : step.focus with
      | none =>
          simp [partyTransferPreservationNextState, hfocus]
      | some focused =>
          by_cases hparty : focused ∈ partyCandidates
          · cases hkind : step.kind
            · simp [partyTransferPreservationNextState, hfocus, hparty,
                hkind, Nat.cast_add, Nat.cast_one]
              ring
            · simp [partyTransferPreservationNextState, hfocus, hparty,
                hkind]
            · simp [partyTransferPreservationNextState, hfocus, hparty,
                hkind]
            · simp [partyTransferPreservationNextState, hfocus, hparty,
                hkind]
          · cases hkind : step.kind <;>
              simp [partyTransferPreservationNextState, hfocus, hparty]

/--
For the standard party start state, terminal vote mass is the initial party
mass minus one quota for every same-party election step.
-/
theorem voteMass_partyTransferPreservationTerminalState_startState
    {Candidate : Type*} [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota initialVotes : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ)
    (steps : List (STVStep Candidate)) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).voteMass =
      initialVotes - (partyElectStepCount partyCandidates steps : ℝ) *
        quota := by
  simpa [PartyQuotaStartState] using
    voteMass_partyTransferPreservationTerminalState
      partyCandidates quota fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)

/--
The deterministic party-state fold and the fractional voter-weight fold have
the same party vote mass after any trace prefix, provided they start with the
same total party weight and follow the source transfer law.
-/
theorem voteMass_partyTransferPreservationTerminalState_eq_sum_fractionalSTVWeightAfterSteps
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hinitial :
      initialVotes = ∑ voter ∈ voters, initialWeight voter)
    (hquota_pos : 0 < quota)
    (hlaw :
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps initialWeight) :
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).voteMass =
      ∑ voter ∈ voters,
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter := by
  calc
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).voteMass
        =
        initialVotes - (partyElectStepCount partyCandidates steps : ℝ) *
          quota := by
          rw [voteMass_partyTransferPreservationTerminalState_startState]
    _ =
        (∑ voter ∈ voters, initialWeight voter) -
          (partyElectStepCount partyCandidates steps : ℝ) * quota := by
          rw [hinitial]
    _ =
        ∑ voter ∈ voters,
          fractionalSTVWeightAfterSteps voters ballots quota steps
            initialWeight voter := by
          rw [sum_fractionalSTVWeightAfterSteps_eq_sum_sub_partyElectStepCount
            (voters := voters) (ballots := ballots)
            (partyCandidates := partyCandidates) (quota := quota)
            (steps := steps) (initialWeight := initialWeight)
            hquota_pos hlaw]

/--
Weight-fold terminal residual form: if the recursively transferred party
weights are below quota after the trace, then the deterministic party-state
fold is terminal below quota.
-/
theorem terminalBelowQuota_of_fractionalSTVWeightAfterSteps_lt
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {initialWeight : Voter → ℝ}
    (hinitial :
      initialVotes = ∑ voter ∈ voters, initialWeight voter)
    (hquota_pos : 0 < quota)
    (hlaw :
      FractionalSTVPartyWeightTraceLaw voters ballots partyCandidates quota
        steps initialWeight)
    (hterminal :
      (∑ voter ∈ voters,
        fractionalSTVWeightAfterSteps voters ballots quota steps
          initialWeight voter) < quota) :
    PartyQuotaTerminalBelowQuota quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps
        (PartyQuotaStartState partyCandidates.card initialVotes)) := by
  change
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).voteMass < quota
  rw [voteMass_partyTransferPreservationTerminalState_eq_sum_fractionalSTVWeightAfterSteps
    (voters := voters) (ballots := ballots)
    (partyCandidates := partyCandidates) (quota := quota)
    (initialVotes := initialVotes) (fractionalTally := fractionalTally)
    (steps := steps) (initialWeight := initialWeight)
    hinitial hquota_pos hlaw]
  exact hterminal

/--
A trace-level residual inequality proves the terminal below-quota predicate for
the deterministic party-state fold.
-/
theorem terminalBelowQuota_of_partyElectStepCount_residual_lt
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    (hresidual :
      initialVotes - (partyElectStepCount partyCandidates steps : ℝ) * quota <
        quota) :
    PartyQuotaTerminalBelowQuota quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps
        (PartyQuotaStartState partyCandidates.card initialVotes)) := by
  change
    (partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)).voteMass < quota
  rw [voteMass_partyTransferPreservationTerminalState_startState]
  exact hresidual

/--
A deterministic party-state fold whose synthetic residual is below quota
implies the direct quota-floor lower bound for the number of same-party
elections in the trace.
-/
theorem floor_votes_div_quota_le_partyElectStepCount_of_terminalBelowQuota
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (hterminal :
      PartyQuotaTerminalBelowQuota quota
        (partyTransferPreservationTerminalState partyCandidates quota
          fractionalTally steps
          (PartyQuotaStartState partyCandidates.card initialVotes))) :
    ⌊initialVotes / quota⌋₊ ≤ partyElectStepCount partyCandidates steps := by
  let terminalState :=
    partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)
  have hres_lt : terminalState.voteMass < quota := hterminal
  have hmass :
      terminalState.voteMass =
        initialVotes - (partyElectStepCount partyCandidates steps : ℝ) *
          quota := by
    simpa [terminalState] using
      voteMass_partyTransferPreservationTerminalState_startState
        partyCandidates quota initialVotes fractionalTally steps
  have hinit :
      initialVotes =
        (partyElectStepCount partyCandidates steps : ℝ) * quota +
          terminalState.voteMass := by
    rw [hmass]
    ring
  have hx_nonneg : 0 ≤ initialVotes / quota :=
    div_nonneg hvotes_nonneg hquota_pos.le
  have hx_lt :
      initialVotes / quota <
        (partyElectStepCount partyCandidates steps : ℝ) + 1 := by
    rw [hinit]
    have hquot_lt : terminalState.voteMass / quota < 1 := by
      rw [div_lt_one hquota_pos]
      exact hres_lt
    field_simp [hquota_pos.ne']
    nlinarith
  have hfloor_lt :
      ⌊initialVotes / quota⌋₊ <
        partyElectStepCount partyCandidates steps + 1 := by
    rw [Nat.floor_lt hx_nonneg]
    simpa [Nat.cast_add, Nat.cast_one] using hx_lt
  exact Nat.lt_succ_iff.mp hfloor_lt

/--
If a same-party quota process preserves the capacity invariant, then the
canonical quota floor is bounded by quota winners plus the same-party
candidates still active at the terminal fill point.

This is the arithmetic form used for source STV rules that fill the remaining
seats with terminal active candidates rather than treating those final seats as
additional quota-transfer rounds.
-/
theorem floor_votes_div_quota_le_quotaWinners_add_remaining_of_capacityBound
    {initialVotes quota : ℝ} {state : PartyQuotaState}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (hinit :
      initialVotes = (state.quotaWinners : ℝ) * quota + state.voteMass)
    (hcapacity : PartyQuotaCapacityBound quota state) :
    ⌊initialVotes / quota⌋₊ ≤
      state.quotaWinners + state.remainingCandidates := by
  have hx_nonneg : 0 ≤ initialVotes / quota :=
    div_nonneg hvotes_nonneg hquota_pos.le
  have hcapacity' :
      state.voteMass < ((state.remainingCandidates : ℝ) + 1) * quota := by
    simpa [PartyQuotaCapacityBound, Nat.cast_add, Nat.cast_one]
      using hcapacity
  have hx_lt :
      initialVotes / quota <
        ((state.quotaWinners + state.remainingCandidates : ℕ) : ℝ) + 1 := by
    rw [hinit]
    rw [div_lt_iff₀ hquota_pos]
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hfloor_lt :
      ⌊initialVotes / quota⌋₊ <
        state.quotaWinners + state.remainingCandidates + 1 := by
    rw [Nat.floor_lt hx_nonneg]
    simpa [Nat.cast_add, Nat.cast_one] using hx_lt
  exact Nat.lt_succ_iff.mp hfloor_lt

/--
Capacity preservation for a solid coalition using source-faithful lower-bound
accounting: each same-party election can remove at most one quota of the
coalition's current weight, while same-party eliminations are allowed only when
no active same-party candidate is at quota in the global tally.

Unlike the exact party-weight replay theorem, this result does not assume that
other voters give no support to same-party winners.
-/
theorem partyTransferPreservationTerminalState_capacityAndMassLower_of_replaySteps_lowerBound
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ} {startState : PartyQuotaState}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (htally_eq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ (steps.get i).beforeActive →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart : PartyQuotaCapacityBound quota startState)
    (hstartRemaining :
      startState.remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hmassLower :
      0 < startState.remainingCandidates →
        startState.voteMass ≤ ∑ voter ∈ partyVoters, initialWeight voter)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota) :
    PartyQuotaCapacityBound quota
        (partyTransferPreservationTerminalState partyCandidates quota
          fractionalTally steps startState) ∧
      (0 <
          (partyTransferPreservationTerminalState partyCandidates quota
            fractionalTally steps startState).remainingCandidates →
        (partyTransferPreservationTerminalState partyCandidates quota
          fractionalTally steps startState).voteMass ≤
          ∑ voter ∈ partyVoters,
            fractionalSTVWeightAfterSteps allVoters ballots quota steps
              initialWeight voter) := by
  induction steps generalizing startActive initialWeight startState with
  | nil =>
      constructor
      · simpa [partyTransferPreservationTerminalState] using hstart
      · simpa [partyTransferPreservationTerminalState] using hmassLower
  | cons step steps ih =>
      simp only [STVTrace.replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, htailReplay⟩
      let nextState :=
        partyTransferPreservationNextState partyCandidates
          (fractionalTally step) quota step startState
      let nextWeight :=
        fractionalSTVNextWeight allVoters ballots quota step initialWeight
      have hstepConcrete :
          FractionalSTVConcreteStepLaw (fractionalTally step) quota step := by
        have h0 := htraceSteps ⟨0, by simp⟩
        simpa using h0
      rcases hstepConcrete with
        ⟨hremove, focused, hfocus, hfocused_active, _htally_nonneg,
          hkind_allowed, hquota_if_elect⟩
      have hremaining_step :
          startState.remainingCandidates =
            (activePartyCandidates step.beforeActive partyCandidates).card := by
        simpa [hbefore] using hstartRemaining
      have hnextRemaining :
          nextState.remainingCandidates =
            (activePartyCandidates step.afterActive partyCandidates).card := by
        simpa [nextState] using
          remainingCandidates_partyTransferPreservationNextState_eq_activePartyCandidates
            (partyCandidates := partyCandidates)
            (fractionalTally := fractionalTally step) (quota := quota)
            (step := step) (before := startState) hremove hfocus
            hfocused_active hkind_allowed hremaining_step
      have hsum_non_elect :
          step.kind ≠ StepKind.elect →
            (∑ voter ∈ partyVoters, nextWeight voter) =
              ∑ voter ∈ partyVoters, initialWeight voter := by
        intro hne
        refine Finset.sum_congr rfl ?_
        intro voter hvoter
        cases hfocus' : step.focus with
        | none =>
            simp [nextWeight, fractionalSTVNextWeight, hfocus']
        | some focused' =>
            cases hkind' : step.kind <;>
              simp [nextWeight, fractionalSTVNextWeight, hfocus', hkind'] at hne ⊢
      have hnextCapacity : PartyQuotaCapacityBound quota nextState := by
        by_cases hparty : focused ∈ partyCandidates
        · have hpartyActiveStep :
              ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive :=
            ⟨focused, hparty, hfocused_active⟩
          have hremaining_pos : 0 < startState.remainingCandidates := by
            rw [hremaining_step]
            exact Finset.card_pos.mpr
              ⟨focused, by
                simp [activePartyCandidates, hfocused_active, hparty]⟩
          cases hkind : step.kind with
          | elect =>
              have hremaining_update :
                  nextState.remainingCandidates + 1 =
                    startState.remainingCandidates := by
                simp [nextState, partyTransferPreservationNextState, hfocus,
                  hparty, hkind]
                omega
              have hmass_update :
                  nextState.voteMass = startState.voteMass - quota := by
                simp [nextState, partyTransferPreservationNextState, hfocus,
                  hparty, hkind]
              exact PartyQuotaCapacityBound.of_electUpdate hstart
                hremaining_update hmass_update
          | eliminate =>
              have hstate_le_sum :
                  startState.voteMass ≤
                    ∑ voter ∈ partyVoters, initialWeight voter :=
                hmassLower hremaining_pos
              have hweighted_eq :
                  partyFractionalTallyMass partyCandidates
                      (fractionalActiveTally partyVoters ballots
                        initialWeight step.beforeActive)
                      step.beforeActive =
                    ∑ voter ∈ partyVoters, initialWeight voter :=
                partyFractionalTallyMass_fractionalActiveTally_eq_sum_weights_of_solidCoalition
                  (voters := partyVoters) (ballots := ballots)
                  (weight := initialWeight) (active := step.beforeActive)
                  (partyCandidates := partyCandidates) hsolid
                  hpartyActiveStep
              have hweighted_le_trace :
                  partyFractionalTallyMass partyCandidates
                      (fractionalActiveTally partyVoters ballots
                        initialWeight step.beforeActive)
                      step.beforeActive ≤
                    partyFractionalTallyMass partyCandidates
                      (fractionalTally step) step.beforeActive := by
                dsimp [partyFractionalTallyMass]
                refine Finset.sum_le_sum ?_
                intro candidate hcandidate
                have hcandidate_active :
                    candidate ∈ step.beforeActive :=
                  (Finset.mem_filter.mp hcandidate).1
                have hle_global :
                    fractionalActiveTally partyVoters ballots initialWeight
                        step.beforeActive candidate ≤
                      fractionalActiveTally allVoters ballots initialWeight
                        step.beforeActive candidate :=
                  fractionalActiveTally_le_of_voters_subset
                    (voters₁ := partyVoters) (voters₂ := allVoters)
                    (ballots := ballots) (weight := initialWeight)
                    (active := step.beforeActive) (candidate := candidate)
                    hpartyVoters_subset hweight_nonneg
                have heq_trace :
                    fractionalTally step candidate =
                      fractionalActiveTally allVoters ballots initialWeight
                        step.beforeActive candidate := by
                  have h0 := htally_eq ⟨0, by simp⟩ candidate hcandidate_active
                  simpa [fractionalSTVWeightAfterSteps] using h0
                simpa [heq_trace] using hle_global
              have htrace_mass_lt :
                  partyFractionalTallyMass partyCandidates
                      (fractionalTally step) step.beforeActive <
                    ((activePartyCandidates step.beforeActive
                        partyCandidates).card : ℝ) * quota :=
                partyFractionalTallyMass_lt_card_mul_quota_of_forall_lt
                  (partyCandidates := partyCandidates)
                  (fractionalTally := fractionalTally step)
                  (active := step.beforeActive) (quota := quota)
                  (by
                    rcases hpartyActiveStep with
                      ⟨same, hsame_party, hsame_active⟩
                    exact ⟨same, by
                      simp [activePartyCandidates, hsame_active,
                        hsame_party]⟩)
                  (hnoquota_on_eliminate ⟨0, by simp⟩ hkind)
              have hmass_lt :
                  startState.voteMass <
                    (startState.remainingCandidates : ℝ) * quota := by
                rw [hremaining_step]
                rw [← hweighted_eq] at hstate_le_sum
                exact lt_of_le_of_lt
                  (le_trans hstate_le_sum hweighted_le_trace)
                  htrace_mass_lt
              have hremaining_update :
                  nextState.remainingCandidates + 1 =
                    startState.remainingCandidates := by
                simp [nextState, partyTransferPreservationNextState, hfocus,
                  hparty, hkind]
                omega
              have hmass_update :
                  nextState.voteMass = startState.voteMass := by
                simp [nextState, partyTransferPreservationNextState, hfocus,
                  hparty, hkind]
              exact
                PartyQuotaCapacityBound.of_eliminateStep_of_voteMass_lt_remaining_mul_quota
                  hmass_lt ⟨hremaining_update, by
                    simp [nextState, partyTransferPreservationNextState,
                      hfocus, hparty, hkind],
                    hmass_update⟩
          | transfer =>
              rcases hkind_allowed with helect | heliminate <;> simp [hkind] at *
          | finish =>
              rcases hkind_allowed with helect | heliminate <;> simp [hkind] at *
        · have hsame :
              nextState = startState := by
            simp [nextState, partyTransferPreservationNextState, hfocus, hparty]
          simpa [hsame] using hstart
      have hnextMassLower :
          0 < nextState.remainingCandidates →
            nextState.voteMass ≤ ∑ voter ∈ partyVoters, nextWeight voter := by
        intro hnext_pos
        by_cases hparty : focused ∈ partyCandidates
        · have hremaining_pos : 0 < startState.remainingCandidates := by
            rw [hremaining_step]
            exact Finset.card_pos.mpr
              ⟨focused, by
                simp [activePartyCandidates, hfocused_active, hparty]⟩
          have hstate_le_sum :
              startState.voteMass ≤
                ∑ voter ∈ partyVoters, initialWeight voter :=
            hmassLower hremaining_pos
          cases hkind : step.kind with
          | elect =>
              have hquota_le_global :
                  quota ≤
                    fractionalActiveTally allVoters ballots initialWeight
                      step.beforeActive focused := by
                have hquota_le_trace : quota ≤ fractionalTally step focused :=
                  hquota_if_elect hkind
                have heq_trace :
                    fractionalTally step focused =
                      fractionalActiveTally allVoters ballots initialWeight
                        step.beforeActive focused := by
                  have h0 := htally_eq ⟨0, by simp⟩ focused hfocused_active
                  simpa [fractionalSTVWeightAfterSteps] using h0
                simpa [heq_trace] using hquota_le_trace
              have hsum_lower :
                  (∑ voter ∈ partyVoters, initialWeight voter) - quota ≤
                    ∑ voter ∈ partyVoters, nextWeight voter := by
                simpa [nextWeight] using
                  sum_fractionalSTVNextWeight_elect_ge_sum_sub_quota_of_subset
                    (allVoters := allVoters) (voters := partyVoters)
                    (ballots := ballots) (quota := quota) (step := step)
                    (weight := initialWeight) (focused := focused)
                    hpartyVoters_subset hweight_nonneg hquota_pos hfocus
                    hkind hquota_le_global
              have hmass_update :
                  nextState.voteMass = startState.voteMass - quota := by
                simp [nextState, partyTransferPreservationNextState, hfocus,
                  hparty, hkind]
              rw [hmass_update]
              linarith
          | eliminate =>
              have hsum_eq := hsum_non_elect (by simp [hkind])
              have hmass_update :
                  nextState.voteMass = startState.voteMass := by
                simp [nextState, partyTransferPreservationNextState, hfocus,
                  hparty, hkind]
              rw [hmass_update, hsum_eq]
              exact hstate_le_sum
          | transfer =>
              rcases hkind_allowed with helect | heliminate <;> simp [hkind] at *
          | finish =>
              rcases hkind_allowed with helect | heliminate <;> simp [hkind] at *
        · have hsame :
              nextState = startState := by
            simp [nextState, partyTransferPreservationNextState, hfocus, hparty]
          have hremaining_pos : 0 < startState.remainingCandidates := by
            simpa [hsame] using hnext_pos
          have hstate_le_sum :
              startState.voteMass ≤
                ∑ voter ∈ partyVoters, initialWeight voter :=
            hmassLower hremaining_pos
          cases hkind : step.kind with
          | elect =>
              have hpartyActiveStep :
                  ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
                rw [hremaining_step] at hremaining_pos
                rcases Finset.card_pos.mp hremaining_pos with
                  ⟨same, hsame_mem⟩
                exact ⟨same, (Finset.mem_filter.mp hsame_mem).2,
                  (Finset.mem_filter.mp hsame_mem).1⟩
              have hsum_eq :
                  (∑ voter ∈ partyVoters, nextWeight voter) =
                    ∑ voter ∈ partyVoters, initialWeight voter := by
                simpa [nextWeight] using
                  sum_fractionalSTVNextWeight_elect_eq_sum_of_solidCoalition_outside
                    (allVoters := allVoters) (voters := partyVoters)
                    (ballots := ballots) (partyCandidates := partyCandidates)
                    (quota := quota) (step := step) (weight := initialWeight)
                    (focused := focused) hsolid hpartyActiveStep hfocus
                    hkind hparty
              simpa [hsame, hsum_eq] using hstate_le_sum
          | eliminate =>
              have hsum_eq := hsum_non_elect (by simp [hkind])
              simpa [hsame, hsum_eq] using hstate_le_sum
          | transfer =>
              rcases hkind_allowed with helect | heliminate <;> simp [hkind] at *
          | finish =>
              rcases hkind_allowed with helect | heliminate <;> simp [hkind] at *
      have htailTraceSteps :
          ∀ i : Fin steps.length,
            FractionalSTVConcreteStepLaw
              (fractionalTally (steps.get i)) quota (steps.get i) := by
        intro i
        have hsucc :=
          htraceSteps ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
        simpa using hsucc
      have htailTallyEq :
          ∀ i : Fin steps.length, ∀ candidate,
            candidate ∈ (steps.get i).beforeActive →
              fractionalTally (steps.get i) candidate =
                fractionalActiveTally allVoters ballots
                  (fractionalSTVWeightAfterSteps allVoters ballots quota
                    (steps.take i.1) nextWeight)
                  (steps.get i).beforeActive candidate := by
        intro i candidate hcandidate
        have hsucc :=
          htally_eq ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
            candidate hcandidate
        simpa [fractionalSTVWeightAfterSteps, Nat.succ_eq_add_one,
          nextWeight] using hsucc
      have htailNoquota :
          ∀ i : Fin steps.length,
            (steps.get i).kind = StepKind.eliminate →
              ∀ candidate,
                candidate ∈
                    activePartyCandidates (steps.get i).beforeActive
                      partyCandidates →
                  fractionalTally (steps.get i) candidate < quota := by
        intro i hkind candidate hcandidate
        exact
          hnoquota_on_eliminate
            ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
            (by simpa using hkind) candidate (by simpa using hcandidate)
      have hnextWeight_nonneg :
          ∀ voter, voter ∈ allVoters → 0 ≤ nextWeight voter := by
        exact
          fractionalSTVNextWeight_nonneg
            (voters := allVoters) (ballots := ballots) (quota := quota)
            (step := step) (weight := initialWeight)
            hweight_nonneg hquota_pos (by
              intro elected helect_focus helect_kind
              have hquota_le_trace :
                  quota ≤ fractionalTally step elected := by
                have heq : elected = focused :=
                  Option.some.inj (helect_focus.symm.trans hfocus)
                subst elected
                exact hquota_if_elect helect_kind
              have heq_trace :
                  fractionalTally step elected =
                    fractionalActiveTally allVoters ballots initialWeight
                      step.beforeActive elected := by
                have hactive : elected ∈ step.beforeActive := by
                  have heq : elected = focused :=
                    Option.some.inj (helect_focus.symm.trans hfocus)
                  simpa [heq] using hfocused_active
                have h0 := htally_eq ⟨0, by simp⟩ elected hactive
                simpa [fractionalSTVWeightAfterSteps] using h0
              simpa [heq_trace] using hquota_le_trace)
      simpa [partyTransferPreservationTerminalState, nextState, nextWeight] using
        ih hnextWeight_nonneg htailTraceSteps htailTallyEq htailReplay
          hnextCapacity hnextRemaining hnextMassLower htailNoquota

/--
Capacity preservation for a solid coalition using source-faithful lower-bound
accounting.
-/
theorem partyTransferPreservationTerminalState_capacityBound_of_replaySteps_lowerBound
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ} {startState : PartyQuotaState}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (htally_eq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ (steps.get i).beforeActive →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart : PartyQuotaCapacityBound quota startState)
    (hstartRemaining :
      startState.remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hmassLower :
      0 < startState.remainingCandidates →
        startState.voteMass ≤ ∑ voter ∈ partyVoters, initialWeight voter)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota) :
    PartyQuotaCapacityBound quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState) :=
  (partyTransferPreservationTerminalState_capacityAndMassLower_of_replaySteps_lowerBound
    hsolid hpartyVoters_subset hweight_nonneg hquota_pos htraceSteps
    htally_eq hreplay hstart hstartRemaining hmassLower
    hnoquota_on_eliminate).1

/--
If the source-faithful lower-bound replay keeps the current global weight of a
solid coalition below quota, then the deterministic party-state fold is
terminal below quota. If the party has no remaining candidates, this follows
from capacity; otherwise the strengthened replay invariant bounds party-state
vote mass by the coalition's current global weight.
-/
theorem terminalBelowQuota_of_replaySteps_lowerBound_globalWeight_lt
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ} {startState : PartyQuotaState}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (htally_eq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ (steps.get i).beforeActive →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart : PartyQuotaCapacityBound quota startState)
    (hstartRemaining :
      startState.remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hmassLower :
      0 < startState.remainingCandidates →
        startState.voteMass ≤ ∑ voter ∈ partyVoters, initialWeight voter)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota)
    (hterminalWeightBelow :
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps allVoters ballots quota steps
          initialWeight voter) < quota) :
    PartyQuotaTerminalBelowQuota quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState) := by
  let terminalState :=
    partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps startState
  have hpair :
      PartyQuotaCapacityBound quota terminalState ∧
        (0 < terminalState.remainingCandidates →
          terminalState.voteMass ≤
            ∑ voter ∈ partyVoters,
              fractionalSTVWeightAfterSteps allVoters ballots quota steps
                initialWeight voter) := by
    simpa [terminalState] using
      partyTransferPreservationTerminalState_capacityAndMassLower_of_replaySteps_lowerBound
        hsolid hpartyVoters_subset hweight_nonneg hquota_pos htraceSteps
        htally_eq hreplay hstart hstartRemaining hmassLower
        hnoquota_on_eliminate
  by_cases hremaining_pos : 0 < terminalState.remainingCandidates
  · change terminalState.voteMass < quota
    exact lt_of_le_of_lt (hpair.2 hremaining_pos) hterminalWeightBelow
  · have hremaining_zero : terminalState.remainingCandidates = 0 :=
      Nat.eq_zero_of_not_pos hremaining_pos
    exact
      PartyQuotaCapacityBound.terminalBelowQuota_of_remaining_zero
        hpair.1 hremaining_zero

/--
If the source-faithful lower-bound replay preserves capacity and the active-set
replay ends with no same-party candidates, then the deterministic party-state
fold is terminal below quota.
-/
theorem terminalBelowQuota_of_replaySteps_lowerBound_capacity_no_activeParty_terminal
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ} {startState : PartyQuotaState}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (htally_eq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ (steps.get i).beforeActive →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart : PartyQuotaCapacityBound quota startState)
    (hstartRemaining :
      startState.remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hmassLower :
      0 < startState.remainingCandidates →
        startState.voteMass ≤ ∑ voter ∈ partyVoters, initialWeight voter)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota)
    (hsteps :
      ∀ step, step ∈ steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hterminalNoParty :
      activePartyCandidates terminalActive partyCandidates = ∅) :
    PartyQuotaTerminalBelowQuota quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState) := by
  have hcapacity :
      PartyQuotaCapacityBound quota
        (partyTransferPreservationTerminalState partyCandidates quota
          fractionalTally steps startState) :=
    partyTransferPreservationTerminalState_capacityBound_of_replaySteps_lowerBound
      hsolid hpartyVoters_subset hweight_nonneg hquota_pos htraceSteps
      htally_eq hreplay hstart hstartRemaining hmassLower
      hnoquota_on_eliminate
  have hremaining :
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState).remainingCandidates =
        (activePartyCandidates terminalActive partyCandidates).card :=
    remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
      (partyCandidates := partyCandidates) (quota := quota)
      (fractionalTally := fractionalTally) (steps := steps)
      (startActive := startActive) (terminalActive := terminalActive)
      (state := startState) hreplay hstartRemaining hsteps
  have hremaining_zero :
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState).remainingCandidates = 0 := by
    rw [hremaining, hterminalNoParty]
    simp
  exact
    PartyQuotaCapacityBound.terminalBelowQuota_of_remaining_zero hcapacity
      hremaining_zero

/--
Source-faithful lower-bound replay gives the direct quota-floor lower bound for
the final same-party seat count, using only concrete trace laws, solid
coalitions, quota-respecting eliminations, and terminal exhaustion.
-/
theorem floor_votes_div_quota_le_finalSeats_of_replaySteps_lowerBound_capacityTerminal
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ} {finalSeats : ℕ}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (htally_eq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ (steps.get i).beforeActive →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hmassLower :
      0 <
          (PartyQuotaStartState partyCandidates.card
            initialVotes).remainingCandidates →
        (PartyQuotaStartState partyCandidates.card initialVotes).voteMass ≤
          ∑ voter ∈ partyVoters, initialWeight voter)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota)
    (hsteps :
      ∀ step, step ∈ steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hterminalNoParty :
      activePartyCandidates terminalActive partyCandidates = ∅)
    (hfinal :
      partyElectStepCount partyCandidates steps ≤ finalSeats) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats := by
  have hterminal :
      PartyQuotaTerminalBelowQuota quota
        (partyTransferPreservationTerminalState partyCandidates quota
          fractionalTally steps
          (PartyQuotaStartState partyCandidates.card initialVotes)) :=
    terminalBelowQuota_of_replaySteps_lowerBound_capacity_no_activeParty_terminal
      (partyCandidates := partyCandidates) (quota := quota)
      (fractionalTally := fractionalTally) (steps := steps)
      (startActive := startActive) (terminalActive := terminalActive)
      (initialWeight := initialWeight)
      (startState := PartyQuotaStartState partyCandidates.card initialVotes)
      hsolid hpartyVoters_subset hweight_nonneg hquota_pos htraceSteps
      htally_eq hreplay hstart hstartRemaining hmassLower
      hnoquota_on_eliminate hsteps hterminalNoParty
  exact le_trans
    (floor_votes_div_quota_le_partyElectStepCount_of_terminalBelowQuota
      (partyCandidates := partyCandidates) (quota := quota)
      (initialVotes := initialVotes) (fractionalTally := fractionalTally)
      (steps := steps) hquota_pos hvotes_nonneg hterminal)
    hfinal

/--
Source-faithful lower-bound replay for filled-seat STV rules.

The final party seat count may include both same-party quota election steps and
the terminal active same-party candidates that are filled when the source STV
rule reaches the "remaining candidates fill remaining seats" condition.
-/
theorem floor_votes_div_quota_le_finalSeats_of_replaySteps_lowerBound_capacityFill
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {quota initialVotes : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    {initialWeight : Voter → ℝ} {finalSeats : ℕ}
    (hsolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hweight_nonneg : ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (htraceSteps :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (htally_eq :
      ∀ i : Fin steps.length, ∀ candidate,
        candidate ∈ (steps.get i).beforeActive →
          fractionalTally (steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots quota
                (steps.take i.1) initialWeight)
              (steps.get i).beforeActive candidate)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstart :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hmassLower :
      0 <
          (PartyQuotaStartState partyCandidates.card
            initialVotes).remainingCandidates →
        (PartyQuotaStartState partyCandidates.card initialVotes).voteMass ≤
          ∑ voter ∈ partyVoters, initialWeight voter)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota)
    (hsteps :
      ∀ step, step ∈ steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hfinal :
      partyElectStepCount partyCandidates steps +
          (activePartyCandidates terminalActive partyCandidates).card ≤
        finalSeats) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats := by
  let terminalState :=
    partyTransferPreservationTerminalState partyCandidates quota
      fractionalTally steps
      (PartyQuotaStartState partyCandidates.card initialVotes)
  have hcapacity :
      PartyQuotaCapacityBound quota terminalState := by
    simpa [terminalState] using
      partyTransferPreservationTerminalState_capacityBound_of_replaySteps_lowerBound
        (partyCandidates := partyCandidates) (quota := quota)
        (fractionalTally := fractionalTally) (steps := steps)
        (startActive := startActive) (terminalActive := terminalActive)
        (initialWeight := initialWeight)
        (startState := PartyQuotaStartState partyCandidates.card initialVotes)
        hsolid hpartyVoters_subset hweight_nonneg hquota_pos htraceSteps
        htally_eq hreplay hstart hstartRemaining hmassLower
        hnoquota_on_eliminate
  have hremaining :
      terminalState.remainingCandidates =
        (activePartyCandidates terminalActive partyCandidates).card := by
    simpa [terminalState] using
      remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
        (partyCandidates := partyCandidates) (quota := quota)
        (fractionalTally := fractionalTally) (steps := steps)
        (startActive := startActive) (terminalActive := terminalActive)
        (state := PartyQuotaStartState partyCandidates.card initialVotes)
        hreplay hstartRemaining hsteps
  have hwinners :
      terminalState.quotaWinners =
        partyElectStepCount partyCandidates steps := by
    simpa [terminalState] using
      quotaWinners_partyTransferPreservationTerminalState_startState
        partyCandidates quota initialVotes fractionalTally steps
  have hmass :
      terminalState.voteMass =
        initialVotes - (partyElectStepCount partyCandidates steps : ℝ) *
          quota := by
    simpa [terminalState] using
      voteMass_partyTransferPreservationTerminalState_startState
        partyCandidates quota initialVotes fractionalTally steps
  have hinit :
      initialVotes =
        (terminalState.quotaWinners : ℝ) * quota + terminalState.voteMass := by
    rw [hwinners, hmass]
    ring
  have hfloor :
      ⌊initialVotes / quota⌋₊ ≤
        terminalState.quotaWinners + terminalState.remainingCandidates :=
    floor_votes_div_quota_le_quotaWinners_add_remaining_of_capacityBound
      hquota_pos hvotes_nonneg hinit hcapacity
  have hterminal_le_final :
      terminalState.quotaWinners + terminalState.remainingCandidates ≤
        finalSeats := by
    rw [hwinners, hremaining]
    exact hfinal
  exact le_trans hfloor hterminal_le_final

/--
One-party executable-trace lower-bound theorem.  It derives the concrete
source-step facts, tally agreement, active replay, nonnegative weights, and
initial party-mass lower bound from the executable candidate-level trace.
-/
theorem floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityTerminal
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {finalSeats : ℕ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight partyInitialWeight : Voter → ℝ}
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots quota
        initialActive terminalActive initialWeight)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hpartyInitialMass :
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hstartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card)
    (hnoquota_on_eliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate < quota)
    (hterminalNoParty :
      activePartyCandidates terminalActive partyCandidates = ∅)
    (hfinal :
      partyElectStepCount partyCandidates trace.steps ≤ finalSeats) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats := by
  have hinitialMass_global :
      initialVotes = ∑ voter ∈ partyVoters, initialWeight voter := by
    calc
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter :=
        hpartyInitialMass
      _ = ∑ voter ∈ partyVoters, initialWeight voter := by
        refine Finset.sum_congr rfl ?_
        intro voter hvoter
        exact (hpartyInitialWeightEq voter hvoter).symm
  have hvotes_nonneg : 0 ≤ initialVotes := by
    rw [hinitialMass_global]
    exact Finset.sum_nonneg (by
      intro voter hvoter
      exact hrun.initialWeight_nonneg voter (hpartyVoters_subset hvoter))
  have hsteps :
      ∀ step, step ∈ trace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    rcases (FractionalSTVExecutableTrace.concreteStepLaw hrun) ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota_if_elect⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  exact
    floor_votes_div_quota_le_finalSeats_of_replaySteps_lowerBound_capacityTerminal
      (partyCandidates := partyCandidates) (quota := quota)
      (initialVotes := initialVotes)
      (fractionalTally := rule.fractionalTally) (steps := trace.steps)
      (startActive := initialActive) (terminalActive := terminalActive)
      (initialWeight := initialWeight) (finalSeats := finalSeats)
      hpartySolid hpartyVoters_subset hrun.initialWeight_nonneg hrun.quota_pos
      hvotes_nonneg (FractionalSTVExecutableTrace.concreteStepLaw hrun)
      hrun.tally_eq hrun.activeReplay hstartCapacity hstartRemaining
      (by
        intro _hremaining_pos
        simpa [PartyQuotaStartState, hinitialMass_global])
      hnoquota_on_eliminate hsteps hterminalNoParty hfinal

/--
One-party executable-trace lower-bound theorem for source STV rules that fill
the remaining seats with terminal active candidates.
-/
theorem floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityFill
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {finalSeats : ℕ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight partyInitialWeight : Voter → ℝ}
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots quota
        initialActive terminalActive initialWeight)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hpartyInitialMass :
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hstartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card)
    (hnoquota_on_eliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate < quota)
    (hfinal :
      partyElectStepCount partyCandidates trace.steps +
          (activePartyCandidates terminalActive partyCandidates).card ≤
        finalSeats) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats := by
  have hinitialMass_global :
      initialVotes = ∑ voter ∈ partyVoters, initialWeight voter := by
    calc
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter :=
        hpartyInitialMass
      _ = ∑ voter ∈ partyVoters, initialWeight voter := by
        refine Finset.sum_congr rfl ?_
        intro voter hvoter
        exact (hpartyInitialWeightEq voter hvoter).symm
  have hvotes_nonneg : 0 ≤ initialVotes := by
    rw [hinitialMass_global]
    exact Finset.sum_nonneg (by
      intro voter hvoter
      exact hrun.initialWeight_nonneg voter (hpartyVoters_subset hvoter))
  have hsteps :
      ∀ step, step ∈ trace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    rcases (FractionalSTVExecutableTrace.concreteStepLaw hrun) ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota_if_elect⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  exact
    floor_votes_div_quota_le_finalSeats_of_replaySteps_lowerBound_capacityFill
      (partyCandidates := partyCandidates) (quota := quota)
      (initialVotes := initialVotes)
      (fractionalTally := rule.fractionalTally) (steps := trace.steps)
      (startActive := initialActive) (terminalActive := terminalActive)
      (initialWeight := initialWeight) (finalSeats := finalSeats)
      hpartySolid hpartyVoters_subset hrun.initialWeight_nonneg hrun.quota_pos
      hvotes_nonneg (FractionalSTVExecutableTrace.concreteStepLaw hrun)
      hrun.tally_eq hrun.activeReplay hstartCapacity hstartRemaining
      (by
        intro _hremaining_pos
        simpa [PartyQuotaStartState, hinitialMass_global])
      hnoquota_on_eliminate hsteps hfinal

/--
Prefix form of
`floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityTerminal`.

The executable source trace is restricted to `trace.steps.take n`; if that
prefix exhausts the party and its same-party election count is included in the
final seat count, it yields the same quota-floor lower bound.
-/
theorem floor_votes_div_quota_le_finalSeats_of_executableTrace_take_solidCoalition_left_lowerBound_capacityTerminal
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {finalSeats n : ℕ}
    {initialActive terminalActive prefixTerminalActive : Finset Candidate}
    {initialWeight partyInitialWeight : Voter → ℝ}
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots quota
        initialActive terminalActive initialWeight)
    (hreplay :
      STVTrace.replayStepsFrom (trace.steps.take n) initialActive
        prefixTerminalActive)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hpartyInitialMass :
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hstartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card)
    (hnoquota_on_eliminate :
      ∀ i : Fin (trace.steps.take n).length,
        ((trace.steps.take n).get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates ((trace.steps.take n).get i).beforeActive
                  partyCandidates →
              rule.fractionalTally ((trace.steps.take n).get i) candidate <
                quota)
    (hterminalNoParty :
      activePartyCandidates prefixTerminalActive partyCandidates = ∅)
    (hfinal :
      partyElectStepCount partyCandidates (trace.steps.take n) ≤ finalSeats) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats :=
  floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityTerminal
    (rule := rule)
    (trace := ({ steps := trace.steps.take n } : STVTrace Candidate))
    (allVoters := allVoters) (partyVoters := partyVoters)
    (ballots := ballots) (partyCandidates := partyCandidates)
    (quota := quota) (initialVotes := initialVotes)
    (finalSeats := finalSeats) (initialActive := initialActive)
    (terminalActive := prefixTerminalActive) (initialWeight := initialWeight)
    (partyInitialWeight := partyInitialWeight)
    (FractionalSTVExecutableTrace.of_take hrun n hreplay)
    hpartySolid hpartyVoters_subset hpartyInitialWeightEq hpartyInitialMass
    hstartCapacity hstartRemaining hnoquota_on_eliminate hterminalNoParty
    hfinal

/--
One-party executable-prefix lower-bound theorem for a prefix selected by the
`beforeActive` set of an indexed source step.

The replay endpoint is derived from the executable trace's active-set replay,
so callers only need to identify the concrete source step before which the
party has no active candidates.
-/
theorem floor_votes_div_quota_le_finalSeats_of_executableTrace_index_solidCoalition_left_lowerBound_capacityTerminal
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {allVoters partyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {finalSeats : ℕ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight partyInitialWeight : Voter → ℝ}
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots quota
        initialActive terminalActive initialWeight)
    (i : Fin trace.steps.length)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hpartyVoters_subset : partyVoters ⊆ allVoters)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hpartyInitialMass :
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hstartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card)
    (hnoquota_on_eliminate :
      ∀ j : Fin (trace.steps.take i.1).length,
        ((trace.steps.take i.1).get j).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates ((trace.steps.take i.1).get j).beforeActive
                  partyCandidates →
              rule.fractionalTally ((trace.steps.take i.1).get j) candidate <
                quota)
    (hterminalNoParty :
      activePartyCandidates (trace.steps.get i).beforeActive partyCandidates = ∅)
    (hfinal :
      partyElectStepCount partyCandidates (trace.steps.take i.1) ≤ finalSeats) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats :=
  floor_votes_div_quota_le_finalSeats_of_executableTrace_take_solidCoalition_left_lowerBound_capacityTerminal
    (rule := rule) (trace := trace) (allVoters := allVoters)
    (partyVoters := partyVoters) (ballots := ballots)
    (partyCandidates := partyCandidates) (quota := quota)
    (initialVotes := initialVotes) (finalSeats := finalSeats)
    (n := i.1) (initialActive := initialActive)
    (terminalActive := terminalActive)
    (prefixTerminalActive := (trace.steps.get i).beforeActive)
    (initialWeight := initialWeight)
    (partyInitialWeight := partyInitialWeight) hrun
    (FractionalSTVExecutableTrace.prefixReplay hrun i)
    hpartySolid hpartyVoters_subset hpartyInitialWeightEq hpartyInitialMass
    hstartCapacity hstartRemaining hnoquota_on_eliminate hterminalNoParty
    hfinal

/--
Primitive source law for a concrete STV trace, threaded through the party-state
fold. Each step is checked against the current deterministic party projection.
-/
def FractionalPartySTVPrimitiveTransferTraceLaw {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ) :
    List (STVStep Candidate) → PartyQuotaState → Prop
  | [], _state => True
  | step :: steps, state =>
      FractionalPartySTVPrimitiveTransferStepLaw partyCandidates
        (fractionalTally step) quota step state ∧
      FractionalPartySTVPrimitiveTransferTraceLaw partyCandidates quota
        fractionalTally steps
        (partyTransferPreservationNextState partyCandidates
          (fractionalTally step) quota step state)

/--
Index-wise primitive transfer facts over a concrete trace package into the
recursive primitive trace law.  This is the library bridge for source STV
implementations that verify each trace step against the deterministic party
projection state obtained by folding the preceding steps.
-/
theorem fractionalPartySTVPrimitiveTransferTraceLaw_of_getElem
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {startState : PartyQuotaState}
    (hstep :
      ∀ i : Fin steps.length,
        FractionalPartySTVPrimitiveTransferStepLaw partyCandidates
          (fractionalTally (steps.get i)) quota (steps.get i)
          (partyTransferPreservationTerminalState partyCandidates quota
            fractionalTally (steps.take i.1) startState)) :
    FractionalPartySTVPrimitiveTransferTraceLaw partyCandidates quota
      fractionalTally steps startState := by
  induction steps generalizing startState with
  | nil =>
      simp [FractionalPartySTVPrimitiveTransferTraceLaw]
  | cons step steps ih =>
      constructor
      · have h0 := hstep ⟨0, by simp⟩
        simpa [partyTransferPreservationTerminalState] using h0
      · apply ih
        intro i
        have hsucc := hstep ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
        simpa [partyTransferPreservationTerminalState, Nat.succ_eq_add_one]
          using hsucc

/--
Source trace law for one party projection of a concrete fractional STV trace.

Each concrete step is checked against the deterministic party state obtained by
folding the preceding concrete steps. This is the trace-level form expected
from a source STV implementation or audited replay.
-/
def FractionalPartySTVSourceTraceLaw {Candidate : Type*}
    [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (quota : ℝ)
    (fractionalTally : STVStep Candidate → Candidate → ℝ)
    (steps : List (STVStep Candidate)) (startState : PartyQuotaState) : Prop :=
  ∀ i : Fin steps.length,
    FractionalPartySTVSourceStepLaw partyCandidates
      (fractionalTally (steps.get i)) quota (steps.get i)
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally (steps.take i.1) startState)

/--
Concrete per-step laws plus party projection-state identities construct the
source trace law for one party.
-/
theorem fractionalPartySTVSourceTraceLaw_of_concreteStepLaw
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {startState : PartyQuotaState}
    (hstep :
      ∀ i : Fin steps.length,
        FractionalSTVConcreteStepLaw
          (fractionalTally (steps.get i)) quota (steps.get i))
    (hprojection :
      ∀ i : Fin steps.length,
        FractionalPartySTVProjectionStateLaw partyCandidates
          (fractionalTally (steps.get i)) (steps.get i)
          (partyTransferPreservationTerminalState partyCandidates quota
            fractionalTally (steps.take i.1) startState)) :
    FractionalPartySTVSourceTraceLaw partyCandidates quota fractionalTally
      steps startState := by
  intro i
  exact fractionalPartySTVSourceStepLaw_of_concreteStepLaw
    (hstep i) (hprojection i)

/--
An executable fractional STV trace, restricted to a solid coalition in a
two-party election, supplies the source-step trace law for that party.

The theorem is phrased for the left coalition; applying it with the voter and
candidate partitions swapped gives the symmetric party.
-/
theorem fractionalPartySTVSourceTraceLaw_of_executableTrace_solidCoalition_left
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {trace : STVTrace Candidate}
    {allVoters partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {quota initialVotes : ℝ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight partyInitialWeight : Voter → ℝ}
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots quota
        initialActive terminalActive initialWeight)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hpartyInitialMass :
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card) :
    FractionalPartySTVSourceTraceLaw partyCandidates quota rule.fractionalTally
      trace.steps (PartyQuotaStartState partyCandidates.card initialVotes) := by
  have htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i)) quota
          (trace.steps.get i) :=
    FractionalSTVExecutableTrace.concreteStepLaw hrun
  have hordinarySteps :
      ∀ step, step ∈ trace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    rcases htraceSteps ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota_if_elect⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  have hpartyActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hpartyActive ⟨n, hn⟩
  have hotherActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hotherActive ⟨n, hn⟩
  have hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots quota
                (trace.steps.take i.1) partyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_party : candidate ∈ partyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_other : candidate ∉ otherPartyCandidates := by
      intro hcandidate_other
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hother_empty :
        Ballot.activeSupport otherPartyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hotherSolid (hotherActive i) hcandidate_not_other
    have hweight_eq :
        ∀ voter, voter ∈ partyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots quota
              (trace.steps.take i.1) initialWeight voter =
            fractionalSTVWeightAfterSteps partyVoters ballots quota
              (trace.steps.take i.1) partyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := partyVoters)
        (otherVoters := otherPartyVoters) (ballots := ballots)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        (quota := quota) (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := partyInitialWeight)
        hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
        hotherSolid
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        hpartyInitialWeightEq
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots quota
              (trace.steps.take i.1) initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hrun.tally_eq i candidate hcandidate_active
      _ =
          fractionalActiveTally partyVoters ballots
            (fractionalSTVWeightAfterSteps partyVoters ballots quota
              (trace.steps.take i.1) partyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := partyVoters)
          (voters₂ := otherPartyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots quota
              (trace.steps.take i.1) initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps partyVoters ballots quota
              (trace.steps.take i.1) partyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition hvoterDisjoint hother_empty hweight_eq
  have hpartyWeightTrace :
      FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
        quota trace.steps partyInitialWeight :=
    fractionalSTVPartyWeightTraceLaw_of_concreteStepLaw_solidCoalition
      (voters := partyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates) (quota := quota)
      (fractionalTally := rule.fractionalTally)
      (steps := trace.steps) (initialWeight := partyInitialWeight)
      hpartySolid htraceSteps hpartyActive hpartyTallyEq
  apply fractionalPartySTVSourceTraceLaw_of_concreteStepLaw
    (partyCandidates := partyCandidates) (quota := quota)
    (fractionalTally := rule.fractionalTally)
    (steps := trace.steps)
    (startState := PartyQuotaStartState partyCandidates.card initialVotes)
    htraceSteps
  intro i
  have hprefixReplay :
      STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
        (trace.steps.get i).beforeActive :=
    STVTrace.replaysFrom_take_get_beforeActive hrun.activeReplay i
  have hprefixSteps :
      ∀ step, step ∈ trace.steps.take i.1 →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    exact hordinarySteps step (List.mem_of_mem_take hstep)
  have hremaining :
      (partyTransferPreservationTerminalState partyCandidates quota
        rule.fractionalTally (trace.steps.take i.1)
        (PartyQuotaStartState partyCandidates.card initialVotes)).remainingCandidates =
        (activePartyCandidates (trace.steps.get i).beforeActive
          partyCandidates).card :=
    remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
      (partyCandidates := partyCandidates) (quota := quota)
      (fractionalTally := rule.fractionalTally)
      (steps := trace.steps.take i.1)
      (startActive := initialActive)
      (terminalActive := (trace.steps.get i).beforeActive)
      (state := PartyQuotaStartState partyCandidates.card initialVotes)
      hprefixReplay hstartRemaining hprefixSteps
  have hmass :
      (partyTransferPreservationTerminalState partyCandidates quota
        rule.fractionalTally (trace.steps.take i.1)
        (PartyQuotaStartState partyCandidates.card initialVotes)).voteMass =
        ∑ voter ∈ partyVoters,
          fractionalSTVWeightAfterSteps partyVoters ballots quota
            (trace.steps.take i.1) partyInitialWeight voter :=
    voteMass_partyTransferPreservationTerminalState_eq_sum_fractionalSTVWeightAfterSteps
      (voters := partyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates) (quota := quota)
      (initialVotes := initialVotes) (fractionalTally := rule.fractionalTally)
      (steps := trace.steps.take i.1)
      (initialWeight := partyInitialWeight)
      hpartyInitialMass hrun.quota_pos
      (fractionalSTVPartyWeightTraceLaw_take hpartyWeightTrace i.1)
  exact
    fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass_of_tally_eq
      (voters := partyVoters) (ballots := ballots)
      (weight :=
        fractionalSTVWeightAfterSteps partyVoters ballots quota
          (trace.steps.take i.1) partyInitialWeight)
      (partyCandidates := partyCandidates)
      (fractionalTally := rule.fractionalTally (trace.steps.get i))
      (step := trace.steps.get i)
      (before :=
        partyTransferPreservationTerminalState partyCandidates quota
          rule.fractionalTally (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card initialVotes))
      hpartySolid (hpartyActive i) (hpartyTallyEq i) hremaining hmass

/--
Source trace laws preserve the party capacity bound when same-party
eliminations occur only in rounds with no active same-party candidate at quota.
-/
theorem partyTransferPreservationTerminalState_capacityBound_of_sourceTraceLaw
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {startState : PartyQuotaState}
    (hlaw :
      FractionalPartySTVSourceTraceLaw partyCandidates quota fractionalTally
        steps startState)
    (hstart : PartyQuotaCapacityBound quota startState)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota) :
    PartyQuotaCapacityBound quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState) := by
  induction steps generalizing startState with
  | nil =>
      simpa [partyTransferPreservationTerminalState] using hstart
  | cons step steps ih =>
      let nextState :=
        partyTransferPreservationNextState partyCandidates
          (fractionalTally step) quota step startState
      have hstepSource :
          FractionalPartySTVSourceStepLaw partyCandidates
            (fractionalTally step) quota step startState := by
        have h0 := hlaw ⟨0, by simp⟩
        simpa [partyTransferPreservationTerminalState] using h0
      have hprimitive :
          FractionalPartySTVPrimitiveTransferStepLaw partyCandidates
            (fractionalTally step) quota step startState :=
        primitiveTransferStepLaw_of_sourceStepLaw hstepSource
      have hpres :
          FractionalPartySTVTransferPreservationStep partyCandidates
            (fractionalTally step) quota step startState nextState := by
        simpa [nextState] using
          transferPreservationStep_of_primitiveStepLaw hprimitive
      have hnextBound : PartyQuotaCapacityBound quota nextState := by
        rcases hpres with ⟨_hremove, helect | heliminate | houtside⟩
        · rcases helect with
            ⟨_hkind, _focused, _hfocus, _hparty, helectStep⟩
          exact PartyQuotaCapacityBound.of_electStep hstart
            (partyQuotaElectStep_of_fractionalPartySTVElectStep
              (fractionalPartySTVElectStep_of_withTally helectStep))
        · rcases heliminate with
            ⟨hkind, focused, hfocus, hparty, heliminateStep⟩
          have hpartyActiveStep :
              ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
            rcases hstepSource with
              ⟨_hremove, sourceFocused, hsourceFocus, hsourceActive,
                _hnonneg, _hremaining, _hmass, _hfocused_party_law⟩
            have hsource_eq : sourceFocused = focused :=
              Option.some.inj (hsourceFocus.symm.trans hfocus)
            subst sourceFocused
            exact ⟨focused, hparty, hsourceActive⟩
          have hmass_lt :
              startState.voteMass <
                (startState.remainingCandidates : ℝ) * quota :=
            voteMass_lt_remaining_mul_quota_of_sourceStepLaw_forall_activeParty_lt
              hstepSource hpartyActiveStep
              (hnoquota_on_eliminate ⟨0, by simp⟩ hkind)
          exact
            PartyQuotaCapacityBound.of_eliminateStep_of_voteMass_lt_remaining_mul_quota
              hmass_lt
              (partyQuotaEliminateStep_of_fractionalPartySTVEliminateStep
                (fractionalPartySTVEliminateStep_of_withTally
                  (focusedTally := fractionalTally step focused)
                  heliminateStep))
        · rcases houtside with ⟨_focused, _hfocus, _hnot_party, hsame⟩
          simpa [hsame] using hstart
      have htailLaw :
          FractionalPartySTVSourceTraceLaw partyCandidates quota
            fractionalTally steps nextState := by
        intro i
        have hsucc :=
          hlaw ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
        simpa [FractionalPartySTVSourceTraceLaw,
          partyTransferPreservationTerminalState, Nat.succ_eq_add_one,
          nextState] using hsucc
      have htailNoquota :
          ∀ i : Fin steps.length,
            (steps.get i).kind = StepKind.eliminate →
              ∀ candidate,
                candidate ∈
                    activePartyCandidates (steps.get i).beforeActive
                      partyCandidates →
                  fractionalTally (steps.get i) candidate < quota := by
        intro i hkind candidate hcandidate
        exact
          hnoquota_on_eliminate
            ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
            (by simpa using hkind) candidate (by simpa using hcandidate)
      simpa [partyTransferPreservationTerminalState, nextState] using
        ih htailLaw hnextBound htailNoquota

/--
If a source trace preserves the party capacity bound and its active-set replay
ends with no active same-party candidates, then the deterministic party-state
fold is terminal below quota.
-/
theorem terminalBelowQuota_of_sourceTraceLaw_capacityBound_no_activeParty_terminal
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {startState : PartyQuotaState}
    {startActive terminalActive : Finset Candidate}
    (hlaw :
      FractionalPartySTVSourceTraceLaw partyCandidates quota fractionalTally
        steps startState)
    (hstart : PartyQuotaCapacityBound quota startState)
    (hnoquota_on_eliminate :
      ∀ i : Fin steps.length,
        (steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (steps.get i).beforeActive
                  partyCandidates →
              fractionalTally (steps.get i) candidate < quota)
    (hreplay : STVTrace.replayStepsFrom steps startActive terminalActive)
    (hstartRemaining :
      startState.remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hsteps :
      ∀ step, step ∈ steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hterminalNoParty :
      activePartyCandidates terminalActive partyCandidates = ∅) :
    PartyQuotaTerminalBelowQuota quota
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState) := by
  have hcapacity :
      PartyQuotaCapacityBound quota
        (partyTransferPreservationTerminalState partyCandidates quota
          fractionalTally steps startState) :=
    partyTransferPreservationTerminalState_capacityBound_of_sourceTraceLaw
      hlaw hstart hnoquota_on_eliminate
  have hremaining :
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState).remainingCandidates =
        (activePartyCandidates terminalActive partyCandidates).card :=
    remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
      (partyCandidates := partyCandidates) (quota := quota)
      (fractionalTally := fractionalTally) (steps := steps)
      (startActive := startActive) (terminalActive := terminalActive)
      (state := startState) hreplay hstartRemaining hsteps
  have hremaining_zero :
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState).remainingCandidates = 0 := by
    rw [hremaining, hterminalNoParty]
    simp
  exact
    PartyQuotaCapacityBound.terminalBelowQuota_of_remaining_zero hcapacity
      hremaining_zero

/--
Source trace laws imply the primitive transfer trace law used by the
party-quota replay.
-/
theorem fractionalPartySTVPrimitiveTransferTraceLaw_of_sourceTraceLaw
    {Candidate : Type*} [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {startState : PartyQuotaState}
    (hlaw :
      FractionalPartySTVSourceTraceLaw partyCandidates quota fractionalTally
        steps startState) :
    FractionalPartySTVPrimitiveTransferTraceLaw partyCandidates quota
      fractionalTally steps startState :=
  fractionalPartySTVPrimitiveTransferTraceLaw_of_getElem
    (fun i => primitiveTransferStepLaw_of_sourceStepLaw (hlaw i))

/--
Primitive per-step transfer laws construct the source-shaped preservation path.
-/
theorem transferPreservationPath_of_primitiveTraceLaw {Candidate : Type*}
    [DecidableEq Candidate]
    {partyCandidates : Finset Candidate} {quota : ℝ}
    {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {startState : PartyQuotaState}
    (hlaw :
      FractionalPartySTVPrimitiveTransferTraceLaw partyCandidates quota
        fractionalTally steps startState) :
    FractionalPartySTVTransferPreservationPath partyCandidates quota
      fractionalTally steps startState
      (partyTransferPreservationTerminalState partyCandidates quota
        fractionalTally steps startState) := by
  induction steps generalizing startState with
  | nil =>
      exact FractionalPartySTVTransferPreservationPath.nil startState
  | cons step steps ih =>
      rcases hlaw with ⟨hstep, hrest⟩
      exact FractionalPartySTVTransferPreservationPath.cons
        (transferPreservationStep_of_primitiveStepLaw hstep)
        (ih hrest)

/--
The source-shaped transfer-preservation path projects to the same-party
quota-process path, dropping outside-party stutter steps.
-/
theorem partyQuotaPath_of_transferPreservationPath {Candidate : Type*}
    [DecidableEq Candidate] {partyCandidates : Finset Candidate}
    {quota : ℝ} {fractionalTally : STVStep Candidate → Candidate → ℝ}
    {steps : List (STVStep Candidate)} {before after : PartyQuotaState}
    (hpath :
      FractionalPartySTVTransferPreservationPath
        partyCandidates quota fractionalTally steps before after) :
    Relation.ReflTransGen (PartyQuotaStep quota) before after := by
  induction hpath with
  | nil state =>
      exact Relation.ReflTransGen.refl
  | cons hstep _hrest ih =>
      rcases partyQuotaStep_or_eq_of_transferPreservationStep hstep with
        hquotaStep | hsame
      · exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single hquotaStep) ih
      · subst hsame
        exact ih

/--
Source-shaped replay certificate for one party: the analyzed shared STV steps
preserve party vote mass except when a same-party quota winner retains exactly
one quota.
-/
structure FractionalPartySTVTransferPreservationReplay {Candidate : Type*}
    [DecidableEq Candidate] (initialVotes quota : ℝ) where
  partyCandidates : Finset Candidate
  steps : List (STVStep Candidate)
  fractionalTally : STVStep Candidate → Candidate → ℝ
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : FractionalPartySTVTransferPreservationPath partyCandidates quota
    fractionalTally steps startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/--
Transfer-rule-parametric version of the source-shaped preservation replay.
-/
structure FractionalPartySTVTransferRulePreservationReplay {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (initialVotes quota : ℝ) where
  partyCandidates : Finset Candidate
  steps : List (STVStep Candidate)
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : FractionalPartySTVTransferPreservationPath partyCandidates quota
    rule.fractionalTally steps startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/--
A source-shaped transfer-preservation replay yields the terminal same-party
quota-process certificate used by solid-coalition STV proofs.
-/
def partyQuotaProcess_of_transferPreservationReplay {Candidate : Type*}
    [DecidableEq Candidate] {initialVotes quota : ℝ}
    (replay :
      FractionalPartySTVTransferPreservationReplay
        (Candidate := Candidate) initialVotes quota) :
    PartyQuotaProcess initialVotes quota where
  startState := replay.startState
  terminalState := replay.terminalState
  startInvariant := replay.startInvariant
  path := partyQuotaPath_of_transferPreservationPath replay.path
  terminalBelowQuota := replay.terminalBelowQuota

/--
A transfer-rule-parametric preservation replay yields the terminal same-party
quota-process certificate used by solid-coalition STV proofs.
-/
def partyQuotaProcess_of_transferRulePreservationReplay {Candidate : Type*}
    [DecidableEq Candidate] {rule : FractionalSTVTransferRule Candidate}
    {initialVotes quota : ℝ}
    (replay :
      FractionalPartySTVTransferRulePreservationReplay
        (Candidate := Candidate) rule initialVotes quota) :
    PartyQuotaProcess initialVotes quota where
  startState := replay.startState
  terminalState := replay.terminalState
  startInvariant := replay.startInvariant
  path := partyQuotaPath_of_transferPreservationPath replay.path
  terminalBelowQuota := replay.terminalBelowQuota

/-- If a party has a remaining candidate with at least one quota of vote mass, an elect step exists. -/
theorem exists_partyQuotaElectStep {quota : ℝ} {before : PartyQuotaState}
    (hquota_le : quota ≤ before.voteMass)
    (hremaining : 0 < before.remainingCandidates) :
    ∃ after, PartyQuotaElectStep quota before after := by
  refine ⟨{
    remainingCandidates := before.remainingCandidates - 1
    quotaWinners := before.quotaWinners + 1
    voteMass := before.voteMass - quota
  }, hquota_le, ?_, rfl, rfl⟩
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hremaining)

/-- If a party has a remaining candidate, an elimination step exists. -/
theorem exists_partyQuotaEliminateStep {quota : ℝ} {before : PartyQuotaState}
    (hremaining : 0 < before.remainingCandidates) :
    ∃ after, PartyQuotaEliminateStep quota before after := by
  refine ⟨{
    remainingCandidates := before.remainingCandidates - 1
    quotaWinners := before.quotaWinners
    voteMass := before.voteMass
  }, ?_, rfl, rfl⟩
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hremaining)

/-- If a party's vote mass is not at least quota, it is terminal for this proof. -/
theorem PartyQuotaTerminalBelowQuota.of_not_quota_le {quota : ℝ}
    {state : PartyQuotaState} (hquota_not_le : ¬ quota ≤ state.voteMass) :
    PartyQuotaTerminalBelowQuota quota state :=
  not_le.mp hquota_not_le

/--
Starting from all same-party votes in one process state, repeated elect steps
can realize any number of quota winners whose full quotas fit inside the
initial vote mass and candidate supply.
-/
theorem exists_partyQuotaElectPath {initialVotes quota : ℝ}
    (hquota_pos : 0 < quota) :
    ∀ {quotaSeats remainingCandidates : ℕ},
      quotaSeats ≤ remainingCandidates →
      (quotaSeats : ℝ) * quota ≤ initialVotes →
      ∃ state,
        Relation.ReflTransGen (PartyQuotaStep quota)
          (PartyQuotaStartState remainingCandidates initialVotes) state ∧
        state.remainingCandidates = remainingCandidates - quotaSeats ∧
        state.quotaWinners = quotaSeats ∧
        state.voteMass = initialVotes - (quotaSeats : ℝ) * quota := by
  intro quotaSeats
  induction quotaSeats with
  | zero =>
      intro remainingCandidates _hcandidates _hvotes
      refine ⟨PartyQuotaStartState remainingCandidates initialVotes,
        Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp [PartyQuotaStartState]
      · simp [PartyQuotaStartState]
      · simp [PartyQuotaStartState]
  | succ quotaSeats ih =>
      intro remainingCandidates hcandidates hvotes
      have hprev_candidates : quotaSeats ≤ remainingCandidates := by
        omega
      have hprev_votes : (quotaSeats : ℝ) * quota ≤ initialVotes := by
        have hcast_le : (quotaSeats : ℝ) ≤ ((quotaSeats + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ quotaSeats
        nlinarith
      rcases ih hprev_candidates hprev_votes with
        ⟨state, hpath, hremaining, hwinners, hmass⟩
      have hstate_remaining_pos : 0 < state.remainingCandidates := by
        rw [hremaining]
        have hlt : quotaSeats < remainingCandidates := by
          exact Nat.lt_of_succ_le hcandidates
        exact Nat.sub_pos_of_lt hlt
      have hquota_le : quota ≤ state.voteMass := by
        rw [hmass]
        have hvotes_succ : (((quotaSeats + 1 : ℕ) : ℝ) * quota) ≤
            initialVotes := hvotes
        norm_num [Nat.cast_add, Nat.cast_one] at hvotes_succ
        nlinarith
      rcases exists_partyQuotaElectStep hquota_le hstate_remaining_pos with
        ⟨after, hstep⟩
      have hsingle :
          Relation.ReflTransGen (PartyQuotaStep quota) state after :=
        Relation.ReflTransGen.single (Or.inl hstep)
      refine ⟨after, Relation.ReflTransGen.trans hpath hsingle, ?_, ?_, ?_⟩
      · rcases hstep with ⟨_hquota, hafter_remaining, _hwinners, _hmass⟩
        have hafter_succ :
            after.remainingCandidates + 1 = remainingCandidates - quotaSeats := by
          simpa [hremaining] using hafter_remaining
        omega
      · rcases hstep with ⟨_hquota, _hremaining, hafter_winners, _hmass⟩
        rw [hafter_winners, hwinners]
      · rcases hstep with ⟨_hquota, _hremaining, _hwinners, hafter_mass⟩
        rw [hafter_mass, hmass]
        have hsucc_cast : (((quotaSeats + 1 : ℕ) : ℝ) = (quotaSeats : ℝ) + 1) := by
          norm_num [Nat.cast_add, Nat.cast_one, add_comm]
        rw [hsucc_cast]
        ring

/--
With enough same-party candidates, the elect-step recurrence reaches the
canonical floor-quota terminal state.
-/
theorem exists_partyQuotaProcess_floor {initialVotes quota : ℝ}
    {remainingCandidates : ℕ}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (hcandidates : ⌊initialVotes / quota⌋₊ ≤ remainingCandidates) :
    ∃ process : PartyQuotaProcess initialVotes quota,
      process.terminalState.quotaWinners = ⌊initialVotes / quota⌋₊ ∧
      process.terminalState.voteMass =
        initialVotes - (⌊initialVotes / quota⌋₊ : ℝ) * quota := by
  let quotaSeats : ℕ := ⌊initialVotes / quota⌋₊
  have hres :
      QuotaResidualBound quotaSeats initialVotes quota := by
    simpa [quotaSeats] using
      quotaResidualBound_floor_votes_div_quota hquota_pos hvotes_nonneg
  rcases hres with ⟨_hquota_pos, residual, hres_nonneg, hres_lt, hinit⟩
  have hvotes_floor : (quotaSeats : ℝ) * quota ≤ initialVotes := by
    nlinarith
  rcases exists_partyQuotaElectPath (initialVotes := initialVotes)
      (quota := quota) hquota_pos hcandidates hvotes_floor with
    ⟨terminalState, hpath, _hremaining, hwinners, hmass⟩
  have hterminal : PartyQuotaTerminalBelowQuota quota terminalState := by
    change terminalState.voteMass < quota
    rw [hmass]
    have hresidual_eq :
        initialVotes - (⌊initialVotes / quota⌋₊ : ℝ) * quota = residual := by
      simpa [quotaSeats] using
        (by nlinarith : initialVotes - (quotaSeats : ℝ) * quota = residual)
    rw [hresidual_eq]
    exact hres_lt
  refine ⟨{
    startState := PartyQuotaStartState remainingCandidates initialVotes
    terminalState := terminalState
    startInvariant := PartyQuotaInvariant.start hvotes_nonneg
    path := hpath
    terminalBelowQuota := hterminal
  }, ?_, ?_⟩
  · simpa [quotaSeats] using hwinners
  · simpa [quotaSeats] using hmass

/-- Elect steps preserve the quota decomposition invariant. -/
theorem PartyQuotaInvariant.of_electStep {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hstep : PartyQuotaElectStep quota before after) :
    PartyQuotaInvariant initialVotes quota after := by
  rcases hinv with ⟨hinit, hmass_nonneg⟩
  rcases hstep with ⟨hquota_le, _hcand, hwinners, hmass⟩
  constructor
  · rw [hinit, hwinners, hmass]
    norm_num
    ring
  · rw [hmass]
    linarith

/-- Elimination steps preserve the quota decomposition invariant. -/
theorem PartyQuotaInvariant.of_eliminateStep {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hstep : PartyQuotaEliminateStep quota before after) :
    PartyQuotaInvariant initialVotes quota after := by
  rcases hinv with ⟨hinit, hmass_nonneg⟩
  rcases hstep with ⟨_hcand, hwinners, hmass⟩
  constructor
  · rw [hinit, hwinners, hmass]
  · rw [hmass]
    exact hmass_nonneg

/-- Any same-party quota process step preserves the quota decomposition invariant. -/
theorem PartyQuotaInvariant.of_step {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hstep : PartyQuotaStep quota before after) :
    PartyQuotaInvariant initialVotes quota after := by
  rcases hstep with hstep | hstep
  · exact PartyQuotaInvariant.of_electStep hinv hstep
  · exact PartyQuotaInvariant.of_eliminateStep hinv hstep

/--
Reachability along a same-party quota process preserves the quota decomposition
invariant.
-/
theorem PartyQuotaInvariant.of_reflTransGen {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hpath : Relation.ReflTransGen (PartyQuotaStep quota) before after) :
    PartyQuotaInvariant initialVotes quota after := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl => exact hinv
  | single hstep => exact PartyQuotaInvariant.of_step hinv hstep
  | trans _ _ hleft hright => exact hright (hleft hinv)

namespace PartyQuotaProcess

/-- The terminal state of a certified same-party process satisfies the invariant. -/
theorem terminalInvariant {initialVotes quota : ℝ}
    (process : PartyQuotaProcess initialVotes quota) :
    PartyQuotaInvariant initialVotes quota process.terminalState :=
  PartyQuotaInvariant.of_reflTransGen process.startInvariant process.path

end PartyQuotaProcess

/--
A terminal same-party quota process provides a residual certificate for its
number of quota winners.
-/
theorem quotaResidualBound_of_partyQuotaInvariant_of_terminalBelowQuota
    {initialVotes quota : ℝ} {state : PartyQuotaState}
    (hquota_pos : 0 < quota)
    (hinv : PartyQuotaInvariant initialVotes quota state)
    (hterminal : PartyQuotaTerminalBelowQuota quota state) :
    QuotaResidualBound state.quotaWinners initialVotes quota := by
  exact ⟨hquota_pos, state.voteMass, hinv.2, hterminal, hinv.1⟩

/--
If final same-party STV seats include all quota winners from a terminal
same-party process, then the final seat count has the quota lower-bound witness.
-/
theorem quotaLowerBoundWitness_of_partyQuotaProcess {finalSeats : ℕ}
    {initialVotes quota : ℝ} {state : PartyQuotaState}
    (hquota_pos : 0 < quota)
    (hfinal : state.quotaWinners ≤ finalSeats)
    (hinv : PartyQuotaInvariant initialVotes quota state)
    (hterminal : PartyQuotaTerminalBelowQuota quota state) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  ⟨state.quotaWinners, hfinal,
    quotaResidualBound_of_partyQuotaInvariant_of_terminalBelowQuota
      hquota_pos hinv hterminal⟩

/--
A terminal fractional party replay directly provides the quota lower-bound
witness for its number of same-party quota winners.
-/
theorem quotaLowerBoundWitness_of_fractionalPartySTVReplay {finalSeats : ℕ}
    {initialVotes quota : ℝ}
    (replay : FractionalPartySTVReplay initialVotes quota)
    (hquota_pos : 0 < quota)
    (hfinal : replay.terminalState.quotaWinners ≤ finalSeats) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  quotaLowerBoundWitness_of_partyQuotaProcess hquota_pos hfinal
    (PartyQuotaInvariant.of_reflTransGen replay.startInvariant
      (partyQuotaPath_of_fractionalPartySTVPath replay.path))
    replay.terminalBelowQuota

/--
A shared-trace fractional party replay directly provides the quota lower-bound
witness used by solid-coalition STV proofs.
-/
theorem quotaLowerBoundWitness_of_fractionalPartySTVTraceReplay
    {Candidate : Type*} [DecidableEq Candidate] {finalSeats : ℕ}
    {initialVotes quota : ℝ}
    (replay :
      FractionalPartySTVTraceReplay
        (Candidate := Candidate) initialVotes quota)
    (hquota_pos : 0 < quota)
    (hfinal : replay.terminalState.quotaWinners ≤ finalSeats) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  quotaLowerBoundWitness_of_fractionalPartySTVReplay
    (fractionalPartySTVReplay_of_traceReplay replay) hquota_pos hfinal

/--
If final same-party STV seats include all quota winners from a certified
same-party process, then the final seat count has the quota lower-bound witness.
-/
theorem quotaLowerBoundWitness_of_partyQuotaProcessCertificate {finalSeats : ℕ}
    {initialVotes quota : ℝ}
    (process : PartyQuotaProcess initialVotes quota)
    (hquota_pos : 0 < quota)
    (hfinal : process.terminalState.quotaWinners ≤ finalSeats) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  quotaLowerBoundWitness_of_partyQuotaProcess hquota_pos hfinal
    process.terminalInvariant process.terminalBelowQuota

/--
Source-primitive candidate trace outcome for one party.

The path starts from the actual party candidate count and initial party vote
mass, follows the shared candidate-level STV trace under the supplied transfer
rule, and ends below quota with all quota winners included in the final party
seat count.
-/
def PartyTransferPreservationTraceOutcome {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyCandidates : Finset Candidate)
    (initialVotes quota : ℝ) (finalSeats : ℕ) : Prop :=
  ∃ terminalState,
    FractionalPartySTVTransferPreservationPath partyCandidates quota
      rule.fractionalTally trace.steps
      (PartyQuotaStartState partyCandidates.card initialVotes) terminalState ∧
    PartyQuotaTerminalBelowQuota quota terminalState ∧
    terminalState.quotaWinners ≤ finalSeats

/--
Primitive candidate trace outcome for one party.

Unlike `PartyTransferPreservationTraceOutcome`, this does not take a replay
path as input. The path is obtained by folding the concrete trace through the
deterministic party-state transition and checking the primitive per-step
transfer laws.
-/
def PartyTransferPrimitiveTraceOutcome {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyCandidates : Finset Candidate)
    (initialVotes quota : ℝ) (finalSeats : ℕ) : Prop :=
  let startState := PartyQuotaStartState partyCandidates.card initialVotes
  let terminalState :=
    partyTransferPreservationTerminalState partyCandidates quota
      rule.fractionalTally trace.steps startState
  FractionalPartySTVPrimitiveTransferTraceLaw partyCandidates quota
      rule.fractionalTally trace.steps startState ∧
    PartyQuotaTerminalBelowQuota quota terminalState ∧
    terminalState.quotaWinners ≤ finalSeats

/--
Source-step candidate trace outcome for one party.

This is the trace-step version of
`PartyTransferPrimitiveTraceOutcome`: each concrete trace step supplies active
focused-candidate, nonnegative tally, same-party mass, and quota-election
facts, from which the primitive transfer trace is derived internally.
-/
def PartyTransferSourceTraceOutcome {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyCandidates : Finset Candidate)
    (initialVotes quota : ℝ) (finalSeats : ℕ) : Prop :=
  let startState := PartyQuotaStartState partyCandidates.card initialVotes
  let terminalState :=
    partyTransferPreservationTerminalState partyCandidates quota
      rule.fractionalTally trace.steps startState
  FractionalPartySTVSourceTraceLaw partyCandidates quota
      rule.fractionalTally trace.steps startState ∧
    PartyQuotaTerminalBelowQuota quota terminalState ∧
    terminalState.quotaWinners ≤ finalSeats

/--
Source-step trace outcomes construct primitive transfer trace outcomes.
-/
theorem partyTransferPrimitiveTraceOutcome_of_sourceTraceOutcome
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates : Finset Candidate} {initialVotes quota : ℝ}
    {finalSeats : ℕ}
    (houtcome :
      PartyTransferSourceTraceOutcome
        rule trace partyCandidates initialVotes quota finalSeats) :
    PartyTransferPrimitiveTraceOutcome
      rule trace partyCandidates initialVotes quota finalSeats := by
  dsimp [PartyTransferSourceTraceOutcome,
    PartyTransferPrimitiveTraceOutcome] at houtcome ⊢
  rcases houtcome with ⟨hlaw, hterminal, hfinal⟩
  exact ⟨fractionalPartySTVPrimitiveTransferTraceLaw_of_sourceTraceLaw hlaw,
    hterminal, hfinal⟩

/--
Primitive trace laws construct the existing transfer-preservation trace
outcome, discharging the replay/path object internally.
-/
theorem partyTransferPreservationTraceOutcome_of_primitiveTraceOutcome
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates : Finset Candidate} {initialVotes quota : ℝ}
    {finalSeats : ℕ}
    (houtcome :
      PartyTransferPrimitiveTraceOutcome
        rule trace partyCandidates initialVotes quota finalSeats) :
    PartyTransferPreservationTraceOutcome
      rule trace partyCandidates initialVotes quota finalSeats := by
  dsimp [PartyTransferPrimitiveTraceOutcome,
    PartyTransferPreservationTraceOutcome] at houtcome ⊢
  rcases houtcome with ⟨hlaw, hterminal, hfinal⟩
  exact ⟨_,
    transferPreservationPath_of_primitiveTraceLaw hlaw,
    hterminal, hfinal⟩

/--
Source-step trace outcomes construct the transfer-preservation trace outcome,
discharging both the primitive trace law and the replay/path object internally.
-/
theorem partyTransferPreservationTraceOutcome_of_sourceTraceOutcome
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates : Finset Candidate} {initialVotes quota : ℝ}
    {finalSeats : ℕ}
    (houtcome :
      PartyTransferSourceTraceOutcome
        rule trace partyCandidates initialVotes quota finalSeats) :
    PartyTransferPreservationTraceOutcome
      rule trace partyCandidates initialVotes quota finalSeats :=
  partyTransferPreservationTraceOutcome_of_primitiveTraceOutcome
    (partyTransferPrimitiveTraceOutcome_of_sourceTraceOutcome houtcome)

/--
Build a source-primitive party trace outcome from a source trace law and the
capacity-terminal proof obligations produced by a quota-respecting STV
simulator prefix.
-/
theorem partyTransferPreservationTraceOutcome_of_sourceTraceLaw_capacityTerminal
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates : Finset Candidate} {initialVotes quota : ℝ}
    {finalSeats : ℕ} {startActive terminalActive : Finset Candidate}
    (hlaw :
      FractionalPartySTVSourceTraceLaw partyCandidates quota
        rule.fractionalTally trace.steps
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hnoquota_on_eliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate < quota)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates startActive partyCandidates).card)
    (hsteps :
      ∀ step, step ∈ trace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hterminalNoParty :
      activePartyCandidates terminalActive partyCandidates = ∅)
    (hfinal :
      partyElectStepCount partyCandidates trace.steps ≤ finalSeats) :
    PartyTransferPreservationTraceOutcome
      rule trace partyCandidates initialVotes quota finalSeats := by
  have hterminal :
      PartyQuotaTerminalBelowQuota quota
        (partyTransferPreservationTerminalState partyCandidates quota
          rule.fractionalTally trace.steps
          (PartyQuotaStartState partyCandidates.card initialVotes)) :=
    terminalBelowQuota_of_sourceTraceLaw_capacityBound_no_activeParty_terminal
      (partyCandidates := partyCandidates) (quota := quota)
      (fractionalTally := rule.fractionalTally) (steps := trace.steps)
      (startState := PartyQuotaStartState partyCandidates.card initialVotes)
      (startActive := startActive) (terminalActive := terminalActive)
      hlaw hstartCapacity hnoquota_on_eliminate hreplay hstartRemaining
      hsteps hterminalNoParty
  have hfinal_terminal :
      (partyTransferPreservationTerminalState partyCandidates quota
        rule.fractionalTally trace.steps
        (PartyQuotaStartState partyCandidates.card initialVotes)).quotaWinners ≤
        finalSeats :=
    quotaWinners_terminalState_le_of_partyElectStepCount_le
      (partyCandidates := partyCandidates) (quota := quota)
      (initialVotes := initialVotes) (fractionalTally := rule.fractionalTally)
      (steps := trace.steps) hfinal
  exact
    partyTransferPreservationTraceOutcome_of_sourceTraceOutcome
      (rule := rule) (trace := trace) (partyCandidates := partyCandidates)
      (initialVotes := initialVotes) (quota := quota)
      (finalSeats := finalSeats)
      ⟨hlaw, hterminal, hfinal_terminal⟩

/--
One-party executable-trace packaging theorem.  It derives the source trace law
and ordinary step facts from the executable candidate-level STV trace, then
uses the capacity-terminal argument to produce the party transfer-preservation
outcome.
-/
theorem partyTransferPreservationTraceOutcome_of_executableTrace_solidCoalition_left_capacityTerminal
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {allVoters partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {quota initialVotes : ℝ} {finalSeats : ℕ}
    {initialActive terminalActive : Finset Candidate}
    {initialWeight partyInitialWeight : Voter → ℝ}
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots quota
        initialActive terminalActive initialWeight)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hpartyInitialMass :
      initialVotes = ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hstartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card initialVotes))
    (hstartRemaining :
      (PartyQuotaStartState partyCandidates.card initialVotes).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card)
    (hnoquota_on_eliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate < quota)
    (hterminalNoParty :
      activePartyCandidates terminalActive partyCandidates = ∅)
    (hfinal :
      partyElectStepCount partyCandidates trace.steps ≤ finalSeats) :
    PartyTransferPreservationTraceOutcome rule trace partyCandidates
      initialVotes quota finalSeats := by
  have hlaw :
      FractionalPartySTVSourceTraceLaw partyCandidates quota
        rule.fractionalTally trace.steps
        (PartyQuotaStartState partyCandidates.card initialVotes) :=
    fractionalPartySTVSourceTraceLaw_of_executableTrace_solidCoalition_left
      (rule := rule) (trace := trace) (allVoters := allVoters)
      (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates) (quota := quota)
      (initialVotes := initialVotes) (initialActive := initialActive)
      (terminalActive := terminalActive) (initialWeight := initialWeight)
      (partyInitialWeight := partyInitialWeight) hrun hvoterPartition
      hvoterDisjoint hcandidateDisjoint hpartySolid hotherSolid
      hpartyActive hotherActive hpartyInitialWeightEq hpartyInitialMass
      hstartRemaining
  have hsteps :
      ∀ step, step ∈ trace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    rcases (FractionalSTVExecutableTrace.concreteStepLaw hrun) ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota_if_elect⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  exact
    partyTransferPreservationTraceOutcome_of_sourceTraceLaw_capacityTerminal
      (rule := rule) (trace := trace) (partyCandidates := partyCandidates)
      (initialVotes := initialVotes) (quota := quota)
      (finalSeats := finalSeats) (startActive := initialActive)
      (terminalActive := terminalActive) hlaw hstartCapacity
      hnoquota_on_eliminate hrun.activeReplay hstartRemaining hsteps
      hterminalNoParty hfinal

/--
A source-primitive transfer-preserving candidate trace yields the quota
lower-bound witness used by solid-coalition STV proofs.
-/
theorem quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
    {Candidate : Type*} [DecidableEq Candidate] {finalSeats : ℕ}
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates : Finset Candidate} {initialVotes quota : ℝ}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (houtcome :
      PartyTransferPreservationTraceOutcome
        rule trace partyCandidates initialVotes quota finalSeats) :
    QuotaLowerBoundWitness finalSeats initialVotes quota := by
  rcases houtcome with ⟨terminalState, hpath, hterminal, hfinal⟩
  have hstart :
      PartyQuotaInvariant initialVotes quota
        (PartyQuotaStartState partyCandidates.card initialVotes) :=
    PartyQuotaInvariant.start hvotes_nonneg
  have hterminalInvariant :
      PartyQuotaInvariant initialVotes quota terminalState :=
    PartyQuotaInvariant.of_reflTransGen hstart
      (partyQuotaPath_of_transferPreservationPath hpath)
  exact quotaLowerBoundWitness_of_partyQuotaProcess hquota_pos hfinal
    hterminalInvariant hterminal

end Voting
end SocialChoice
end AppliedModelingLib
