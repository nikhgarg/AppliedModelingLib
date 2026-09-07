import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Ranked Ballots

Reusable finite ballot primitives for ranked-choice voting and STV-style
election rules.

The library starts with partial rankings represented as lists. Paper folders can
add source-specific conventions, such as complete rankings, exhausted ballots,
or equal-rank exclusions, as thin wrappers around this API.

## Main declarations

- `Ballot`
- `Ballot.Valid`
- `Ballot.nextActive`
- `Ballot.removeCandidates`
- `Ballot.firstChoiceIn`
- `Ballot.firstChoiceVoters`
- `Ballot.firstChoiceCount`
- `Ballot.strictSupportVoters`
- `Ballot.strictSupportCount`
- `Ballot.strictSupportCountWithBlockerPrefix`
- `Ballot.strictSupportCountWithAccumulatedBlockers`
- `Ballot.IsSuffixExtension`
- `Ballot.IsPrefixExtension`
- `Ballot.PreservesPrefixThrough`
- `Ballot.RespectsLength`
- `Ballot.weightedActiveSupportCount`
- `Ballot.activeSupport_card_eq_of_forall_suffixExtension_nextActive_some`
- `Ballot.activeSupport_card_eq_of_forall_prefixExtension_inactive`
- `Ballot.activeSupport_card_eq_of_forall_append_exhausted_prefix`
- `Ballot.activeSupport_card_removeCandidates_eq_of_disjoint_active`
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/-- A ranked ballot is a finite ordered list of candidates. -/
abbrev Ballot (Candidate : Type*) := List Candidate

namespace Ballot

/-- A ballot is valid when it lists each candidate at most once. -/
def Valid {Candidate : Type*} (ballot : Ballot Candidate) : Prop :=
  ballot.Nodup

/-- `extended` is obtained from `base` by suffixing additional preferences. -/
def IsSuffixExtension {Candidate : Type*}
    (base extended : Ballot Candidate) : Prop :=
  ∃ suffix, extended = base ++ suffix

/-- `extended` is obtained from `base` by prefixing additional preferences. -/
def IsPrefixExtension {Candidate : Type*}
    (pref base extended : Ballot Candidate) : Prop :=
  extended = pref ++ base

/--
`before` and `after` have the same prefix through `candidate`.

This captures paper-neutral strategic-voting moves where a candidate can change
later preferences after their own position, but cannot move themselves earlier
or edit earlier-ranked candidates.
-/
def PreservesPrefixThrough {Candidate : Type*}
    (candidate : Candidate) (before after : Ballot Candidate) : Prop :=
  ∃ pref beforeSuffix afterSuffix,
    before = pref ++ candidate :: beforeSuffix ∧
      after = pref ++ candidate :: afterSuffix

/-- A ballot respects a maximum allowed ranking length. -/
def RespectsLength {Candidate : Type*} (maxLength : ℕ) (ballot : Ballot Candidate) :
    Prop :=
  ballot.length ≤ maxLength

/-- A single-choice ballot ranks at most one candidate. -/
def IsSingleChoice {Candidate : Type*} (ballot : Ballot Candidate) : Prop :=
  RespectsLength 1 ballot

/--
The first candidate on a ballot that is still active, if one exists.

This is the core exhaustion operation used by deterministic RCV/STV traces.
-/
def nextActive {Candidate : Type*} [DecidableEq Candidate]
    (ballot : Ballot Candidate) (active : Finset Candidate) : Option Candidate :=
  match ballot with
  | [] => none
  | c :: rest => if c ∈ active then some c else nextActive rest active

/--
Remove every candidate in `removed` from a ballot, preserving the relative
order of all remaining candidates.
-/
def removeCandidates {Candidate : Type*} [DecidableEq Candidate]
    (removed : Finset Candidate) (ballot : Ballot Candidate) : Ballot Candidate :=
  ballot.filter fun candidate => candidate ∉ removed

/-- The ballot's first-ranked candidate belongs to a given candidate set. -/
def firstChoiceIn {Candidate : Type*} [DecidableEq Candidate]
    (ballot : Ballot Candidate) (candidates : Finset Candidate) : Prop :=
  match ballot with
  | [] => False
  | candidate :: _rest => candidate ∈ candidates

@[simp] theorem firstChoiceIn_nil {Candidate : Type*} [DecidableEq Candidate]
    (candidates : Finset Candidate) :
    firstChoiceIn ([] : Ballot Candidate) candidates = False := rfl

@[simp] theorem firstChoiceIn_cons {Candidate : Type*} [DecidableEq Candidate]
    (candidate : Candidate) (rest : Ballot Candidate)
    (candidates : Finset Candidate) :
    firstChoiceIn (candidate :: rest) candidates =
      (candidate ∈ candidates) := rfl

/--
If a ballot's first choice belongs to a finite set, then it first chooses one
of that set's singleton candidates.
-/
theorem firstChoiceIn_exists_singleton {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {candidates : Finset Candidate}
    (hfirst : firstChoiceIn ballot candidates) :
    ∃ candidate, candidate ∈ candidates ∧ firstChoiceIn ballot {candidate} := by
  cases ballot with
  | nil =>
      simp [firstChoiceIn] at hfirst
  | cons candidate rest =>
      exact ⟨candidate, by simpa [firstChoiceIn] using hfirst, by simp⟩

instance decidableFirstChoiceIn {Candidate : Type*} [DecidableEq Candidate]
    (ballot : Ballot Candidate) (candidates : Finset Candidate) :
    Decidable (firstChoiceIn ballot candidates) := by
  cases ballot with
  | nil =>
      exact isFalse (by simp [firstChoiceIn])
  | cons candidate rest =>
      change Decidable (candidate ∈ candidates)
      infer_instance

/-- Voters whose first-ranked candidate is exactly `candidate`. -/
def firstChoiceVoters {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (candidate : Candidate) : Finset Voter :=
  voters.filter fun voter => firstChoiceIn (ballots voter) {candidate}

/-- Number of voters whose first-ranked candidate is exactly `candidate`. -/
def firstChoiceCount {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (candidate : Candidate) : ℕ :=
  (firstChoiceVoters voters ballots candidate).card

@[simp] theorem mem_firstChoiceVoters_iff
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidate : Candidate} {voter : Voter} :
    voter ∈ firstChoiceVoters voters ballots candidate ↔
      voter ∈ voters ∧ firstChoiceIn (ballots voter) {candidate} := by
  simp [firstChoiceVoters]

@[simp] theorem nextActive_nil {Candidate : Type*} [DecidableEq Candidate]
    (active : Finset Candidate) :
    nextActive ([] : Ballot Candidate) active = none := rfl

@[simp] theorem nextActive_cons_of_mem {Candidate : Type*} [DecidableEq Candidate]
    (c : Candidate) (rest : Ballot Candidate) (active : Finset Candidate)
    (h : c ∈ active) :
    nextActive (c :: rest) active = some c := by
  simp [nextActive, h]

@[simp] theorem nextActive_cons_of_not_mem {Candidate : Type*} [DecidableEq Candidate]
    (c : Candidate) (rest : Ballot Candidate) (active : Finset Candidate)
    (h : c ∉ active) :
    nextActive (c :: rest) active = nextActive rest active := by
  simp [nextActive, h]

theorem nextActive_mem {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active : Finset Candidate} {c : Candidate}
    (h : nextActive ballot active = some c) :
    c ∈ active := by
  induction ballot with
  | nil =>
      simp [nextActive] at h
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · simp [nextActive, hhead] at h
        simpa [← h] using hhead
      · simp [nextActive, hhead] at h
        exact ih h

/--
If a ballot's first choice lies in an initial active set and its current first
active candidate is `candidate`, then the ballot either first chose
`candidate` or first chose a candidate removed from the current active set.
-/
theorem firstChoiceIn_singleton_or_sdiff_of_nextActive_some
    {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {initial active : Finset Candidate}
    {candidate : Candidate}
    (hfirst : firstChoiceIn ballot initial)
    (hnext : nextActive ballot active = some candidate) :
    firstChoiceIn ballot {candidate} ∨ firstChoiceIn ballot (initial \ active) := by
  cases hballot : ballot with
  | nil =>
      simp [firstChoiceIn, hballot] at hfirst
  | cons head rest =>
      have hhead_initial : head ∈ initial := by
        simpa [firstChoiceIn, hballot] using hfirst
      by_cases hhead_active : head ∈ active
      · have hcandidate : head = candidate := by
          simpa [nextActive, hballot, hhead_active] using hnext
        left
        simpa [firstChoiceIn, hballot, hcandidate]
      · right
        exact Finset.mem_sdiff.mpr ⟨hhead_initial, hhead_active⟩

/--
If the ballot's first choice is active, then first-active support for a
candidate is the same as first-choice support for that candidate.
-/
theorem nextActive_eq_some_iff_firstChoiceIn_singleton_of_firstChoiceIn
    {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hfirst : firstChoiceIn ballot active) :
    nextActive ballot active = some candidate ↔
      firstChoiceIn ballot {candidate} := by
  cases hballot : ballot with
  | nil =>
      simp [firstChoiceIn, hballot] at hfirst
  | cons head rest =>
      have hhead_active : head ∈ active := by
        simpa [firstChoiceIn, hballot] using hfirst
      simp [nextActive, firstChoiceIn, hhead_active]

/--
Removing candidates from a ballot is equivalent, for first-active lookup, to
running the original ballot with those candidates absent from the active set.
-/
@[simp] theorem nextActive_removeCandidates_sdiff {Candidate : Type*}
    [DecidableEq Candidate]
    (ballot : Ballot Candidate) (active removed : Finset Candidate) :
    nextActive (removeCandidates removed ballot) (active \ removed) =
      nextActive ballot (active \ removed) := by
  induction ballot with
  | nil =>
      simp [removeCandidates]
  | cons head rest ih =>
      by_cases hremoved : head ∈ removed
      · have hinactive : head ∉ active \ removed := by
          intro hhead
          exact (Finset.mem_sdiff.mp hhead).2 hremoved
        simp [removeCandidates, nextActive, hremoved, hinactive]
        simpa [removeCandidates] using ih
      · by_cases hactive : head ∈ active \ removed
        · simp [removeCandidates, nextActive, hremoved, hactive]
        · simp [removeCandidates, nextActive, hremoved, hactive]
          simpa [removeCandidates] using ih

/--
Removing candidates that are not active does not change the first active
candidate.
-/
theorem nextActive_removeCandidates_eq_of_forall_not_mem {Candidate : Type*}
    [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active removed : Finset Candidate}
    (hremoved : ∀ candidate, candidate ∈ active → candidate ∉ removed) :
    nextActive (removeCandidates removed ballot) active =
      nextActive ballot active := by
  have hsdiff : active \ removed = active := by
    ext candidate
    constructor
    · intro hcandidate
      exact (Finset.mem_sdiff.mp hcandidate).1
    · intro hcandidate
      exact Finset.mem_sdiff.mpr
        ⟨hcandidate, hremoved candidate hcandidate⟩
  simpa [hsdiff] using nextActive_removeCandidates_sdiff ballot active removed

/--
Removing candidates disjoint from the active set does not change the first
active candidate.
-/
theorem nextActive_removeCandidates_eq_of_disjoint_active {Candidate : Type*}
    [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active removed : Finset Candidate}
    (hdisjoint : active ∩ removed = ∅) :
    nextActive (removeCandidates removed ballot) active =
      nextActive ballot active := by
  exact nextActive_removeCandidates_eq_of_forall_not_mem (by
    intro candidate hactive hremoved
    have hmem : candidate ∈ active ∩ removed := by
      simp [hactive, hremoved]
    rw [hdisjoint] at hmem
    simpa using hmem)

/--
Suffixing later preferences does not change the first active candidate when
the original ballot already has one.
-/
theorem nextActive_append_of_some {Candidate : Type*} [DecidableEq Candidate]
    {ballot suffix : Ballot Candidate} {active : Finset Candidate} {c : Candidate}
    (h : nextActive ballot active = some c) :
    nextActive (ballot ++ suffix) active = some c := by
  induction ballot with
  | nil =>
      simp [nextActive] at h
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · simpa [nextActive, hhead] using h
      · simp [nextActive, hhead] at h ⊢
        exact ih h

/--
If the original ballot is exhausted at an active set, appending later
preferences makes the next active candidate come from the suffix.
-/
theorem nextActive_append_of_none {Candidate : Type*} [DecidableEq Candidate]
    {ballot suffix : Ballot Candidate} {active : Finset Candidate}
    (h : nextActive ballot active = none) :
    nextActive (ballot ++ suffix) active = nextActive suffix active := by
  induction ballot with
  | nil =>
      simp
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · simp [nextActive, hhead] at h
      · simp [nextActive, hhead] at h ⊢
        exact ih h

/--
Prefixing inactive candidates does not change the first active candidate.
-/
theorem nextActive_append_left_of_forall_not_mem {Candidate : Type*} [DecidableEq Candidate]
    {pref ballot : Ballot Candidate} {active : Finset Candidate}
    (hpref : ∀ c, c ∈ pref → c ∉ active) :
    nextActive (pref ++ ballot) active = nextActive ballot active := by
  induction pref with
  | nil =>
      simp
  | cons head rest ih =>
      have hhead : head ∉ active := hpref head (by simp)
      have hrest : ∀ c, c ∈ rest → c ∉ active := by
        intro c hc
        exact hpref c (by simp [hc])
      simp [List.cons_append, hhead, ih hrest]

/-- If no listed candidate is active, the ballot is exhausted. -/
theorem nextActive_eq_none_of_forall_not_mem {Candidate : Type*}
    [DecidableEq Candidate] {ballot : Ballot Candidate}
    {active : Finset Candidate}
    (hballot : ∀ c, c ∈ ballot → c ∉ active) :
    nextActive ballot active = none := by
  induction ballot with
  | nil =>
      simp [nextActive]
  | cons head rest ih =>
      have hhead : head ∉ active := hballot head (by simp)
      have hrest : ∀ c, c ∈ rest → c ∉ active := by
        intro c hc
        exact hballot c (by simp [hc])
      simp [nextActive, hhead, ih hrest]

/-- A first-active candidate is listed somewhere on the ballot. -/
theorem mem_of_nextActive_eq_some {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hnext : nextActive ballot active = some candidate) :
    candidate ∈ ballot := by
  induction ballot with
  | nil =>
      simp [nextActive] at hnext
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · have hcandidate : head = candidate := by
          simpa [nextActive, hhead] using hnext
        simp [hcandidate]
      · have hrest : nextActive rest active = some candidate := by
          simpa [nextActive, hhead] using hnext
        exact by simp [ih hrest]

/--
Filtering an ordered ballot by a source allocation predicate makes `candidate`
the first active candidate exactly when the predicate keeps `candidate`,
provided all candidates in the displayed prefix are inactive and `candidate`
itself is active.
-/
theorem nextActive_filter_eq_some_iff_of_split {Candidate : Type*}
    [DecidableEq Candidate] {order pref suffix : Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (keep : Candidate → Prop) [DecidablePred keep]
    (hsplit : order = pref ++ candidate :: suffix)
    (hprefix : ∀ c, c ∈ pref → c ∉ active)
    (hcandidate : candidate ∈ active) :
    nextActive (order.filter keep) active = some candidate ↔ keep candidate := by
  constructor
  · intro hnext
    have hmem : candidate ∈ order.filter keep :=
      mem_of_nextActive_eq_some hnext
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  · intro hkeep
    subst order
    rw [List.filter_append]
    have hpref_none : nextActive (pref.filter keep) active = none := by
      refine nextActive_eq_none_of_forall_not_mem ?_
      intro c hc
      exact hprefix c (List.mem_filter.mp hc).1
    rw [nextActive_append_of_none hpref_none]
    simp [hkeep, hcandidate]

/--
If a filtered ballot keeps at least one listed active candidate, then the
filtered ballot has some first active candidate.
-/
theorem exists_nextActive_filter_eq_some_of_exists_mem_active_keep
    {Candidate : Type*} [DecidableEq Candidate]
    {order : Ballot Candidate} {active : Finset Candidate}
    {keep : Candidate → Prop} [DecidablePred keep]
    (h : ∃ candidate,
      candidate ∈ order ∧ keep candidate ∧ candidate ∈ active) :
    ∃ first, nextActive (order.filter keep) active = some first := by
  induction order with
  | nil =>
      rcases h with ⟨candidate, hmem, _hkeep, _hactive⟩
      simp at hmem
  | cons head rest ih =>
      by_cases hkeep_head : keep head
      · by_cases hactive_head : head ∈ active
        · exact ⟨head, by simp [hkeep_head, hactive_head]⟩
        · have hrest :
              ∃ candidate,
                candidate ∈ rest ∧ keep candidate ∧ candidate ∈ active := by
            rcases h with ⟨candidate, hmem, hkeep, hactive⟩
            rcases List.mem_cons.mp hmem with hcandidate | hcandidate
            · subst candidate
              exact False.elim (hactive_head hactive)
            · exact ⟨candidate, hcandidate, hkeep, hactive⟩
          rcases ih hrest with ⟨first, hfirst⟩
          exact ⟨first, by simp [hkeep_head, hactive_head, hfirst]⟩
      · have hrest :
            ∃ candidate,
              candidate ∈ rest ∧ keep candidate ∧ candidate ∈ active := by
          rcases h with ⟨candidate, hmem, hkeep, hactive⟩
          rcases List.mem_cons.mp hmem with hcandidate | hcandidate
          · subst candidate
            exact False.elim (hkeep_head hkeep)
          · exact ⟨candidate, hcandidate, hkeep, hactive⟩
        rcases ih hrest with ⟨first, hfirst⟩
        exact ⟨first, by simp [hkeep_head, hfirst]⟩

/--
If two ballots preserve the prefix through a candidate that is still active,
then they have the same first active candidate.
-/
theorem nextActive_eq_of_preservesPrefixThrough_active {Candidate : Type*}
    [DecidableEq Candidate] {before after : Ballot Candidate}
    {active : Finset Candidate} {gate : Candidate}
    (hpreserve : PreservesPrefixThrough gate before after)
    (hgate : gate ∈ active) :
    nextActive before active = nextActive after active := by
  rcases hpreserve with ⟨pref, beforeSuffix, afterSuffix, hbefore, hafter⟩
  subst before
  subst after
  cases hpref : nextActive pref active with
  | none =>
      rw [nextActive_append_of_none hpref, nextActive_append_of_none hpref]
      simp [nextActive, hgate]
  | some first =>
      have hbeforePrefix :
          nextActive (pref ++ gate :: beforeSuffix) active = some first :=
        nextActive_append_of_some hpref
      have hafterPrefix :
          nextActive (pref ++ gate :: afterSuffix) active = some first :=
        nextActive_append_of_some hpref
      rw [hbeforePrefix, hafterPrefix]

/--
If a pair of ballots preserves the prefix through some active gate candidate,
then the first active candidate is unchanged.
-/
theorem nextActive_eq_of_exists_preservesPrefixThrough_active {Candidate : Type*}
    [DecidableEq Candidate] {before after : Ballot Candidate}
    {active : Finset Candidate}
    (hpreserve : ∃ gate, gate ∈ active ∧ PreservesPrefixThrough gate before after) :
    nextActive before active = nextActive after active := by
  rcases hpreserve with ⟨gate, hgate, hgatePreserve⟩
  exact nextActive_eq_of_preservesPrefixThrough_active hgatePreserve hgate

/--
If a preserved-prefix gate belongs to a set of candidates that are all active,
then it can be used as an active gate.
-/
theorem exists_active_preservesPrefixThrough_of_subset {Candidate : Type*}
    {before after : Ballot Candidate} {gates active : Finset Candidate}
    (hsubset : gates ⊆ active)
    (hpreserve : ∃ gate, gate ∈ gates ∧ PreservesPrefixThrough gate before after) :
    ∃ gate, gate ∈ active ∧ PreservesPrefixThrough gate before after := by
  rcases hpreserve with ⟨gate, hgate, hgatePreserve⟩
  exact ⟨gate, hsubset hgate, hgatePreserve⟩

/--
Pointwise version of
`exists_active_preservesPrefixThrough_of_subset` for a finite voter set.
-/
theorem forall_exists_active_preservesPrefixThrough_of_subset
    {Voter Candidate : Type*} {voters : Finset Voter}
    {before after : Voter → Ballot Candidate}
    {gates active : Finset Candidate}
    (hsubset : gates ⊆ active)
    (hpreserve : ∀ voter ∈ voters,
      ∃ gate, gate ∈ gates ∧
        PreservesPrefixThrough gate (before voter) (after voter)) :
    ∀ voter ∈ voters,
      ∃ gate, gate ∈ active ∧
        PreservesPrefixThrough gate (before voter) (after voter) := by
  intro voter hvoter
  exact exists_active_preservesPrefixThrough_of_subset hsubset
    (hpreserve voter hvoter)

/--
If two ballots preserve the prefix through an active candidate, then the
candidate being first active after the edit implies the candidate was already
first active before the edit.
-/
theorem nextActive_eq_some_of_preservesPrefixThrough {Candidate : Type*}
    [DecidableEq Candidate] {before after : Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hpreserve : PreservesPrefixThrough candidate before after)
    (hcandidate : candidate ∈ active)
    (hafter : nextActive after active = some candidate) :
    nextActive before active = some candidate := by
  rw [nextActive_eq_of_preservesPrefixThrough_active hpreserve hcandidate]
  exact hafter

/-- Voters whose ballots first activate a candidate at a fixed active set. -/
def activeSupport {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (active : Finset Candidate) (candidate : Candidate) : Finset Voter :=
  voters.filter fun voter => nextActive (ballots voter) active = some candidate

/--
Weighted active-support count for a finite list of ballot types with
multiplicities. This is the finite-list analogue of `activeSupport`: each block
contributes its multiplicity exactly when its first active candidate is the
queried candidate.
-/
def weightedActiveSupportCount {Candidate : Type*} [DecidableEq Candidate]
    (entries : List (Ballot Candidate × ℕ)) (active : Finset Candidate)
    (candidate : Candidate) : ℕ :=
  (entries.map fun entry =>
    if nextActive entry.1 active = some candidate then entry.2 else 0).sum

@[simp] theorem weightedActiveSupportCount_nil {Candidate : Type*}
    [DecidableEq Candidate] (active : Finset Candidate)
    (candidate : Candidate) :
    weightedActiveSupportCount ([] : List (Ballot Candidate × ℕ)) active
      candidate = 0 := by
  simp [weightedActiveSupportCount]

@[simp] theorem weightedActiveSupportCount_cons {Candidate : Type*}
    [DecidableEq Candidate] (entry : Ballot Candidate × ℕ)
    (entries : List (Ballot Candidate × ℕ)) (active : Finset Candidate)
    (candidate : Candidate) :
    weightedActiveSupportCount (entry :: entries) active candidate =
      (if nextActive entry.1 active = some candidate then entry.2 else 0) +
        weightedActiveSupportCount entries active candidate := by
  simp [weightedActiveSupportCount]

theorem weightedActiveSupportCount_append {Candidate : Type*}
    [DecidableEq Candidate] (left right : List (Ballot Candidate × ℕ))
    (active : Finset Candidate) (candidate : Candidate) :
    weightedActiveSupportCount (left ++ right) active candidate =
      weightedActiveSupportCount left active candidate +
        weightedActiveSupportCount right active candidate := by
  simp [weightedActiveSupportCount, List.map_append, List.sum_append]

@[simp] theorem weightedActiveSupportCount_singleton {Candidate : Type*}
    [DecidableEq Candidate] (ballot : Ballot Candidate) (weight : ℕ)
    (active : Finset Candidate) (candidate : Candidate) :
    weightedActiveSupportCount [(ballot, weight)] active candidate =
      if nextActive ballot active = some candidate then weight else 0 := by
  simp [weightedActiveSupportCount]

/--
When every voter's first choice belongs to the active set, active support for a
candidate is contained in that candidate's first-choice voter set.
-/
theorem activeSupport_subset_firstChoiceVoters_of_forall_firstChoiceIn
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hfirst : ∀ voter, voter ∈ voters →
      firstChoiceIn (ballots voter) active) :
    activeSupport voters ballots active candidate ⊆
      firstChoiceVoters voters ballots candidate := by
  intro voter hvoter
  simp [activeSupport] at hvoter ⊢
  exact ⟨hvoter.1,
    (nextActive_eq_some_iff_firstChoiceIn_singleton_of_firstChoiceIn
      (hfirst voter hvoter.1)).mp hvoter.2⟩

/--
Cardinal form of
`activeSupport_subset_firstChoiceVoters_of_forall_firstChoiceIn`.
-/
theorem activeSupport_card_le_firstChoiceCount_of_forall_firstChoiceIn
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hfirst : ∀ voter, voter ∈ voters →
      firstChoiceIn (ballots voter) active) :
    (activeSupport voters ballots active candidate).card ≤
      firstChoiceCount voters ballots candidate :=
  Finset.card_le_card
    (activeSupport_subset_firstChoiceVoters_of_forall_firstChoiceIn
      (voters := voters) (ballots := ballots) (active := active)
      (candidate := candidate) hfirst)

/--
If `candidate` is active, then first-choice support for `candidate` is included
in first-active support at that active set.
-/
theorem firstChoiceVoters_subset_activeSupport_of_mem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hactive : candidate ∈ active) :
    firstChoiceVoters voters ballots candidate ⊆
      activeSupport voters ballots active candidate := by
  intro voter hvoter
  simp [firstChoiceVoters] at hvoter
  rcases hvoter with ⟨hvoters, hfirst⟩
  cases hballot : ballots voter with
  | nil =>
      simp [firstChoiceIn, hballot] at hfirst
  | cons head rest =>
      have hhead : head = candidate := by
        have hsingleton : head ∈ ({candidate} : Finset Candidate) := by
          simpa [firstChoiceIn, hballot] using hfirst
        simpa using (Finset.mem_singleton.mp hsingleton)
      exact Finset.mem_filter.mpr ⟨hvoters, by
        simpa [activeSupport, hballot, hhead, hactive] using
          nextActive_cons_of_mem candidate rest active hactive⟩

/--
If `candidate` is active, then its first-choice count is bounded by its
first-active support count at that active set.
-/
theorem firstChoiceCount_le_activeSupport_card_of_mem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hactive : candidate ∈ active) :
    firstChoiceCount voters ballots candidate ≤
      (activeSupport voters ballots active candidate).card :=
  Finset.card_le_card
    (firstChoiceVoters_subset_activeSupport_of_mem
      (voters := voters) (ballots := ballots) (active := active)
      (candidate := candidate) hactive)

/--
If deleting one active source candidate makes `target` the next active
candidate on a ballot, then before deleting that source the ballot selected
either `target` or the deleted source.
-/
theorem nextActive_eq_some_or_source_of_nextActive_erase_eq_some
    {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active : Finset Candidate}
    {source target : Candidate}
    (hsource : source ∈ active)
    (htarget : target ∈ active.erase source)
    (hnext : nextActive ballot (active.erase source) = some target) :
    nextActive ballot active = some target ∨
      nextActive ballot active = some source := by
  induction ballot with
  | nil =>
      simp [nextActive] at hnext
  | cons head rest ih =>
      by_cases hhead_active : head ∈ active
      · by_cases hhead_erased : head ∈ active.erase source
        · have hhead_target : head = target := by
            simpa [nextActive, hhead_erased] using hnext
          left
          subst head
          have htarget_active : target ∈ active :=
            Finset.mem_of_mem_erase htarget
          simp [nextActive, htarget_active]
        · have hhead_source : head = source := by
            have hhead_ne : head ≠ source → False := by
              intro hne
              exact hhead_erased (Finset.mem_erase.mpr ⟨hne, hhead_active⟩)
            exact Classical.byContradiction fun hne =>
              hhead_ne hne
          right
          subst head
          simp [nextActive, hsource]
      · have hhead_erased : head ∉ active.erase source := by
          intro hmem
          exact hhead_active (Finset.mem_of_mem_erase hmem)
        simp [nextActive, hhead_active, hhead_erased] at hnext ⊢
        exact ih hnext

/--
After deleting one active source candidate, support for any still-active target
is contained in the union of the target's old support and the source's old
support.
-/
theorem activeSupport_erase_subset_union_activeSupport
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {source target : Candidate}
    (hsource : source ∈ active)
    (htarget : target ∈ active.erase source) :
    activeSupport voters ballots (active.erase source) target ⊆
      (activeSupport voters ballots active target ∪
        activeSupport voters ballots active source) := by
  intro voter hvoter
  simp [activeSupport] at hvoter ⊢
  rcases hvoter with ⟨hvoters, hnext⟩
  rcases
    nextActive_eq_some_or_source_of_nextActive_erase_eq_some
      (ballot := ballots voter) hsource htarget hnext with
    htarget_support | hsource_support
  · exact Or.inl ⟨hvoters, htarget_support⟩
  · exact Or.inr ⟨hvoters, hsource_support⟩

/--
Cardinal form of `activeSupport_erase_subset_union_activeSupport`: erasing one
active source can increase any remaining target's support by at most the
source's previous active support.
-/
theorem activeSupport_card_erase_le_activeSupport_card_add_source
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {source target : Candidate}
    (hsource : source ∈ active)
    (htarget : target ∈ active.erase source) :
    (activeSupport voters ballots (active.erase source) target).card ≤
      (activeSupport voters ballots active target).card +
        (activeSupport voters ballots active source).card := by
  calc
    (activeSupport voters ballots (active.erase source) target).card ≤
        (activeSupport voters ballots active target ∪
            activeSupport voters ballots active source).card :=
      Finset.card_le_card
        (activeSupport_erase_subset_union_activeSupport
          (voters := voters) (ballots := ballots) hsource htarget)
    _ ≤
        (activeSupport voters ballots active target).card +
          (activeSupport voters ballots active source).card :=
      Finset.card_union_le
        (activeSupport voters ballots active target)
        (activeSupport voters ballots active source)

/--
Voters contributing to a strict-support count.

A voter contributes for `candidate`, source group `sources`, and blocker set
`blockers` when the ballot starts in `sources` and, after ignoring candidates
other than `candidate` and the blockers, the first active candidate is
`candidate`.
-/
def strictSupportVoters {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) :
    Finset Voter :=
  voters.filter fun voter =>
    firstChoiceIn (ballots voter) sources ∧
      nextActive (ballots voter) (insert candidate blockers) =
        some candidate

/--
Number of voters with strict support for `candidate` from `sources` before
any candidate in `blockers`.
-/
def strictSupportCount {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) : ℕ :=
  (strictSupportVoters voters ballots sources blockers candidate).card

/--
If a ballot selects `candidate` when `candidate` is considered together with
some blockers, then it also selects `candidate` when `candidate` is the only
active candidate.
-/
theorem nextActive_singleton_eq_some_of_nextActive_insert_eq_some
    {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {blockers : Finset Candidate}
    {candidate : Candidate}
    (hnext :
      nextActive ballot (insert candidate blockers) = some candidate) :
    nextActive ballot {candidate} = some candidate := by
  induction ballot with
  | nil =>
      simp [nextActive] at hnext
  | cons head rest ih =>
      by_cases hhead_active : head ∈ insert candidate blockers
      · simp [nextActive, hhead_active] at hnext
        have hhead_eq : head = candidate := by
          exact hnext
        subst head
        simp [nextActive]
      · have hhead_singleton : head ∉ ({candidate} : Finset Candidate) := by
          intro hhead_singleton
          exact hhead_active (by
            have hhead_eq : head = candidate := by
              simpa using hhead_singleton
            simp [hhead_eq])
        simp [nextActive, hhead_active] at hnext
        simp [nextActive, hhead_singleton]
        exact ih hnext

/--
Adding blockers can only reduce strict support for a fixed source set and
target candidate.
-/
theorem strictSupportVoters_subset_empty_blockers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) :
    strictSupportVoters voters ballots sources blockers candidate ⊆
      strictSupportVoters voters ballots sources ∅ candidate := by
  intro voter hvoter
  simp [strictSupportVoters] at hvoter ⊢
  exact
    ⟨hvoter.1, hvoter.2.1,
      nextActive_singleton_eq_some_of_nextActive_insert_eq_some
        hvoter.2.2⟩

/--
Strict-support counts with blockers are bounded by the corresponding
no-blocker strict-support count.
-/
theorem strictSupportCount_le_empty_blockers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) :
    strictSupportCount voters ballots sources blockers candidate ≤
      strictSupportCount voters ballots sources ∅ candidate := by
  exact Finset.card_le_card
    (strictSupportVoters_subset_empty_blockers voters ballots sources blockers
      candidate)

/--
Strict support from a finite source set is bounded by the sum of singleton
source strict supports.  This is useful when a paper computes transfer mass by
candidate of origin but a proof obligation speaks about a removed source set.
-/
theorem strictSupportCount_le_sum_singleton_sources
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) :
    strictSupportCount voters ballots sources blockers candidate ≤
      ∑ source ∈ sources,
        strictSupportCount voters ballots {source} blockers candidate := by
  let singletonSupport : Candidate → Finset Voter :=
    fun source => strictSupportVoters voters ballots {source} blockers candidate
  have hsubset :
      strictSupportVoters voters ballots sources blockers candidate ⊆
        sources.biUnion singletonSupport := by
    intro voter hvoter
    rcases Finset.mem_filter.mp hvoter with ⟨hvoters, hsupport⟩
    rcases hsupport with ⟨hfirst, hnext⟩
    rcases firstChoiceIn_exists_singleton hfirst with
      ⟨source, hsource, hfirst_source⟩
    exact Finset.mem_biUnion.mpr
      ⟨source, hsource, Finset.mem_filter.mpr
        ⟨hvoters, ⟨hfirst_source, hnext⟩⟩⟩
  calc
    strictSupportCount voters ballots sources blockers candidate =
        (strictSupportVoters voters ballots sources blockers candidate).card :=
      rfl
    _ ≤ (sources.biUnion singletonSupport).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ source ∈ sources, (singletonSupport source).card :=
      Finset.card_biUnion_le
    _ =
        ∑ source ∈ sources,
          strictSupportCount voters ballots {source} blockers candidate := by
      rfl

/--
Strict support from a singleton source is included in the source candidate's
first-choice support.
-/
theorem strictSupportVoters_singleton_subset_firstChoiceVoters
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {source candidate : Candidate} {blockers : Finset Candidate} :
    strictSupportVoters voters ballots {source} blockers candidate ⊆
      firstChoiceVoters voters ballots source := by
  intro voter hvoter
  simp [strictSupportVoters, firstChoiceVoters] at hvoter ⊢
  exact ⟨hvoter.1, hvoter.2.1⟩

/--
The singleton-source strict-support count is bounded by that source's
first-choice count.
-/
theorem strictSupportCount_singleton_le_firstChoiceCount
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {source candidate : Candidate} {blockers : Finset Candidate} :
    strictSupportCount voters ballots {source} blockers candidate ≤
      firstChoiceCount voters ballots source :=
  Finset.card_le_card
    (strictSupportVoters_singleton_subset_firstChoiceVoters
      (voters := voters) (ballots := ballots) (source := source)
      (candidate := candidate) (blockers := blockers))

/--
First-choice support for `candidate` is included in strict support from any
source set containing `candidate`, with no blockers.
-/
theorem firstChoiceVoters_subset_strictSupportVoters_of_mem_sources
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources : Finset Candidate} {candidate : Candidate}
    (hsource : candidate ∈ sources) :
    firstChoiceVoters voters ballots candidate ⊆
      strictSupportVoters voters ballots sources (∅ : Finset Candidate)
        candidate := by
  intro voter hvoter
  simp [firstChoiceVoters] at hvoter
  rcases hvoter with ⟨hvoters, hfirst⟩
  change voter ∈
    voters.filter fun voter =>
      firstChoiceIn (ballots voter) sources ∧
        nextActive (ballots voter) (insert candidate (∅ : Finset Candidate)) =
          some candidate
  cases hballot : ballots voter with
  | nil =>
      simp [firstChoiceIn, hballot] at hfirst
  | cons head rest =>
      have hhead : head = candidate := by
        have hsingleton : head ∈ ({candidate} : Finset Candidate) := by
          simpa [firstChoiceIn, hballot] using hfirst
        simpa using (Finset.mem_singleton.mp hsingleton)
      exact Finset.mem_filter.mpr ⟨hvoters, by
        constructor
        · simpa [firstChoiceIn, hballot, hhead] using hsource
        · simpa [hballot, hhead] using
            nextActive_cons_of_mem candidate rest
              (insert candidate (∅ : Finset Candidate))
              (Finset.mem_insert_self candidate (∅ : Finset Candidate))⟩

/--
The first-choice count is bounded by strict support from any source set
containing `candidate`, with no blockers.
-/
theorem firstChoiceCount_le_strictSupportCount_of_mem_sources
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources : Finset Candidate} {candidate : Candidate}
    (hsource : candidate ∈ sources) :
    firstChoiceCount voters ballots candidate ≤
      strictSupportCount voters ballots sources (∅ : Finset Candidate)
        candidate := by
  exact Finset.card_le_card
    (firstChoiceVoters_subset_strictSupportVoters_of_mem_sources
      (voters := voters) (ballots := ballots) hsource)

/--
Ordered strict-support sum with an accumulated blocker prefix.

For each candidate in the list, the strict-support count is computed with the
blockers already accumulated from earlier candidates, then the candidate is
added to the blocker set before processing the tail. This is the paper-neutral
loop shape used by STV prediction routines that avoid double-counting voters
across an ordered candidate family.
-/
def strictSupportCountWithBlockerPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) : List Candidate → ℕ
  | [] => 0
  | candidate :: rest =>
      strictSupportCount voters ballots sources blockers candidate +
        strictSupportCountWithBlockerPrefix voters ballots sources
          (insert candidate blockers) rest

/--
Quota lower-bound invariant for an accumulated-blocker strict-support loop.

At each step, the current strict-support count is at least `quota`, and the
tail is checked after inserting the current candidate into the blocker set.
-/
def StrictSupportAccumulatorQuota {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ) : List Candidate → Prop
  | [] => True
  | candidate :: rest =>
      quota ≤ strictSupportCount voters ballots sources blockers candidate ∧
        StrictSupportAccumulatorQuota voters ballots sources
          (insert candidate blockers) quota rest

/--
Budgeted quota invariant for an accumulated-blocker strict-support loop.

At each step, the current strict-support count together with the budget units
assigned to the current candidate reaches `quota`.
-/
def StrictSupportAccumulatorBudgetQuota {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) : List Candidate → Prop
  | [] => True
  | candidate :: rest =>
      quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots sources blockers candidate ∧
        StrictSupportAccumulatorBudgetQuota voters ballots sources
          (insert candidate blockers) assignedBudget quota rest

/--
Blockers after processing a candidate prefix in order.

This is a paper-neutral way to state loop invariants: the condition for a
candidate can refer to exactly the blockers accumulated from earlier listed
candidates.
-/
def blockersAfterPrefix {Candidate : Type*} [DecidableEq Candidate]
    (blockers : Finset Candidate) : List Candidate → Finset Candidate
  | [] => blockers
  | candidate :: rest => blockersAfterPrefix (insert candidate blockers) rest

@[simp]
theorem blockersAfterPrefix_eq_union_toFinset {Candidate : Type*}
    [DecidableEq Candidate] (blockers : Finset Candidate)
    (processed : List Candidate) :
    blockersAfterPrefix blockers processed = blockers ∪ processed.toFinset := by
  induction processed generalizing blockers with
  | nil =>
      simp [blockersAfterPrefix]
  | cons candidate rest ih =>
      ext other
      simp [blockersAfterPrefix, ih]

/--
Prefix-form quota condition for an accumulated-blocker strict-support loop.
-/
def StrictSupportAccumulatorQuotaAtPrefixes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ)
    (candidates : List Candidate) : Prop :=
  ∀ pref candidate suffix,
    candidates = pref ++ candidate :: suffix →
      quota ≤ strictSupportCount voters ballots sources
        (blockersAfterPrefix blockers pref) candidate

/--
Prefix-form budgeted quota condition for an accumulated-blocker
strict-support loop.
-/
def StrictSupportAccumulatorBudgetQuotaAtPrefixes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (candidates : List Candidate) : Prop :=
  ∀ pref candidate suffix,
    candidates = pref ++ candidate :: suffix →
      quota ≤ assignedBudget candidate +
        strictSupportCount voters ballots sources
          (blockersAfterPrefix blockers pref) candidate

/--
Candidates that meet the current accumulated-blocker quota test at a given
processed prefix.
-/
def strictSupportReadyCandidatesAtPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ)
    (processed : List Candidate) : Finset Candidate :=
  sources.filter fun candidate =>
    quota ≤ strictSupportCount voters ballots sources
      (blockersAfterPrefix blockers processed) candidate

/--
Candidates that meet the current accumulated-blocker quota test after adding
candidate-specific budget units at a given processed prefix.
-/
def strictSupportBudgetReadyCandidatesAtPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (processed : List Candidate) : Finset Candidate :=
  sources.filter fun candidate =>
    quota ≤ assignedBudget candidate +
      strictSupportCount voters ballots sources
        (blockersAfterPrefix blockers processed) candidate

/-- Membership in the current-prefix ready set is exactly source membership plus quota support. -/
theorem mem_strictSupportReadyCandidatesAtPrefix_iff {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {quota : ℕ}
    {processed : List Candidate} {candidate : Candidate} :
    candidate ∈
        strictSupportReadyCandidatesAtPrefix voters ballots sources blockers
          quota processed ↔
      candidate ∈ sources ∧
        quota ≤ strictSupportCount voters ballots sources
          (blockersAfterPrefix blockers processed) candidate := by
  simp [strictSupportReadyCandidatesAtPrefix]

/--
Membership in the budgeted current-prefix ready set is exactly source
membership plus the budgeted quota-support inequality.
-/
theorem mem_strictSupportBudgetReadyCandidatesAtPrefix_iff
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {processed : List Candidate} {candidate : Candidate} :
    candidate ∈
        strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
          blockers assignedBudget quota processed ↔
      candidate ∈ sources ∧
        quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots sources
            (blockersAfterPrefix blockers processed) candidate := by
  simp [strictSupportBudgetReadyCandidatesAtPrefix]

/--
If every selected loop item belongs to the ready-candidate set computed from
the earlier selected prefix, then the source-loop selections satisfy the
prefix-form accumulator quota condition.
-/
theorem strictSupportAccumulatorQuotaAtPrefixes_of_mem_readyCandidatesAtPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {quota : ℕ}
    {candidates : List Candidate}
    (hselected :
      ∀ pref candidate suffix,
        candidates = pref ++ candidate :: suffix →
          candidate ∈
            strictSupportReadyCandidatesAtPrefix voters ballots sources
              blockers quota pref) :
    StrictSupportAccumulatorQuotaAtPrefixes voters ballots sources blockers
      quota candidates := by
  intro pref candidate suffix hdecomp
  have hmem := hselected pref candidate suffix hdecomp
  have hready :
      candidate ∈ sources ∧
        quota ≤ strictSupportCount voters ballots sources
          (blockersAfterPrefix blockers pref) candidate := by
    simpa [strictSupportReadyCandidatesAtPrefix] using hmem
  exact hready.2

/--
If every selected loop item belongs to the budgeted ready-candidate set
computed from the earlier selected prefix, then the source-loop selections
satisfy the prefix-form budgeted accumulator quota condition.
-/
theorem strictSupportAccumulatorBudgetQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {candidates : List Candidate}
    (hselected :
      ∀ pref candidate suffix,
        candidates = pref ++ candidate :: suffix →
          candidate ∈
            strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
              blockers assignedBudget quota pref) :
    StrictSupportAccumulatorBudgetQuotaAtPrefixes voters ballots sources
      blockers assignedBudget quota candidates := by
  intro pref candidate suffix hdecomp
  have hmem := hselected pref candidate suffix hdecomp
  have hready :
      candidate ∈ sources ∧
        quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots sources
            (blockersAfterPrefix blockers pref) candidate := by
    simpa [strictSupportBudgetReadyCandidatesAtPrefix] using hmem
  exact hready.2

/--
Source-order loop relation for budgeted ready-candidate selection. The
`processed` list records candidates already selected before this source-order
suffix is scanned.
-/
inductive StrictSupportBudgetReadySelectionLoop {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) :
    List Candidate → List Candidate → List Candidate → Prop
  | nil (processed : List Candidate) :
      StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
        assignedBudget quota processed [] []
  | skip {processed : List Candidate} {candidate : Candidate}
      {remaining selected : List Candidate}
      (hnotReady :
        candidate ∉ strictSupportBudgetReadyCandidatesAtPrefix voters ballots
          sources blockers assignedBudget quota processed)
      (hrest :
        StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
          assignedBudget quota processed remaining selected) :
      StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
        assignedBudget quota processed (candidate :: remaining) selected
  | take {processed : List Candidate} {candidate : Candidate}
      {remaining selected : List Candidate}
      (hready :
        candidate ∈ strictSupportBudgetReadyCandidatesAtPrefix voters ballots
          sources blockers assignedBudget quota processed)
      (hrest :
        StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
          assignedBudget quota (processed ++ [candidate]) remaining selected) :
      StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
        assignedBudget quota processed (candidate :: remaining)
        (candidate :: selected)

/--
Executable source-order loop that selects exactly budget-ready candidates,
using the already-selected prefix as accumulated blockers.
-/
def strictSupportBudgetReadySelectionLoopOutput {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (processed sourceOrder : List Candidate) :
    List Candidate :=
  match sourceOrder with
  | [] => []
  | candidate :: remaining =>
      if candidate ∈
          strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
            blockers assignedBudget quota processed then
        candidate ::
          strictSupportBudgetReadySelectionLoopOutput voters ballots sources
            blockers assignedBudget quota (processed ++ [candidate])
            remaining
      else
        strictSupportBudgetReadySelectionLoopOutput voters ballots sources
          blockers assignedBudget quota processed remaining

/--
The executable budget-ready source-order loop satisfies the source-order loop
relation by construction.
-/
theorem strictSupportBudgetReadySelectionLoopOutput_spec
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) :
    ∀ processed sourceOrder,
      StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
        assignedBudget quota processed sourceOrder
        (strictSupportBudgetReadySelectionLoopOutput voters ballots sources
          blockers assignedBudget quota processed sourceOrder) := by
  intro processed sourceOrder
  induction sourceOrder generalizing processed with
  | nil =>
      simp [strictSupportBudgetReadySelectionLoopOutput,
        StrictSupportBudgetReadySelectionLoop.nil]
  | cons candidate remaining ih =>
      by_cases hready :
        candidate ∈
          strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
            blockers assignedBudget quota processed
      · simp [strictSupportBudgetReadySelectionLoopOutput, hready]
        exact StrictSupportBudgetReadySelectionLoop.take hready
          (ih (processed ++ [candidate]))
      · simp [strictSupportBudgetReadySelectionLoopOutput, hready]
        exact StrictSupportBudgetReadySelectionLoop.skip hready
          (ih processed)

/--
If every candidate in the source order is ready at the prefix where the
source-order loop considers it, the executable loop returns the source order
unchanged.
-/
theorem strictSupportBudgetReadySelectionLoopOutput_eq_self_of_forall_ready
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} :
    ∀ {processed sourceOrder : List Candidate},
      (∀ pref candidate suffix,
        sourceOrder = pref ++ candidate :: suffix →
          candidate ∈
            strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
              blockers assignedBudget quota (processed ++ pref)) →
      strictSupportBudgetReadySelectionLoopOutput voters ballots sources
        blockers assignedBudget quota processed sourceOrder = sourceOrder := by
  intro processed sourceOrder hready
  induction sourceOrder generalizing processed with
  | nil =>
      simp [strictSupportBudgetReadySelectionLoopOutput]
  | cons candidate rest ih =>
      have hcandidate :
          candidate ∈
            strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
              blockers assignedBudget quota processed := by
        simpa using hready [] candidate rest rfl
      have hrest :
          ∀ pref selected suffix,
            rest = pref ++ selected :: suffix →
              selected ∈
                strictSupportBudgetReadyCandidatesAtPrefix voters ballots
                  sources blockers assignedBudget quota
                  ((processed ++ [candidate]) ++ pref) := by
        intro pref selected suffix hdecomp
        have hsource :
            candidate :: rest =
              (candidate :: pref) ++ selected :: suffix := by
          simp [hdecomp]
        have hready' := hready (candidate :: pref) selected suffix hsource
        simpa [List.cons_append, List.append_assoc] using hready'
      simp [strictSupportBudgetReadySelectionLoopOutput, hcandidate,
        ih hrest]

/--
Every selected item of a budgeted ready-candidate loop was ready at its
selected-prefix state.
-/
theorem strictSupportBudgetReadySelectionLoop_selected_mem_ready
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {processed sourceOrder selected : List Candidate}
    (hloop :
      StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
        assignedBudget quota processed sourceOrder selected) :
    ∀ pref candidate suffix,
      selected = pref ++ candidate :: suffix →
        candidate ∈
          strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
            blockers assignedBudget quota (processed ++ pref) := by
  induction hloop with
  | nil processed =>
      intro pref candidate suffix hdecomp
      cases pref <;> simp at hdecomp
  | skip hnotReady hrest ih =>
      exact ih
  | take hready hrest ih =>
      intro pref selectedCandidate suffix hdecomp
      cases pref with
      | nil =>
          simp only [List.nil_append] at hdecomp
          injection hdecomp with hcandidate _hsuffix
          subst selectedCandidate
          simpa using hready
      | cons first rest =>
          simp only [List.cons_append] at hdecomp
          injection hdecomp with hfirst htail
          subst first
          have hrec := ih rest selectedCandidate suffix htail
          simpa [List.append_assoc] using hrec

/--
A budgeted ready-candidate source-order loop supplies the prefix-form budgeted
accumulator quota condition.
-/
theorem strictSupportAccumulatorBudgetQuotaAtPrefixes_of_budgetReadySelectionLoop
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {sourceOrder candidates : List Candidate}
    (hloop :
      StrictSupportBudgetReadySelectionLoop voters ballots sources blockers
        assignedBudget quota [] sourceOrder candidates) :
    StrictSupportAccumulatorBudgetQuotaAtPrefixes voters ballots sources
      blockers assignedBudget quota candidates := by
  apply strictSupportAccumulatorBudgetQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
  intro pref candidate suffix hdecomp
  have hready :=
    strictSupportBudgetReadySelectionLoop_selected_mem_ready hloop
      pref candidate suffix hdecomp
  simpa using hready

/--
Build the recursive accumulator invariant from the source-loop statement that
each candidate reaches quota at its processed prefix.
-/
theorem strictSupportAccumulatorQuota_of_atPrefixes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {quota : ℕ}
    {candidates : List Candidate}
    (hprefix :
      StrictSupportAccumulatorQuotaAtPrefixes voters ballots sources blockers
        quota candidates) :
    StrictSupportAccumulatorQuota voters ballots sources blockers quota
      candidates := by
  induction candidates generalizing blockers with
  | nil =>
      trivial
  | cons candidate rest ih =>
      refine ⟨?_, ?_⟩
      · exact hprefix [] candidate rest rfl
      · refine ih ?_
        intro pref candidate' suffix hdecomp
        exact hprefix (candidate :: pref) candidate' suffix (by
          simp [hdecomp])

/--
Build the recursive budgeted accumulator invariant from the source-loop
statement that each candidate reaches quota at its processed prefix after
adding the candidate-specific budget.
-/
theorem strictSupportAccumulatorBudgetQuota_of_atPrefixes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {candidates : List Candidate}
    (hprefix :
      StrictSupportAccumulatorBudgetQuotaAtPrefixes voters ballots sources
        blockers assignedBudget quota candidates) :
    StrictSupportAccumulatorBudgetQuota voters ballots sources blockers
      assignedBudget quota candidates := by
  induction candidates generalizing blockers with
  | nil =>
      trivial
  | cons candidate rest ih =>
      refine ⟨?_, ?_⟩
      · exact hprefix [] candidate rest rfl
      · refine ih ?_
        intro pref candidate' suffix hdecomp
        exact hprefix (candidate :: pref) candidate' suffix (by
          simp [hdecomp])

@[simp] theorem strictSupportCountWithBlockerPrefix_nil
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) :
    strictSupportCountWithBlockerPrefix voters ballots sources blockers [] = 0 :=
  rfl

@[simp] theorem strictSupportCountWithBlockerPrefix_cons
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate)
    (rest : List Candidate) :
    strictSupportCountWithBlockerPrefix voters ballots sources blockers
        (candidate :: rest) =
      strictSupportCount voters ballots sources blockers candidate +
        strictSupportCountWithBlockerPrefix voters ballots sources
          (insert candidate blockers) rest :=
  rfl

/--
If every counted term in an accumulated-blocker loop is at least `quota`, then
the full accumulator is at least `quota` times the list length.
-/
theorem quota_mul_length_le_strictSupportCountWithBlockerPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ)
    (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorQuota voters ballots sources blockers quota
        candidates) :
    quota * candidates.length ≤
      strictSupportCountWithBlockerPrefix voters ballots sources blockers
        candidates := by
  induction candidates generalizing blockers with
  | nil =>
      simp [strictSupportCountWithBlockerPrefix]
  | cons candidate rest ih =>
      rcases hquota with ⟨hhead, htail⟩
      have htail_le :
          quota * rest.length ≤
            strictSupportCountWithBlockerPrefix voters ballots sources
              (insert candidate blockers) rest :=
        ih (blockers := insert candidate blockers) htail
      calc
        quota * (candidate :: rest).length = quota + quota * rest.length := by
          simp [Nat.mul_succ, Nat.add_comm]
        _ ≤ strictSupportCount voters ballots sources blockers candidate +
            strictSupportCountWithBlockerPrefix voters ballots sources
              (insert candidate blockers) rest :=
          Nat.add_le_add hhead htail_le
        _ =
            strictSupportCountWithBlockerPrefix voters ballots sources blockers
              (candidate :: rest) := rfl

/--
If every counted term in an accumulated-blocker loop reaches `quota` after
including candidate-specific budget units, then the full support accumulator
plus the assigned-budget sum is at least `quota` times the list length.
-/
theorem quota_mul_length_le_budget_sum_add_strictSupportCountWithBlockerPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorBudgetQuota voters ballots sources blockers
        assignedBudget quota candidates) :
    quota * candidates.length ≤
      (candidates.map assignedBudget).sum +
        strictSupportCountWithBlockerPrefix voters ballots sources blockers
          candidates := by
  induction candidates generalizing blockers with
  | nil =>
      simp [strictSupportCountWithBlockerPrefix]
  | cons candidate rest ih =>
      rcases hquota with ⟨hhead, htail⟩
      have htail_le :
          quota * rest.length ≤
            (rest.map assignedBudget).sum +
              strictSupportCountWithBlockerPrefix voters ballots sources
                (insert candidate blockers) rest :=
        ih (blockers := insert candidate blockers) htail
      calc
        quota * (candidate :: rest).length = quota + quota * rest.length := by
          simp [Nat.mul_succ, Nat.add_comm]
        _ ≤
            (assignedBudget candidate +
                strictSupportCount voters ballots sources blockers candidate) +
              ((rest.map assignedBudget).sum +
                strictSupportCountWithBlockerPrefix voters ballots sources
                  (insert candidate blockers) rest) :=
          Nat.add_le_add hhead htail_le
        _ =
            ((candidate :: rest).map assignedBudget).sum +
              strictSupportCountWithBlockerPrefix voters ballots sources blockers
                (candidate :: rest) := by
          simp [strictSupportCountWithBlockerPrefix, Nat.add_assoc,
            Nat.add_left_comm]

/--
Ordered strict-support sum with no initial blockers.

This is the usual support accumulator for a prediction loop that traverses a
candidate list and treats earlier selected candidates as blockers for later
strict-support counts.
-/
def strictSupportCountWithAccumulatedBlockers {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (candidates : List Candidate) : ℕ :=
  strictSupportCountWithBlockerPrefix voters ballots sources ∅ candidates

@[simp] theorem strictSupportCountWithAccumulatedBlockers_nil
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) :
    strictSupportCountWithAccumulatedBlockers voters ballots sources [] = 0 :=
  rfl

@[simp] theorem strictSupportCountWithAccumulatedBlockers_cons
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (candidate : Candidate)
    (rest : List Candidate) :
    strictSupportCountWithAccumulatedBlockers voters ballots sources
        (candidate :: rest) =
      strictSupportCount voters ballots sources ∅ candidate +
        strictSupportCountWithBlockerPrefix voters ballots sources
          (insert candidate ∅) rest :=
  rfl

/-- No-initial-blocker form of
`quota_mul_length_le_strictSupportCountWithBlockerPrefix`. -/
theorem quota_mul_length_le_strictSupportCountWithAccumulatedBlockers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (quota : ℕ) (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorQuota voters ballots sources ∅ quota
        candidates) :
    quota * candidates.length ≤
      strictSupportCountWithAccumulatedBlockers voters ballots sources
        candidates := by
  exact quota_mul_length_le_strictSupportCountWithBlockerPrefix
    voters ballots sources ∅ quota candidates hquota

/-- No-initial-blocker budgeted form of
`quota_mul_length_le_budget_sum_add_strictSupportCountWithBlockerPrefix`. -/
theorem quota_mul_length_le_budget_sum_add_strictSupportCountWithAccumulatedBlockers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorBudgetQuota voters ballots sources ∅
        assignedBudget quota candidates) :
    quota * candidates.length ≤
      (candidates.map assignedBudget).sum +
        strictSupportCountWithAccumulatedBlockers voters ballots sources
          candidates := by
  exact quota_mul_length_le_budget_sum_add_strictSupportCountWithBlockerPrefix
    voters ballots sources ∅ assignedBudget quota candidates hquota

/--
Strict support is active support for `{candidate} ∪ blockers`, restricted to
ballots whose first-ranked candidate belongs to `sources`.
-/
theorem strictSupportVoters_eq_activeSupport_filter_firstChoiceIn
    {Voter Candidate : Type*} [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {sources blockers : Finset Candidate}
    {candidate : Candidate} :
    strictSupportVoters voters ballots sources blockers candidate =
      (activeSupport voters ballots (insert candidate blockers) candidate).filter
        (fun voter => firstChoiceIn (ballots voter) sources) := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · simp [strictSupportVoters, activeSupport, hvoter, and_comm]
  · simp [strictSupportVoters, activeSupport, hvoter]

/--
Strict-support voters are active-support voters for the active set consisting
of the target candidate and the blocker candidates.
-/
theorem strictSupportVoters_subset_activeSupport {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {sources blockers : Finset Candidate}
    {candidate : Candidate} :
    strictSupportVoters voters ballots sources blockers candidate ⊆
      activeSupport voters ballots (insert candidate blockers) candidate := by
  intro voter hvoter
  simp [strictSupportVoters, activeSupport] at hvoter ⊢
  exact ⟨hvoter.1, hvoter.2.2⟩

/--
Strict-support counts are bounded by the corresponding active-support counts.
-/
theorem strictSupportVoters_card_le_activeSupport_card {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {sources blockers : Finset Candidate}
    {candidate : Candidate} :
    (strictSupportVoters voters ballots sources blockers candidate).card ≤
      (activeSupport voters ballots (insert candidate blockers) candidate).card :=
  Finset.card_le_card strictSupportVoters_subset_activeSupport

/--
Active support for a candidate at `insert candidate blockers` is covered by
first-choice support for the candidate plus strict support transferred from
`removed`, provided every active-support voter has first choice in one of those
two classes.

The partition premise is the paper- or rule-specific fact: the generic ballot
API can see the first active candidate, but it does not know which inactive
first choices should be treated as the removed prefix.
-/
theorem activeSupport_subset_firstChoiceVoters_union_strictSupportVoters_of_firstChoice_partition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {removed blockers : Finset Candidate} {candidate : Candidate}
    (hpartition :
      ∀ voter, voter ∈ voters →
        nextActive (ballots voter) (insert candidate blockers) =
          some candidate →
        firstChoiceIn (ballots voter) {candidate} ∨
          firstChoiceIn (ballots voter) removed) :
    activeSupport voters ballots (insert candidate blockers) candidate ⊆
      firstChoiceVoters voters ballots candidate ∪
        strictSupportVoters voters ballots removed blockers candidate := by
  intro voter hvoter
  simp [activeSupport] at hvoter
  rcases hvoter with ⟨hvoters, hnext⟩
  rcases hpartition voter hvoters hnext with hfirst | hremoved
  · have hfirstMem : voter ∈ firstChoiceVoters voters ballots candidate := by
      change voter ∈
        voters.filter fun voter => firstChoiceIn (ballots voter) {candidate}
      exact Finset.mem_filter.mpr ⟨hvoters, hfirst⟩
    exact Finset.mem_union_left _ hfirstMem
  · have hstrictMem :
        voter ∈ strictSupportVoters voters ballots removed blockers candidate := by
      change voter ∈
        voters.filter fun voter =>
          firstChoiceIn (ballots voter) removed ∧
            nextActive (ballots voter) (insert candidate blockers) =
              some candidate
      exact Finset.mem_filter.mpr ⟨hvoters, hremoved, hnext⟩
    exact Finset.mem_union_right _ hstrictMem

/--
Cardinal form of
`activeSupport_subset_firstChoiceVoters_union_strictSupportVoters_of_firstChoice_partition`.
-/
theorem activeSupport_card_le_firstChoiceCount_add_strictSupportCount_of_firstChoice_partition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {removed blockers : Finset Candidate} {candidate : Candidate}
    (hpartition :
      ∀ voter, voter ∈ voters →
        nextActive (ballots voter) (insert candidate blockers) =
          some candidate →
        firstChoiceIn (ballots voter) {candidate} ∨
          firstChoiceIn (ballots voter) removed) :
    (activeSupport voters ballots (insert candidate blockers) candidate).card ≤
      firstChoiceCount voters ballots candidate +
        strictSupportCount voters ballots removed blockers candidate := by
  calc
    (activeSupport voters ballots (insert candidate blockers) candidate).card
        ≤
          (firstChoiceVoters voters ballots candidate ∪
            strictSupportVoters voters ballots removed blockers candidate).card :=
      Finset.card_le_card
        (activeSupport_subset_firstChoiceVoters_union_strictSupportVoters_of_firstChoice_partition
          hpartition)
    _ ≤
        firstChoiceCount voters ballots candidate +
          strictSupportCount voters ballots removed blockers candidate := by
      simpa [firstChoiceCount, strictSupportCount] using
        (Finset.card_union_le
          (firstChoiceVoters voters ballots candidate)
          (strictSupportVoters voters ballots removed blockers candidate))

/--
Active-set form: if `candidate` is active, use `active.erase candidate` as the
blocker set for the transferred strict-support count.
-/
theorem activeSupport_card_le_firstChoiceCount_add_strictSupportCount_removed
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {active removed : Finset Candidate} {candidate : Candidate}
    (hcandidate : candidate ∈ active)
    (hpartition :
      ∀ voter, voter ∈ voters →
        nextActive (ballots voter) active = some candidate →
        firstChoiceIn (ballots voter) {candidate} ∨
          firstChoiceIn (ballots voter) removed) :
    (activeSupport voters ballots active candidate).card ≤
      firstChoiceCount voters ballots candidate +
        strictSupportCount voters ballots removed (active.erase candidate)
          candidate := by
  have hactive_eq : insert candidate (active.erase candidate) = active :=
    Finset.insert_erase hcandidate
  have hactiveSupport_eq :
      activeSupport voters ballots active candidate =
        activeSupport voters ballots (insert candidate (active.erase candidate))
          candidate := by
    rw [hactive_eq]
  have hbound :
      (activeSupport voters ballots (insert candidate (active.erase candidate))
          candidate).card ≤
        firstChoiceCount voters ballots candidate +
          strictSupportCount voters ballots removed (active.erase candidate)
            candidate :=
    activeSupport_card_le_firstChoiceCount_add_strictSupportCount_of_firstChoice_partition
      (removed := removed) (blockers := active.erase candidate)
      (candidate := candidate) (by
        intro voter hvoter hnext
        exact hpartition voter hvoter (by simpa [hactive_eq] using hnext))
  rw [hactiveSupport_eq]
  exact hbound

/--
Reducing every ballot by a candidate set preserves active-support sets when the
active set is reduced by the same candidate set.
-/
theorem activeSupport_removeCandidates_sdiff_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} :
    activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        (active \ removed) candidate =
      activeSupport voters ballots (active \ removed) candidate := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · simp [activeSupport, hvoter,
      nextActive_removeCandidates_sdiff]
  · simp [activeSupport, hvoter]

/--
Reducing every ballot by a candidate set preserves active-support counts when
the active set is reduced by the same candidate set.
-/
theorem activeSupport_card_removeCandidates_sdiff_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} :
    (activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        (active \ removed) candidate).card =
      (activeSupport voters ballots (active \ removed) candidate).card := by
  rw [activeSupport_removeCandidates_sdiff_eq]

/--
If the removed candidates are disjoint from the current active set, deleting
them from every ballot preserves active support at that active set.
-/
theorem activeSupport_removeCandidates_eq_of_disjoint_active
    {Voter Candidate : Type*} [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} (hdisjoint : active ∩ removed = ∅) :
    activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        active candidate =
      activeSupport voters ballots active candidate := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · simp [activeSupport, hvoter,
      nextActive_removeCandidates_eq_of_disjoint_active hdisjoint]
  · simp [activeSupport, hvoter]

/--
If the removed candidates are disjoint from the current active set, deleting
them from every ballot preserves active-support counts at that active set.
-/
theorem activeSupport_card_removeCandidates_eq_of_disjoint_active
    {Voter Candidate : Type*} [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} (hdisjoint : active ∩ removed = ∅) :
    (activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        active candidate).card =
      (activeSupport voters ballots active candidate).card := by
  rw [activeSupport_removeCandidates_eq_of_disjoint_active hdisjoint]

/--
If each voter's first active candidate is unchanged, the active support set for
any candidate is unchanged.
-/
theorem activeSupport_eq_of_forall_nextActive_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hstable : ∀ voter ∈ voters,
      nextActive (after voter) active = nextActive (before voter) active) :
    activeSupport voters after active candidate =
      activeSupport voters before active candidate := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · have hstableVoter := hstable voter hvoter
    simp [activeSupport, hvoter, hstableVoter]
  · simp [activeSupport, hvoter]

/--
If each voter's first active candidate is unchanged, the active support count
for any candidate is unchanged.
-/
theorem activeSupport_card_eq_of_forall_nextActive_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hstable : ∀ voter ∈ voters,
      nextActive (after voter) active = nextActive (before voter) active) :
    (activeSupport voters after active candidate).card =
      (activeSupport voters before active candidate).card := by
  rw [activeSupport_eq_of_forall_nextActive_eq hstable]

/--
Suffixing every ballot in a voter profile preserves active-support counts at an
active set, provided each original ballot already reaches some active
candidate at that set.
-/
theorem activeSupport_eq_of_forall_suffixExtension_nextActive_some
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hext : ∀ voter ∈ voters, IsSuffixExtension (before voter) (after voter))
    (hreaches : ∀ voter ∈ voters,
      ∃ first, nextActive (before voter) active = some first) :
    activeSupport voters after active candidate =
      activeSupport voters before active candidate := by
  exact activeSupport_eq_of_forall_nextActive_eq (by
    intro voter hvoter
    rcases hext voter hvoter with ⟨suffix, hsuffix⟩
    rcases hreaches voter hvoter with ⟨first, hfirst⟩
    have hafter : nextActive (after voter) active = some first := by
      rw [hsuffix]
      exact nextActive_append_of_some hfirst
    rw [hafter, hfirst])

/--
Suffixing every ballot in a voter profile preserves active-support counts at an
active set, provided each original ballot already reaches some active
candidate at that set.
-/
theorem activeSupport_card_eq_of_forall_suffixExtension_nextActive_some
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hext : ∀ voter ∈ voters, IsSuffixExtension (before voter) (after voter))
    (hreaches : ∀ voter ∈ voters,
      ∃ first, nextActive (before voter) active = some first) :
    (activeSupport voters after active candidate).card =
      (activeSupport voters before active candidate).card := by
  rw [activeSupport_eq_of_forall_suffixExtension_nextActive_some hext hreaches]

/--
Prefixing inactive candidates onto every ballot in a voter profile preserves
active-support sets at the current active set.
-/
theorem activeSupport_eq_of_forall_prefixExtension_inactive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hext : ∀ voter ∈ voters,
      IsPrefixExtension (pref voter) (before voter) (after voter))
    (hpref : ∀ voter ∈ voters, ∀ c, c ∈ pref voter → c ∉ active) :
    activeSupport voters after active candidate =
      activeSupport voters before active candidate := by
  exact activeSupport_eq_of_forall_nextActive_eq (by
    intro voter hvoter
    rw [hext voter hvoter]
    exact nextActive_append_left_of_forall_not_mem (hpref voter hvoter))

/--
Prefixing inactive candidates onto every ballot in a voter profile preserves
active-support counts at the current active set.
-/
theorem activeSupport_card_eq_of_forall_prefixExtension_inactive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hext : ∀ voter ∈ voters,
      IsPrefixExtension (pref voter) (before voter) (after voter))
    (hpref : ∀ voter ∈ voters, ∀ c, c ∈ pref voter → c ∉ active) :
    (activeSupport voters after active candidate).card =
      (activeSupport voters before active candidate).card := by
  rw [activeSupport_eq_of_forall_prefixExtension_inactive hext hpref]

/--
Appending a strategy ballot after an exhausted prefix for every voter preserves
the active-support sets of the strategy ballots at the current active set.
-/
theorem activeSupport_eq_of_forall_append_exhausted_prefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref strategy completed : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = pref voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      nextActive (pref voter) active = none) :
    activeSupport voters completed active candidate =
      activeSupport voters strategy active candidate := by
  exact activeSupport_eq_of_forall_nextActive_eq (by
    intro voter hvoter
    rw [hcompleted voter hvoter]
    exact nextActive_append_of_none (hexhausted voter hvoter))

/--
Appending a strategy ballot after an exhausted prefix for every voter preserves
the active-support counts of the strategy ballots at the current active set.
-/
theorem activeSupport_card_eq_of_forall_append_exhausted_prefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref strategy completed : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = pref voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      nextActive (pref voter) active = none) :
    (activeSupport voters completed active candidate).card =
      (activeSupport voters strategy active candidate).card := by
  rw [activeSupport_eq_of_forall_append_exhausted_prefix
    hcompleted hexhausted]

/--
If every voter in `available` belongs to `voters` and activates `candidate`,
then `candidate`'s active support is at least `available.card`.
-/
theorem card_le_activeSupport_card_of_subset_forall_nextActive_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {available voters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : available ⊆ voters)
    (hactive : ∀ voter ∈ available,
      nextActive (ballots voter) active = some candidate) :
    available.card ≤ (activeSupport voters ballots active candidate).card := by
  apply Finset.card_le_card
  intro voter hvoter
  simp [activeSupport, hsubset hvoter, hactive voter hvoter]

/--
Completing available exhausted ballots with strategy ballots that activate
`candidate` gives at least one active-support voter per available ballot.
-/
theorem card_le_activeSupport_card_of_subset_forall_append_exhausted_prefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {available voters : Finset Voter}
    {pref strategy completed : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : available ⊆ voters)
    (hcompleted : ∀ voter ∈ available,
      completed voter = pref voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ available,
      nextActive (pref voter) active = none)
    (hstrategy : ∀ voter ∈ available,
      nextActive (strategy voter) active = some candidate) :
    available.card ≤ (activeSupport voters completed active candidate).card :=
  card_le_activeSupport_card_of_subset_forall_nextActive_eq hsubset (by
    intro voter hvoter
    rw [hcompleted voter hvoter]
    exact (nextActive_append_of_none (hexhausted voter hvoter)).trans
      (hstrategy voter hvoter))

/--
If the old voter set is contained in the new voter set and every old voter's
first active candidate is unchanged, then old active support is contained in
new active support.
-/
theorem activeSupport_subset_of_subset_forall_nextActive_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {beforeVoters afterVoters : Finset Voter}
    {before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : beforeVoters ⊆ afterVoters)
    (hstable : ∀ voter ∈ beforeVoters,
      nextActive (after voter) active = nextActive (before voter) active) :
    activeSupport beforeVoters before active candidate ⊆
      activeSupport afterVoters after active candidate := by
  intro voter hvoter
  simp [activeSupport] at hvoter ⊢
  exact ⟨hsubset hvoter.1, by rw [hstable voter hvoter.1, hvoter.2]⟩

/--
Adding a genuinely new voter whose first active candidate is `candidate`
strictly increases `candidate`'s active-support count, provided old voters'
first active choices are unchanged.
-/
theorem activeSupport_card_lt_of_subset_forall_nextActive_eq_exists_new
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {beforeVoters afterVoters : Finset Voter}
    {before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : beforeVoters ⊆ afterVoters)
    (hstable : ∀ voter ∈ beforeVoters,
      nextActive (after voter) active = nextActive (before voter) active)
    (hnew : ∃ voter, voter ∈ afterVoters ∧ voter ∉ beforeVoters ∧
      nextActive (after voter) active = some candidate) :
    (activeSupport beforeVoters before active candidate).card <
      (activeSupport afterVoters after active candidate).card := by
  rcases hnew with ⟨voter, hafter, hbefore, hactive⟩
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact activeSupport_subset_of_subset_forall_nextActive_eq hsubset hstable
  · intro heq
    have hafterSupport :
        voter ∈ activeSupport afterVoters after active candidate := by
      simp [activeSupport, hafter, hactive]
    have hbeforeSupport :
        voter ∈ activeSupport beforeVoters before active candidate := by
      simpa [heq] using hafterSupport
    have hbeforeVoter : voter ∈ beforeVoters := by
      have hbeforeSupport' := hbeforeSupport
      simp [activeSupport] at hbeforeSupport'
      exact hbeforeSupport'.1
    exact hbefore hbeforeVoter

/--
Prefix-through-candidate strategic edits cannot add voters whose first active
candidate is the edited candidate, as long as that candidate is still active.
-/
theorem activeSupport_subset_of_preservesPrefixThrough {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hcandidate : candidate ∈ active)
    (hpreserve : ∀ voter ∈ voters,
      PreservesPrefixThrough candidate (before voter) (after voter)) :
    activeSupport voters after active candidate ⊆
      activeSupport voters before active candidate := by
  intro voter hvoter
  simp [activeSupport] at hvoter ⊢
  exact ⟨hvoter.1,
    nextActive_eq_some_of_preservesPrefixThrough
      (hpreserve voter hvoter.1) hcandidate hvoter.2⟩

/--
The number of voters whose first active candidate is `candidate` cannot increase
under prefix-through-candidate edits while `candidate` is still active.
-/
theorem activeSupport_card_le_of_preservesPrefixThrough {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hcandidate : candidate ∈ active)
    (hpreserve : ∀ voter ∈ voters,
      PreservesPrefixThrough candidate (before voter) (after voter)) :
    (activeSupport voters after active candidate).card ≤
      (activeSupport voters before active candidate).card :=
  Finset.card_le_card
    (activeSupport_subset_of_preservesPrefixThrough hcandidate hpreserve)

end Ballot

/--
A finite source witness that a prediction routine has identified an initial
loss prefix whose length is large enough for a claimed lower bound.
-/
structure InitialLossPrefixCertificate {Candidate Sequence : Type*}
    (lossCandidates : Finset Candidate)
    (initialLossCount : Sequence → ℕ)
    (lowerInitialLosses : ℕ) (sequence : Sequence) where
  lossPrefix : List Candidate
  prefix_nodup : lossPrefix.Nodup
  prefix_subset_lossCandidates :
    ∀ candidate, candidate ∈ lossPrefix → candidate ∈ lossCandidates
  lower_le_prefix_length : lowerInitialLosses ≤ lossPrefix.length
  prefix_length_le_initialLossCount :
    lossPrefix.length ≤ initialLossCount sequence

/-- Project the lower-initial-loss inequality from a concrete prefix witness. -/
theorem lowerInitialLosses_le_initialLossCount_of_initialLossPrefixCertificate
    {Candidate Sequence : Type*} {lossCandidates : Finset Candidate}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    {sequence : Sequence}
    (cert :
      InitialLossPrefixCertificate lossCandidates initialLossCount
        lowerInitialLosses sequence) :
    lowerInitialLosses ≤ initialLossCount sequence :=
  le_trans cert.lower_le_prefix_length cert.prefix_length_le_initialLossCount

/--
Per-sequence initial-loss prefix witnesses give the loss-floor premise used by
sequence-reduction coverage arguments.
-/
theorem loss_floor_of_initialLossPrefixCertificates
    {Candidate Sequence : Type*} {lossCandidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    (cert :
      ∀ sequence, feasibleSequence sequence →
        InitialLossPrefixCertificate lossCandidates initialLossCount
          lowerInitialLosses sequence) :
    ∀ sequence, feasibleSequence sequence →
      lowerInitialLosses ≤ initialLossCount sequence := by
  intro sequence hfeasible
  exact lowerInitialLosses_le_initialLossCount_of_initialLossPrefixCertificate
    (cert sequence hfeasible)

end Voting
end SocialChoice
end AppliedModelingLib
