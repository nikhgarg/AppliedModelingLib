import AppliedModelingLib.Learning.Online.Resampling
import Mathlib.Tactic

/-!
# Finite adaptive resampling transcripts

An adaptive resampling execution must retain the information needed to state
its terminal delayed-label comparison.  This module provides the finite trace
container: a prefix length and one optional record for each horizon position.
It is deliberately independent of a particular learner or adversary.
-/

namespace AppliedModelingLib.Learning.Online

/-- One delayed-label round records the predictable context, the fresh iid
batch drawn after that context, and the resulting label. -/
abbrev AdaptiveResamplingRecord (Context Sample Label : Type*) (sampleCount : ℕ) :=
  Context × (Fin sampleCount → Sample) × Label

/-- A bounded-horizon adaptive resampling transcript.  A `some` entry records
a completed round; entries beyond `nextRound` remain available for later
extension. -/
structure AdaptiveResamplingTrace (Context Sample Label : Type*)
    (roundCount sampleCount : ℕ) where
  nextRound : Fin (roundCount + 1)
  entry : Fin roundCount → Option (AdaptiveResamplingRecord Context Sample Label sampleCount)
deriving Fintype, DecidableEq

/-- The empty delayed-label transcript. -/
def AdaptiveResamplingTrace.empty (Context Sample Label : Type*)
    (roundCount sampleCount : ℕ) :
    AdaptiveResamplingTrace Context Sample Label roundCount sampleCount where
  nextRound := ⟨0, Nat.succ_pos _⟩
  entry := fun _ => none

/-- Append one completed delayed-label round when the transcript is not full.
Appending to a full transcript leaves it unchanged. -/
def AdaptiveResamplingTrace.append
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label) :
    AdaptiveResamplingTrace Context Sample Label roundCount sampleCount :=
  if hnext : trace.nextRound.1 < roundCount then
    { nextRound := ⟨trace.nextRound.1 + 1, by omega⟩
      entry := fun round =>
        if round = ⟨trace.nextRound.1, hnext⟩ then some (context, batch, label)
        else trace.entry round }
  else trace

/-- The prefix consisting of the first `count` slots of a transcript. -/
def AdaptiveResamplingTrace.prefix
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (count : Fin (roundCount + 1)) :
    AdaptiveResamplingTrace Context Sample Label roundCount sampleCount where
  nextRound := count
  entry := fun round => if round.1 < count.1 then trace.entry round else none

/-- A well-formed transcript has no records at or after its next empty slot. -/
def AdaptiveResamplingTrace.IsNormalized
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount) : Prop :=
  ∀ round, trace.nextRound.1 ≤ round.1 → trace.entry round = none

/-- Every slot strictly before the current prefix endpoint has been written.
Together with `IsNormalized`, this says that the transcript is exactly a
contiguous sequence of completed rounds. -/
def AdaptiveResamplingTrace.RecordsArePresent
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount) : Prop :=
  ∀ round, round.1 < trace.nextRound.1 → ∃ record, trace.entry round = some record

/-- The transcript immediately before a designated horizon round. -/
def AdaptiveResamplingTrace.prefixBefore
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (round : Fin roundCount) :
    AdaptiveResamplingTrace Context Sample Label roundCount sampleCount :=
  trace.prefix ⟨round.1, Nat.lt_succ_of_lt round.2⟩

/-- Every completed record of a transcript passed its own pre-batch failure
test.  The test is evaluated on the recovered preceding prefix, rather than
on the terminal state. -/
def AdaptiveResamplingTrace.RecordsAreGood
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Prop)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount) : Prop :=
  ∀ round, round.1 < trace.nextRound.1 →
    ∃ context batch label, trace.entry round = some (context, batch, label) ∧
      ¬ bad round.1 (trace.prefixBefore round) batch

/-- Every completed record of a transcript passed a test which is allowed to
inspect the realized context and post-batch label as well as the batch itself.
This is the delayed-observation counterpart to `RecordsAreGood`: it supports
protocols, such as Algorithm 5, in which the point at which a batch is
evaluated is sampled after the batch but is retained in the completed record.
The strict prefix is still the state at which the batch law was selected. -/
def AdaptiveResamplingTrace.RecordsAreGoodAfter
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Context → (Fin sampleCount → Sample) → Label → Prop)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount) : Prop :=
  ∀ round, round.1 < trace.nextRound.1 →
    ∃ context batch label, trace.entry round = some (context, batch, label) ∧
      ¬ bad round.1 (trace.prefixBefore round) context batch label

/-- Read a transcript record, using a caller-supplied value only outside the
completed prefix.  On a terminal no-failure execution every horizon position
is completed, so the default is never used in the delayed-label guarantee. -/
def AdaptiveResamplingTrace.recordAt
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (defaultRecord : AdaptiveResamplingRecord Context Sample Label sampleCount)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (round : Fin roundCount) :
    AdaptiveResamplingRecord Context Sample Label sampleCount :=
  (trace.entry round).getD defaultRecord

/-- Reading a known completed slot returns precisely its stored record. -/
theorem AdaptiveResamplingTrace.recordAt_eq_of_entry_eq_some
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (defaultRecord : AdaptiveResamplingRecord Context Sample Label sampleCount)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (round : Fin roundCount)
    (record : AdaptiveResamplingRecord Context Sample Label sampleCount)
    (hentry : trace.entry round = some record) :
    trace.recordAt defaultRecord round = record := by
  simp [AdaptiveResamplingTrace.recordAt, hentry]

/-- The empty transcript is normalized. -/
theorem AdaptiveResamplingTrace.empty_isNormalized
    (Context Sample Label : Type*) (roundCount sampleCount : ℕ) :
    (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount).IsNormalized := by
  intro round _
  rfl

/-- The empty transcript vacuously has every completed slot present. -/
theorem AdaptiveResamplingTrace.empty_recordsArePresent
    (Context Sample Label : Type*) (roundCount sampleCount : ℕ) :
    (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount).RecordsArePresent := by
  intro round hround
  change round.1 < 0 at hround
  omega

/-- The empty transcript has no completed record that could fail a batch
test. -/
theorem AdaptiveResamplingTrace.empty_recordsAreGood
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Prop) :
    (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount).RecordsAreGood bad := by
  intro round hround
  change round.1 < 0 at hround
  omega

/-- The empty transcript vacuously satisfies every delayed-observation
record test. -/
theorem AdaptiveResamplingTrace.empty_recordsAreGoodAfter
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Context → (Fin sampleCount → Sample) → Label → Prop) :
    (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount).RecordsAreGoodAfter
      bad := by
  intro round hround
  change round.1 < 0 at hround
  omega

/-- Restricting a transcript to a prefix always produces a normalized trace. -/
theorem AdaptiveResamplingTrace.prefix_isNormalized
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (count : Fin (roundCount + 1)) :
    (trace.prefix count).IsNormalized := by
  intro round hround
  change count.1 ≤ round.1 at hround
  simp [AdaptiveResamplingTrace.prefix, Nat.not_lt.mpr hround]

/-- A completed entry of a prefix is exactly the entry of its parent trace. -/
theorem AdaptiveResamplingTrace.prefix_entry_of_lt
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (count : Fin (roundCount + 1)) (round : Fin roundCount)
    (hround : round.1 < count.1) :
    (trace.prefix count).entry round = trace.entry round := by
  simp [AdaptiveResamplingTrace.prefix, hround]

/-- Entries outside a prefix are empty. -/
theorem AdaptiveResamplingTrace.prefix_entry_of_le
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (count : Fin (roundCount + 1)) (round : Fin roundCount)
    (hround : count.1 ≤ round.1) :
    (trace.prefix count).entry round = none := by
  simp [AdaptiveResamplingTrace.prefix, Nat.not_lt.mpr hround]

/-- A normalized transcript is exactly its own prefix at the current
completed-round count. -/
theorem AdaptiveResamplingTrace.prefix_nextRound_eq_of_normalized
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (htrace : trace.IsNormalized) :
    trace.prefix trace.nextRound = trace := by
  cases trace with
  | mk next entry =>
    dsimp [AdaptiveResamplingTrace.prefix, AdaptiveResamplingTrace.IsNormalized] at htrace ⊢
    congr
    funext round
    by_cases hround : round.1 < next.1
    · simp [hround]
    · have hle : next.1 ≤ round.1 := Nat.le_of_not_gt hround
      simp [hround, htrace round hle]

/-- Appending a later record leaves every earlier prefix unchanged. -/
theorem AdaptiveResamplingTrace.append_prefix_of_le_nextRound
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (count : Fin (roundCount + 1))
    (hcount : count.1 ≤ trace.nextRound.1) :
    (trace.append context batch label).prefix count = trace.prefix count := by
  by_cases hnext : trace.nextRound.1 < roundCount
  · cases trace with
    | mk next entry =>
      dsimp [AdaptiveResamplingTrace.append, AdaptiveResamplingTrace.prefix] at hcount ⊢
      simp [hnext]
      funext round
      by_cases hround : round.1 < count.1
      · have hne : round.1 ≠ next.1 := by omega
        have hslot : round ≠ ⟨next.1, hnext⟩ := by
          intro heq
          exact hne (congrArg Fin.val heq)
        simp [hround, hslot]
      · simp [hround]
  · simp [AdaptiveResamplingTrace.append, hnext]

/-- Immediately before an appended record, the final trace recovers the
normalized preceding transcript exactly. -/
theorem AdaptiveResamplingTrace.append_prefix_current_eq
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (htrace : trace.IsNormalized)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (hnext : trace.nextRound.1 < roundCount) :
    (trace.append context batch label).prefix
      ⟨trace.nextRound.1, Nat.lt_succ_of_lt hnext⟩ = trace := by
  have hcountEq : (⟨trace.nextRound.1, Nat.lt_succ_of_lt hnext⟩ : Fin (roundCount + 1)) =
      trace.nextRound := by
    apply Fin.ext
    rfl
  calc
    (trace.append context batch label).prefix
        ⟨trace.nextRound.1, Nat.lt_succ_of_lt hnext⟩ =
        trace.prefix ⟨trace.nextRound.1, Nat.lt_succ_of_lt hnext⟩ :=
      AdaptiveResamplingTrace.append_prefix_of_le_nextRound trace context batch label
        ⟨trace.nextRound.1, Nat.lt_succ_of_lt hnext⟩ le_rfl
    _ = trace.prefix trace.nextRound := by rw [hcountEq]
    _ = trace := AdaptiveResamplingTrace.prefix_nextRound_eq_of_normalized trace htrace

/-- Appending a round writes precisely the current empty slot. -/
theorem AdaptiveResamplingTrace.append_entry_current
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (hnext : trace.nextRound.1 < roundCount) :
    (trace.append context batch label).entry ⟨trace.nextRound.1, hnext⟩ =
      some (context, batch, label) := by
  simp [AdaptiveResamplingTrace.append, hnext]

/-- Appending one round does not alter any other transcript entry. -/
theorem AdaptiveResamplingTrace.append_entry_of_ne
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (round : Fin roundCount) (hround : round.1 ≠ trace.nextRound.1)
    (hnext : trace.nextRound.1 < roundCount) :
    (trace.append context batch label).entry round = trace.entry round := by
  have hround' : round ≠ ⟨trace.nextRound.1, hnext⟩ := by
    intro heq
    exact hround (congrArg Fin.val heq)
  simp [AdaptiveResamplingTrace.append, hnext, hround']

/-- An append below the horizon advances the completed-round counter by one. -/
theorem AdaptiveResamplingTrace.append_nextRound
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (hnext : trace.nextRound.1 < roundCount) :
    (trace.append context batch label).nextRound.1 = trace.nextRound.1 + 1 := by
  simp [AdaptiveResamplingTrace.append, hnext]

/-- Appending preserves transcript normalization. -/
theorem AdaptiveResamplingTrace.append_isNormalized
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (htrace : trace.IsNormalized)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label) :
    (trace.append context batch label).IsNormalized := by
  by_cases hnext : trace.nextRound.1 < roundCount
  · intro round hround
    have hnewCount := AdaptiveResamplingTrace.append_nextRound trace context batch label hnext
    rw [hnewCount] at hround
    have hroundNe : round.1 ≠ trace.nextRound.1 := by omega
    have hprevious : trace.nextRound.1 ≤ round.1 := by omega
    have hentry := AdaptiveResamplingTrace.append_entry_of_ne trace context batch label round
      hroundNe hnext
    rw [hentry]
    exact htrace round hprevious
  · simpa [AdaptiveResamplingTrace.append, hnext] using htrace

/-- Appending at the current empty slot makes every completed slot present. -/
theorem AdaptiveResamplingTrace.append_recordsArePresent
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (hpresent : trace.RecordsArePresent)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (hnext : trace.nextRound.1 < roundCount) :
    (trace.append context batch label).RecordsArePresent := by
  intro round hround
  have hnewCount := AdaptiveResamplingTrace.append_nextRound trace context batch label hnext
  rw [hnewCount] at hround
  by_cases hearlier : round.1 < trace.nextRound.1
  · obtain ⟨record, hrecord⟩ := hpresent round hearlier
    refine ⟨record, ?_⟩
    have hne : round.1 ≠ trace.nextRound.1 := by omega
    exact (AdaptiveResamplingTrace.append_entry_of_ne trace context batch label round hne hnext).trans
      hrecord
  · have hroundEq : round.1 = trace.nextRound.1 := by omega
    have hroundEq' : round = ⟨trace.nextRound.1, hnext⟩ := by
      apply Fin.ext
      exact hroundEq
    subst round
    exact ⟨(context, batch, label),
      AdaptiveResamplingTrace.append_entry_current trace context batch label hnext⟩

/-- If all earlier records passed their pre-batch tests, then appending a
new passing batch preserves that property for the entire transcript. -/
theorem AdaptiveResamplingTrace.append_recordsAreGood
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Prop)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (htrace : trace.IsNormalized) (hgood : trace.RecordsAreGood bad)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (hnext : trace.nextRound.1 < roundCount)
    (hnew : ¬ bad trace.nextRound.1 trace batch) :
    (trace.append context batch label).RecordsAreGood bad := by
  intro round hround
  have hnewCount := AdaptiveResamplingTrace.append_nextRound trace context batch label hnext
  rw [hnewCount] at hround
  by_cases hold : round.1 < trace.nextRound.1
  · obtain ⟨oldContext, oldBatch, oldLabel, holdEntry, holdGood⟩ := hgood round hold
    refine ⟨oldContext, oldBatch, oldLabel, ?_, ?_⟩
    · have hne : round.1 ≠ trace.nextRound.1 := by omega
      exact (AdaptiveResamplingTrace.append_entry_of_ne trace context batch label round hne hnext).trans
        holdEntry
    · rw [show (trace.append context batch label).prefixBefore round = trace.prefixBefore round by
        unfold AdaptiveResamplingTrace.prefixBefore
        apply AdaptiveResamplingTrace.append_prefix_of_le_nextRound
        exact Nat.le_of_lt hold]
      exact holdGood
  · have hval : round.1 = trace.nextRound.1 := by omega
    have heq : round = ⟨trace.nextRound.1, hnext⟩ := by
      apply Fin.ext
      exact hval
    subst round
    refine ⟨context, batch, label, ?_, ?_⟩
    · exact AdaptiveResamplingTrace.append_entry_current trace context batch label hnext
    · rw [show (trace.append context batch label).prefixBefore
          ⟨trace.nextRound.1, hnext⟩ = trace by
        unfold AdaptiveResamplingTrace.prefixBefore
        exact AdaptiveResamplingTrace.append_prefix_current_eq trace htrace context batch label hnext]
      exact hnew

/-- If all earlier records passed their tests, then appending a record that
passes its test preserves the corresponding delayed-observation invariant. -/
theorem AdaptiveResamplingTrace.append_recordsAreGoodAfter
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Context → (Fin sampleCount → Sample) → Label → Prop)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (htrace : trace.IsNormalized) (hgood : trace.RecordsAreGoodAfter bad)
    (context : Context) (batch : Fin sampleCount → Sample) (label : Label)
    (hnext : trace.nextRound.1 < roundCount)
    (hnew : ¬ bad trace.nextRound.1 trace context batch label) :
    (trace.append context batch label).RecordsAreGoodAfter bad := by
  intro round hround
  have hnewCount := AdaptiveResamplingTrace.append_nextRound trace context batch label hnext
  rw [hnewCount] at hround
  by_cases hold : round.1 < trace.nextRound.1
  · obtain ⟨oldContext, oldBatch, oldLabel, holdEntry, holdGood⟩ := hgood round hold
    refine ⟨oldContext, oldBatch, oldLabel, ?_, ?_⟩
    · have hne : round.1 ≠ trace.nextRound.1 := by omega
      exact (AdaptiveResamplingTrace.append_entry_of_ne trace context batch label round hne hnext).trans
        holdEntry
    · rw [show (trace.append context batch label).prefixBefore round = trace.prefixBefore round by
        unfold AdaptiveResamplingTrace.prefixBefore
        apply AdaptiveResamplingTrace.append_prefix_of_le_nextRound
        exact Nat.le_of_lt hold]
      exact holdGood
  · have hval : round.1 = trace.nextRound.1 := by omega
    have heq : round = ⟨trace.nextRound.1, hnext⟩ := by
      apply Fin.ext
      exact hval
    subst round
    refine ⟨context, batch, label, ?_, ?_⟩
    · exact AdaptiveResamplingTrace.append_entry_current trace context batch label hnext
    · rw [show (trace.append context batch label).prefixBefore
          ⟨trace.nextRound.1, hnext⟩ = trace by
        unfold AdaptiveResamplingTrace.prefixBefore
        exact AdaptiveResamplingTrace.append_prefix_current_eq trace htrace context batch label hnext]
      exact hnew

/-- Every completed trace slot was generated by the delayed-label protocol
from its own preceding prefix.  This is stronger than mere slot presence: it
remembers both the predictable context and the post-batch label rule, while
leaving the fresh batch existential because it is the randomized outcome. -/
def AdaptiveResamplingTrace.RecordsFollowProtocol
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount) : Prop :=
  ∀ round, round.1 < trace.nextRound.1 → ∃ batch,
    trace.entry round = some
      (contextAt round.1 (trace.prefixBefore round), batch,
        labelAt round.1 (trace.prefixBefore round) batch)

/-- The empty trace vacuously follows every delayed-label protocol. -/
theorem AdaptiveResamplingTrace.empty_recordsFollowProtocol
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label) :
    (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount).RecordsFollowProtocol
      contextAt labelAt := by
  intro round hround
  change round.1 < 0 at hround
  omega

/-- Appending the next protocol-generated record preserves exact protocol
faithfulness of every earlier record and establishes it for the new slot. -/
theorem AdaptiveResamplingTrace.append_recordsFollowProtocol
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (hnormalized : trace.IsNormalized)
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (hprotocol : trace.RecordsFollowProtocol contextAt labelAt)
    (batch : Fin sampleCount → Sample) (hnext : trace.nextRound.1 < roundCount) :
    (trace.append (contextAt trace.nextRound.1 trace) batch
      (labelAt trace.nextRound.1 trace batch)).RecordsFollowProtocol contextAt labelAt := by
  intro round hround
  have hnewCount := AdaptiveResamplingTrace.append_nextRound trace
    (contextAt trace.nextRound.1 trace) batch (labelAt trace.nextRound.1 trace batch) hnext
  rw [hnewCount] at hround
  by_cases hearlier : round.1 < trace.nextRound.1
  · obtain ⟨oldBatch, hold⟩ := hprotocol round hearlier
    refine ⟨oldBatch, ?_⟩
    have hne : round.1 ≠ trace.nextRound.1 := by omega
    have hpref :
        (trace.append (contextAt trace.nextRound.1 trace) batch
          (labelAt trace.nextRound.1 trace batch)).prefixBefore round =
          trace.prefixBefore round := by
      unfold AdaptiveResamplingTrace.prefixBefore
      apply AdaptiveResamplingTrace.append_prefix_of_le_nextRound
      exact Nat.le_of_lt hearlier
    rw [hpref]
    exact (AdaptiveResamplingTrace.append_entry_of_ne trace
      (contextAt trace.nextRound.1 trace) batch (labelAt trace.nextRound.1 trace batch)
      round hne hnext).trans hold
  · have hroundEq : round.1 = trace.nextRound.1 := by omega
    have hroundEq' : round = ⟨trace.nextRound.1, hnext⟩ := by
      apply Fin.ext
      exact hroundEq
    subst round
    refine ⟨batch, ?_⟩
    rw [show (trace.append (contextAt trace.nextRound.1 trace) batch
      (labelAt trace.nextRound.1 trace batch)).prefixBefore
        ⟨trace.nextRound.1, hnext⟩ = trace by
      unfold AdaptiveResamplingTrace.prefixBefore
      exact AdaptiveResamplingTrace.append_prefix_current_eq trace hnormalized
        (contextAt trace.nextRound.1 trace) batch
        (labelAt trace.nextRound.1 trace batch) hnext]
    exact AdaptiveResamplingTrace.append_entry_current trace
      (contextAt trace.nextRound.1 trace) batch
      (labelAt trace.nextRound.1 trace batch) hnext

/-- The canonical trace update for a delayed-label protocol.  The context is
chosen from the prefix before the new batch is sampled; the label may then
depend on that batch. -/
def adaptiveResamplingTraceAdvance
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label) :
    AppliedModelingLib.PreferenceRL.AdaptiveStateUpdate
      (AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
      (Fin sampleCount → Sample) :=
  fun round trace batch => trace.append (contextAt round trace) (batch := batch)
    (labelAt round trace batch)

/-- The trace update writes the context chosen before the batch and the label
chosen after that batch into the current slot. -/
theorem adaptiveResamplingTraceAdvance_entry_current
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (round : ℕ) (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (batch : Fin sampleCount → Sample) (hnext : trace.nextRound.1 < roundCount) :
    (adaptiveResamplingTraceAdvance contextAt labelAt round trace batch).entry
      ⟨trace.nextRound.1, hnext⟩ =
        some (contextAt round trace, batch, labelAt round trace batch) := by
  exact AdaptiveResamplingTrace.append_entry_current trace
    (contextAt round trace) batch (labelAt round trace batch) hnext

/-- While a delayed-label transcript is not full, its canonical update
advances the number of completed rounds by one. -/
theorem adaptiveResamplingTraceAdvance_nextRound
    {Context Sample Label : Type*} {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (round : ℕ) (trace : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
    (batch : Fin sampleCount → Sample) (hnext : trace.nextRound.1 < roundCount) :
    (adaptiveResamplingTraceAdvance contextAt labelAt round trace batch).nextRound.1 =
      trace.nextRound.1 + 1 := by
  exact AdaptiveResamplingTrace.append_nextRound trace
    (contextAt round trace) batch (labelAt round trace batch) hnext

/-- The fresh iid batch kernel selected from the current transcript. -/
noncomputable def adaptiveResamplingTraceOutcomeLaw
    {Context Sample Label : Type*} [Fintype Sample] [DecidableEq Sample]
    {roundCount sampleCount : ℕ}
    (lawAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → PMF Sample) :
    AppliedModelingLib.PreferenceRL.AdaptiveOutcomeKernel
      (AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
      (Fin sampleCount → Sample) :=
  fun round trace => pmfProduct (Fin sampleCount) Sample (lawAt round trace)

/-- The two-sided failure event for the current iid batch. -/
def adaptiveResamplingTraceBad
    {Context Sample Label : Type*} [Fintype Sample] [DecidableEq Sample]
    {roundCount sampleCount : ℕ}
    (lawAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → PMF Sample)
    (scoreAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Sample → ℝ)
    (error : ℝ) :
    ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Prop :=
  fun round trace batch => error ≤
    |resamplingSampleAverage batch (scoreAt round trace) - pmfExp (lawAt round trace)
      (scoreAt round trace)|

/-- The literal finite delayed-label trace law: the predictable context is
selected from the prior trace, then an iid batch is drawn, then the label and
the next trace entry are determined. -/
noncomputable def adaptiveResamplingTraceLaw
    {Context Sample Label : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Sample] [DecidableEq Sample] [Fintype Label] [DecidableEq Label]
    {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (lawAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → PMF Sample)
    (scoreAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Sample → ℝ)
    (error : ℝ) :
    PMF (AdaptiveResamplingTrace Context Sample Label roundCount sampleCount × Bool) := by
  classical
  exact AppliedModelingLib.PreferenceRL.adaptiveQueryStateLaw
    (PMF.pure (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount))
    (adaptiveResamplingTraceOutcomeLaw lawAt)
    (adaptiveResamplingTraceAdvance contextAt labelAt)
    (adaptiveResamplingTraceBad lawAt scoreAt error)
    roundCount

/-- Every positive-mass state of a canonical delayed-label trace execution is
normalized, contains a contiguous prefix of completed records, has exactly the
expected prefix length, and—when its carried failure flag is false—contains
only batches that passed their own pre-batch test. -/
theorem adaptiveResamplingTrace_support_invariant
    {Context Sample Label : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Sample] [DecidableEq Sample] [Fintype Label] [DecidableEq Label]
    {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (outcomeLaw : AppliedModelingLib.PreferenceRL.AdaptiveOutcomeKernel
      (AdaptiveResamplingTrace Context Sample Label roundCount sampleCount)
      (Fin sampleCount → Sample))
    (bad : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Prop)
    [∀ round trace batch, Decidable (bad round trace batch)] :
    ∀ queryCount stateFailure,
      stateFailure ∈
        (AppliedModelingLib.PreferenceRL.adaptiveQueryStateLaw
          (PMF.pure (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount))
          outcomeLaw (adaptiveResamplingTraceAdvance contextAt labelAt) bad queryCount).support →
      stateFailure.1.IsNormalized ∧ stateFailure.1.RecordsArePresent ∧
        stateFailure.1.nextRound.1 = Nat.min queryCount roundCount ∧
        (stateFailure.2 = false → stateFailure.1.RecordsAreGood bad) := by
  apply AppliedModelingLib.PreferenceRL.adaptiveQueryStateLaw_support_invariant
    (PMF.pure (AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount))
    outcomeLaw (adaptiveResamplingTraceAdvance contextAt labelAt) bad
    (fun queryIndex trace flag => trace.IsNormalized ∧ trace.RecordsArePresent ∧
      trace.nextRound.1 = Nat.min queryIndex roundCount ∧
      (flag = false → trace.RecordsAreGood bad))
  · intro state hstate
    have hstateEq : state =
        AdaptiveResamplingTrace.empty Context Sample Label roundCount sampleCount := by
      simpa using hstate
    subst state
    refine ⟨AdaptiveResamplingTrace.empty_isNormalized Context Sample Label roundCount sampleCount,
      AdaptiveResamplingTrace.empty_recordsArePresent Context Sample Label roundCount sampleCount,
      rfl, ?_⟩
    intro _
    exact AdaptiveResamplingTrace.empty_recordsAreGood bad
  · intro queryIndex trace flag batch hinvariant
    rcases hinvariant with ⟨hnormalized, hpresent, hcount, hrecords⟩
    by_cases hindex : queryIndex < roundCount
    · have hmin : Nat.min queryIndex roundCount = queryIndex :=
        Nat.min_eq_left (Nat.le_of_lt hindex)
      rw [hmin] at hcount
      have hnext : trace.nextRound.1 < roundCount := by omega
      refine ⟨AdaptiveResamplingTrace.append_isNormalized trace hnormalized
        (contextAt queryIndex trace) batch (labelAt queryIndex trace batch),
        AdaptiveResamplingTrace.append_recordsArePresent trace hpresent
          (contextAt queryIndex trace) batch (labelAt queryIndex trace batch) hnext, ?_, ?_⟩
      · change (trace.append (contextAt queryIndex trace) batch
          (labelAt queryIndex trace batch)).nextRound.1 =
            Nat.min (queryIndex + 1) roundCount
        rw [AdaptiveResamplingTrace.append_nextRound trace (contextAt queryIndex trace) batch
          (labelAt queryIndex trace batch) hnext]
        simp [Nat.min_eq_left (Nat.succ_le_of_lt hindex), hcount]
      · intro hflag
        have hflagParts := Bool.or_eq_false_iff.mp hflag
        have hbad : ¬ bad queryIndex trace batch := of_decide_eq_false hflagParts.2
        exact AdaptiveResamplingTrace.append_recordsAreGood bad trace hnormalized
          (hrecords hflagParts.1) (contextAt queryIndex trace) batch
          (labelAt queryIndex trace batch) hnext (by simpa [hcount] using hbad)
    · have hroundCount : roundCount ≤ queryIndex := Nat.le_of_not_gt hindex
      have hmin : Nat.min queryIndex roundCount = roundCount := Nat.min_eq_right hroundCount
      rw [hmin] at hcount
      have hnotNext : ¬ trace.nextRound.1 < roundCount := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [adaptiveResamplingTraceAdvance, AdaptiveResamplingTrace.append, hnotNext]
          using hnormalized
      · simpa [adaptiveResamplingTraceAdvance, AdaptiveResamplingTrace.append, hnotNext]
          using hpresent
      · simp [adaptiveResamplingTraceAdvance, AdaptiveResamplingTrace.append, hcount,
          Nat.min_eq_right (by omega : roundCount ≤ queryIndex + 1)]
      · intro hflag
        have hflagParts := Bool.or_eq_false_iff.mp hflag
        simpa [adaptiveResamplingTraceAdvance, AdaptiveResamplingTrace.append, hnotNext]
          using hrecords hflagParts.1

/-- At the terminal horizon, a no-failure trace contains every round's actual
batch together with the two-sided empirical-mean comparison evaluated at that
round's recovered preceding transcript. -/
theorem adaptiveResamplingTraceLaw_noFailure_records_good
    {Context Sample Label : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Sample] [DecidableEq Sample] [Fintype Label] [DecidableEq Label]
    {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (lawAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → PMF Sample)
    (scoreAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Sample → ℝ)
    (error : ℝ) (terminal : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount × Bool)
    (hterminal : terminal ∈
      (adaptiveResamplingTraceLaw contextAt labelAt lawAt scoreAt error).support)
    (hflag : terminal.2 = false) :
    ∀ round, ∃ context batch label, terminal.1.entry round = some (context, batch, label) ∧
      |resamplingSampleAverage batch (scoreAt round.1 (terminal.1.prefixBefore round)) -
        pmfExp (lawAt round.1 (terminal.1.prefixBefore round))
          (scoreAt round.1 (terminal.1.prefixBefore round))| ≤ error := by
  classical
  unfold adaptiveResamplingTraceLaw at hterminal
  have hinvariant := adaptiveResamplingTrace_support_invariant
    contextAt labelAt (adaptiveResamplingTraceOutcomeLaw lawAt)
    (adaptiveResamplingTraceBad lawAt scoreAt error) roundCount terminal hterminal
  intro round
  have hcount : terminal.1.nextRound.1 = roundCount := by
    simpa using hinvariant.2.2.1
  have hless : round.1 < terminal.1.nextRound.1 := by
    rw [hcount]
    exact round.2
  obtain ⟨context, batch, label, hentry, hgood⟩ :=
    hinvariant.2.2.2 hflag round hless
  refine ⟨context, batch, label, hentry, ?_⟩
  unfold adaptiveResamplingTraceBad at hgood
  exact le_of_lt (lt_of_not_ge hgood)

/-- At the terminal horizon every positive-mass trace has an actual stored
record at every round, independently of whether a concentration test failed. -/
theorem adaptiveResamplingTraceLaw_terminal_recordAt
    {Context Sample Label : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Sample] [DecidableEq Sample] [Fintype Label] [DecidableEq Label]
    {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (lawAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → PMF Sample)
    (scoreAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Sample → ℝ)
    (error : ℝ) (defaultRecord : AdaptiveResamplingRecord Context Sample Label sampleCount)
    (terminal : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount × Bool)
    (hterminal : terminal ∈
      (adaptiveResamplingTraceLaw contextAt labelAt lawAt scoreAt error).support)
    (round : Fin roundCount) :
    ∃ record, terminal.1.entry round = some record ∧
      terminal.1.recordAt defaultRecord round = record := by
  classical
  unfold adaptiveResamplingTraceLaw at hterminal
  have hinvariant := adaptiveResamplingTrace_support_invariant
    contextAt labelAt (adaptiveResamplingTraceOutcomeLaw lawAt)
    (adaptiveResamplingTraceBad lawAt scoreAt error) roundCount terminal hterminal
  have hcount : terminal.1.nextRound.1 = roundCount := by
    simpa using hinvariant.2.2.1
  have hless : round.1 < terminal.1.nextRound.1 := by
    rw [hcount]
    exact round.2
  obtain ⟨record, hentry⟩ := hinvariant.2.1 round hless
  exact ⟨record, hentry,
    AdaptiveResamplingTrace.recordAt_eq_of_entry_eq_some defaultRecord terminal.1 round record hentry⟩

/-- The trace's total record accessor agrees with the actual batch at every
horizon position of a terminal no-failure execution. -/
theorem adaptiveResamplingTraceLaw_noFailure_recordAt_good
    {Context Sample Label : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Sample] [DecidableEq Sample] [Fintype Label] [DecidableEq Label]
    {roundCount sampleCount : ℕ}
    (contextAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → Context)
    (labelAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      (Fin sampleCount → Sample) → Label)
    (lawAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount → PMF Sample)
    (scoreAt : ℕ → AdaptiveResamplingTrace Context Sample Label roundCount sampleCount →
      Sample → ℝ)
    (error : ℝ) (defaultRecord : AdaptiveResamplingRecord Context Sample Label sampleCount)
    (terminal : AdaptiveResamplingTrace Context Sample Label roundCount sampleCount × Bool)
    (hterminal : terminal ∈
      (adaptiveResamplingTraceLaw contextAt labelAt lawAt scoreAt error).support)
    (hflag : terminal.2 = false) (round : Fin roundCount) :
    |resamplingSampleAverage (terminal.1.recordAt defaultRecord round).2.1
        (scoreAt round.1 (terminal.1.prefixBefore round)) -
      pmfExp (lawAt round.1 (terminal.1.prefixBefore round))
        (scoreAt round.1 (terminal.1.prefixBefore round))| ≤ error := by
  obtain ⟨context, batch, label, hentry, hgood⟩ :=
    adaptiveResamplingTraceLaw_noFailure_records_good contextAt labelAt lawAt scoreAt error
      terminal hterminal hflag round
  have hrecord : terminal.1.recordAt defaultRecord round = (context, batch, label) :=
    AdaptiveResamplingTrace.recordAt_eq_of_entry_eq_some defaultRecord terminal.1 round
      (context, batch, label) hentry
  simpa [hrecord] using hgood

end AppliedModelingLib.Learning.Online
