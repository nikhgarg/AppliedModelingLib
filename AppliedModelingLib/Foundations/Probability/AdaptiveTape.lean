import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# Finite adaptive consumption of independent tapes

An adaptive algorithm can choose its next coordinate from its complete past
without compromising freshness, provided it consumes a pre-sampled independent
tape at the next unused position of that coordinate.  This module defines that
deterministic consumption semantics.  Probability claims are intentionally
separate: a caller supplies a product law for the tape table.
-/

namespace AppliedModelingLib

/-- A list predicate count is the corresponding finite sum over its literal
positions.  Keeping positions, rather than values, is essential because an
adaptive transition trace may revisit the same successor state. -/
theorem list_countP_eq_sum_get
    {α : Type*} (predicate : α → Bool) (events : List α) :
    events.countP predicate =
      ∑ index : Fin events.length, if predicate (events.get index) then 1 else 0 := by
  induction events with
  | nil => simp
  | cons event events ih =>
      change List.countP predicate (event :: events) =
        ∑ index : Fin (events.length + 1),
          if predicate ((event :: events).get index) then 1 else 0
      rw [List.countP_cons, Fin.sum_univ_succ]
      simp only [List.get_cons_zero]
      have htail :
          (∑ index : Fin events.length,
            if predicate ((event :: events).get index.succ) then 1 else 0) =
            ∑ index : Fin events.length, if predicate (events.get index) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        simp
      rw [htail, ← ih]
      exact Nat.add_comm _ _

/-- A predictable coordinate selector sees only prior coordinate/data events. -/
abbrev AdaptiveTapeScheduler (Coordinate Data : Type*) :=
  List (Coordinate × Data) → Coordinate

/-- The number of entries already consumed from one coordinate's tape. -/
def adaptiveTapeVisitCount {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) : ℕ :=
  (events.filter fun event => event.1 = coordinate).length

/-- A coordinate's adaptive visit count is the cardinality of its literal
event-position filter.  The result retains repeated data values because the
finite set consists of positions, not events themselves. -/
theorem adaptiveTapeVisitCount_eq_card_eventIndices
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) :
    adaptiveTapeVisitCount events coordinate =
      (Finset.univ.filter fun index : Fin events.length =>
        (events.get index).1 = coordinate).card := by
  let predicate : Coordinate × Data → Bool := fun event => decide (event.1 = coordinate)
  change (events.filter predicate).length = _
  rw [← List.countP_eq_length_filter, list_countP_eq_sum_get]
  rw [Finset.card_filter]
  simp [predicate]

/-- The real-valued form of a coordinate visit count is its literal sum of
zero-one coordinate indicators over event positions. -/
theorem adaptiveTapeVisitCount_cast_eq_sum_indicators
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) :
    (adaptiveTapeVisitCount events coordinate : ℝ) =
      ∑ index : Fin events.length,
        if (events.get index).1 = coordinate then (1 : ℝ) else 0 := by
  rw [adaptiveTapeVisitCount_eq_card_eventIndices]
  simp [Finset.sum_boole]

/-- A coordinate's consumed-entry count never exceeds the total event count. -/
theorem adaptiveTapeVisitCount_le_length
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) :
    adaptiveTapeVisitCount events coordinate ≤ events.length := by
  unfold adaptiveTapeVisitCount
  let predicate : Coordinate × Data → Bool := fun event => decide (event.1 = coordinate)
  change (events.filter predicate).length ≤ events.length
  calc
    (events.filter predicate).length ≤
        (events.filter predicate).length + (events.filter (!predicate ·)).length :=
      Nat.le_add_right _ _
    _ = events.length := (List.length_eq_length_filter_add predicate).symm

/-- A completed finite adaptive tape run, retaining its exact number of events. -/
structure AdaptiveTapeRun (Coordinate Data : Type*) (rounds : ℕ) where
  events : List (Coordinate × Data)
  length_eq_rounds : events.length = rounds

/--
Run an adaptive scheduler for a bounded number of rounds.  At each round the
scheduler chooses a coordinate from previous events, then consumes the next
unused entry of that coordinate's tape.
-/
def adaptiveTapeRun
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data) :
    ∀ (rounds : ℕ), rounds ≤ visitBudget → AdaptiveTapeRun Coordinate Data rounds
  | 0, _ => ⟨[], rfl⟩
  | rounds + 1, hrounds =>
      let previous := adaptiveTapeRun tape scheduler rounds (Nat.le_of_succ_le hrounds)
      let coordinate := scheduler previous.events
      let consumed := adaptiveTapeVisitCount previous.events coordinate
      have hconsumed : consumed < visitBudget := by
        calc
          consumed ≤ previous.events.length :=
            adaptiveTapeVisitCount_le_length previous.events coordinate
          _ = rounds := previous.length_eq_rounds
          _ < rounds + 1 := Nat.lt_succ_self rounds
          _ ≤ visitBudget := hrounds
      ⟨previous.events ++ [(coordinate, tape coordinate ⟨consumed, hconsumed⟩)], by
        simp [previous.length_eq_rounds]⟩

/-- The event list produced by a bounded adaptive tape run. -/
def adaptiveTapeEvents
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds ≤ visitBudget) : List (Coordinate × Data) :=
  (adaptiveTapeRun tape scheduler rounds hrounds).events

/-- The generated event list has exactly one event per executed round. -/
theorem adaptiveTapeEvents_length
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds ≤ visitBudget) :
    (adaptiveTapeEvents tape scheduler rounds hrounds).length = rounds :=
  (adaptiveTapeRun tape scheduler rounds hrounds).length_eq_rounds

/-- One-step unfolding equation for adaptive tape consumption. -/
theorem adaptiveTapeEvents_succ
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds + 1 ≤ visitBudget) :
    adaptiveTapeEvents tape scheduler (rounds + 1) hrounds =
      let previous := adaptiveTapeEvents tape scheduler rounds (Nat.le_of_succ_le hrounds)
      let coordinate := scheduler previous
      let consumed := adaptiveTapeVisitCount previous coordinate
      previous ++ [(coordinate, tape coordinate
        ⟨consumed, by
          calc
            consumed ≤ previous.length := adaptiveTapeVisitCount_le_length previous coordinate
            _ = rounds := adaptiveTapeEvents_length tape scheduler rounds
              (Nat.le_of_succ_le hrounds)
            _ < rounds + 1 := Nat.lt_succ_self rounds
            _ ≤ visitBudget := hrounds⟩)] := by
  rfl

/-- Running an adaptive tape for more rounds preserves every earlier event
prefix. The scheduler is evaluated on the same preceding events in both
runs, so this is a deterministic execution identity rather than a
probabilistic statement. -/
theorem adaptiveTapeEvents_take
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data) :
    ∀ (prefixLength rounds : ℕ) (hprefix : prefixLength ≤ rounds) (hrounds : rounds ≤ visitBudget),
      (adaptiveTapeEvents tape scheduler rounds hrounds).take prefixLength =
        adaptiveTapeEvents tape scheduler prefixLength (hprefix.trans hrounds)
  | prefixLength, 0, hprefix, hrounds => by
      have hzero : prefixLength = 0 := by omega
      subst prefixLength
      simp [adaptiveTapeEvents, adaptiveTapeRun]
  | 0, rounds + 1, _, _ => by
      simp [adaptiveTapeEvents, adaptiveTapeRun]
  | prefixLength + 1, rounds + 1, hprefix, hrounds => by
      have hprefix_le : prefixLength ≤ rounds := by omega
      by_cases heq : prefixLength = rounds
      · subst prefixLength
        rw [List.take_of_length_le (by
          rw [adaptiveTapeEvents_length])]
      · have hprefix_lt : prefixLength < rounds := lt_of_le_of_ne hprefix_le heq
        rw [adaptiveTapeEvents_succ tape scheduler rounds hrounds]
        rw [List.take_append_of_le_length]
        · exact adaptiveTapeEvents_take tape scheduler (prefixLength + 1) rounds
            (by omega) (Nat.le_of_succ_le hrounds)
        · rw [adaptiveTapeEvents_length]
          omega

/-- The observed data subsequence for a fixed coordinate. -/
def adaptiveTapeObservations
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) : List Data :=
  (events.filter fun event => event.1 = coordinate).map Prod.snd

/-- The initial segment of one coordinate's pre-sampled tape. -/
def adaptiveTapePrefix
    {Coordinate Data : Type*} {visitBudget : ℕ}
    (tape : Coordinate → Fin visitBudget → Data)
    (coordinate : Coordinate) (count : ℕ) (hcount : count ≤ visitBudget) : List Data :=
  List.ofFn fun visit => tape coordinate (Fin.castLE hcount visit)

/-- Observation extraction has the same length as the coordinate's consumed count. -/
theorem adaptiveTapeObservations_length
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) :
    (adaptiveTapeObservations events coordinate).length =
      adaptiveTapeVisitCount events coordinate := by
  simp [adaptiveTapeObservations, adaptiveTapeVisitCount]

/-- Summing a statistic over one coordinate's ordered observation list is the
same as summing it over the corresponding literal event positions.  Event
positions, rather than data values, are essential here because a tape may
produce the same data value at several distinct visits. -/
theorem adaptiveTapeObservations_map_sum_eq_eventCoordinateSum
    {Coordinate Data M : Type*} [DecidableEq Coordinate] [AddCommMonoid M]
    (events : List (Coordinate × Data)) (coordinate : Coordinate) (statistic : Data → M) :
    ((adaptiveTapeObservations events coordinate).map statistic).sum =
      ∑ index ∈ Finset.univ.filter fun index : Fin events.length =>
          (events.get index).1 = coordinate,
        statistic (events.get index).2 := by
  induction events with
  | nil => simp [adaptiveTapeObservations]
  | cons event events ih =>
      rw [Finset.sum_filter]
      change (List.map statistic
          (adaptiveTapeObservations (event :: events) coordinate)).sum =
        ∑ index : Fin (events.length + 1),
          if ((event :: events).get index).1 = coordinate then
            statistic ((event :: events).get index).2
          else 0
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero]
      have ih' :
          (List.map statistic (adaptiveTapeObservations events coordinate)).sum =
            ∑ index : Fin events.length,
              if (events.get index).1 = coordinate then statistic (events.get index).2 else 0 := by
        simpa only [Finset.sum_filter] using ih
      have htail :
          (List.map (statistic ∘ Prod.snd)
            (List.filter (fun event => event.1 = coordinate) events)).sum =
            ∑ index : Fin events.length,
              if (events.get index).1 = coordinate then statistic (events.get index).2 else 0 := by
        simpa [adaptiveTapeObservations, List.map_map, Function.comp_def] using ih'
      by_cases hcoordinate : event.1 = coordinate
      · simp [adaptiveTapeObservations, hcoordinate, htail]
      · simp [adaptiveTapeObservations, hcoordinate, htail]

/-- Appending one event updates exactly the selected coordinate's visit count. -/
theorem adaptiveTapeVisitCount_append_singleton
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (selected coordinate : Coordinate) (data : Data) :
    adaptiveTapeVisitCount (events ++ [(selected, data)]) coordinate =
      if selected = coordinate then adaptiveTapeVisitCount events coordinate + 1
      else adaptiveTapeVisitCount events coordinate := by
  by_cases hselected : selected = coordinate <;>
    simp [adaptiveTapeVisitCount, List.filter_append, hselected]

/-- Appending one event updates exactly the selected coordinate's observations. -/
theorem adaptiveTapeObservations_append_singleton
    {Coordinate Data : Type*} [DecidableEq Coordinate]
    (events : List (Coordinate × Data)) (selected coordinate : Coordinate) (data : Data) :
    adaptiveTapeObservations (events ++ [(selected, data)]) coordinate =
      if selected = coordinate then adaptiveTapeObservations events coordinate ++ [data]
      else adaptiveTapeObservations events coordinate := by
  by_cases hselected : selected = coordinate <;>
    simp [adaptiveTapeObservations, List.filter_append, hselected]

/-- Extending a tape prefix reads precisely the next indexed entry. -/
theorem adaptiveTapePrefix_succ
    {Coordinate Data : Type*} {visitBudget count : ℕ}
    (tape : Coordinate → Fin visitBudget → Data)
    (coordinate : Coordinate) (hcount : count + 1 ≤ visitBudget) :
    adaptiveTapePrefix tape coordinate (count + 1) hcount =
      adaptiveTapePrefix tape coordinate count (Nat.le_of_succ_le hcount) ++
        [tape coordinate ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) hcount⟩] := by
  simp only [adaptiveTapePrefix]
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  congr 1

/-- Tape prefixes are insensitive to the proof used for their common length bound. -/
theorem adaptiveTapePrefix_congr
    {Coordinate Data : Type*} {visitBudget count count' : ℕ}
    (tape : Coordinate → Fin visitBudget → Data)
    (coordinate : Coordinate) (hcountEq : count = count')
    (hcount : count ≤ visitBudget) (hcount' : count' ≤ visitBudget) :
    adaptiveTapePrefix tape coordinate count hcount =
      adaptiveTapePrefix tape coordinate count' hcount' := by
  subst count'
  rfl

/-- Every coordinate's completed consumption is bounded by the tape length. -/
theorem adaptiveTapeVisitCount_adaptiveTapeEvents_le
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds ≤ visitBudget) (coordinate : Coordinate) :
    adaptiveTapeVisitCount (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate ≤
      visitBudget := by
  calc
    adaptiveTapeVisitCount (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate ≤
        (adaptiveTapeEvents tape scheduler rounds hrounds).length :=
      adaptiveTapeVisitCount_le_length _ _
    _ = rounds := adaptiveTapeEvents_length tape scheduler rounds hrounds
    _ ≤ visitBudget := hrounds

/-- The consumed prefix of a coordinate's tape after a completed adaptive run. -/
def adaptiveTapeConsumedPrefix
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds ≤ visitBudget) (coordinate : Coordinate) : List Data :=
  adaptiveTapePrefix tape coordinate
    (adaptiveTapeVisitCount (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate)
    (adaptiveTapeVisitCount_adaptiveTapeEvents_le tape scheduler rounds hrounds coordinate)

/--
Adaptive selection does not permute or skip a coordinate's independent tape:
the observations at every coordinate are exactly its consumed tape prefix.
-/
theorem adaptiveTapeObservations_adaptiveTapeEvents_eq_consumedPrefix
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds ≤ visitBudget) (coordinate : Coordinate) :
    adaptiveTapeObservations (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate =
      adaptiveTapeConsumedPrefix tape scheduler rounds hrounds coordinate := by
  induction rounds generalizing coordinate with
  | zero =>
      simp [adaptiveTapeEvents, adaptiveTapeRun, adaptiveTapeConsumedPrefix,
        adaptiveTapePrefix, adaptiveTapeObservations, adaptiveTapeVisitCount]
  | succ rounds ih =>
      let previous := adaptiveTapeEvents tape scheduler rounds (Nat.le_of_succ_le hrounds)
      let selected := scheduler previous
      let consumed := adaptiveTapeVisitCount previous selected
      rw [adaptiveTapeEvents_succ tape scheduler rounds hrounds]
      change adaptiveTapeObservations
          (previous ++ [(selected, tape selected ⟨consumed, _⟩)]) coordinate =
        adaptiveTapeConsumedPrefix tape scheduler (rounds + 1) hrounds coordinate
      by_cases hselected : selected = coordinate
      · subst selected
        have hprevious : rounds ≤ visitBudget := Nat.le_of_succ_le hrounds
        have hcount : adaptiveTapeVisitCount previous coordinate + 1 ≤ visitBudget := by
          calc
            adaptiveTapeVisitCount previous coordinate + 1 ≤ previous.length + 1 :=
              Nat.add_le_add_right
                (adaptiveTapeVisitCount_le_length previous coordinate) 1
            _ = rounds + 1 := by
              simp [previous, adaptiveTapeEvents_length tape scheduler rounds hprevious]
            _ ≤ visitBudget := hrounds
        have hprefix :
            adaptiveTapeConsumedPrefix tape scheduler (rounds + 1) hrounds coordinate =
              adaptiveTapePrefix tape coordinate
                (adaptiveTapeVisitCount previous coordinate + 1) hcount := by
          have hcountEq :
              adaptiveTapeVisitCount
                  (adaptiveTapeEvents tape scheduler (rounds + 1) hrounds) coordinate =
                adaptiveTapeVisitCount previous coordinate + 1 := by
            have hpreviousEq :
                adaptiveTapeEvents tape scheduler rounds (Nat.le_of_succ_le hrounds) = previous := rfl
            rw [adaptiveTapeEvents_succ tape scheduler rounds hrounds]
            simp [adaptiveTapeVisitCount_append_singleton, hselected, hpreviousEq]
          unfold adaptiveTapeConsumedPrefix
          exact adaptiveTapePrefix_congr tape coordinate hcountEq _ hcount
        rw [adaptiveTapeObservations_append_singleton]
        simp only [if_pos hselected]
        rw [hprefix, adaptiveTapePrefix_succ]
        have ih' := ih hprevious coordinate
        change adaptiveTapeObservations previous coordinate =
          adaptiveTapeConsumedPrefix tape scheduler rounds hprevious coordinate at ih'
        rw [ih']
        have hpastCount :
            adaptiveTapeVisitCount (adaptiveTapeEvents tape scheduler rounds hprevious) coordinate =
              adaptiveTapeVisitCount previous coordinate := by
          rfl
        have hpast :
            adaptiveTapeConsumedPrefix tape scheduler rounds hprevious coordinate =
              adaptiveTapePrefix tape coordinate (adaptiveTapeVisitCount previous coordinate)
                (Nat.le_of_succ_le hcount) := by
          unfold adaptiveTapeConsumedPrefix
          exact adaptiveTapePrefix_congr tape coordinate hpastCount _ _
        have hconsumed : consumed = adaptiveTapeVisitCount previous coordinate := by
          dsimp [consumed]
          rw [hselected]
        have hdata :
            tape (scheduler previous) ⟨consumed, by
              calc
                consumed ≤ previous.length := adaptiveTapeVisitCount_le_length previous _
                _ = rounds := adaptiveTapeEvents_length tape scheduler rounds hprevious
                _ < rounds + 1 := Nat.lt_succ_self rounds
                _ ≤ visitBudget := hrounds⟩ =
              tape coordinate ⟨adaptiveTapeVisitCount previous coordinate,
                Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hcount⟩ := by
          simp [hselected, hconsumed]
        rw [hpast, hdata]
      · have hprevious : rounds ≤ visitBudget := Nat.le_of_succ_le hrounds
        have hcount : adaptiveTapeVisitCount previous coordinate ≤ visitBudget :=
          adaptiveTapeVisitCount_adaptiveTapeEvents_le tape scheduler rounds hprevious coordinate
        have hprefix :
            adaptiveTapeConsumedPrefix tape scheduler (rounds + 1) hrounds coordinate =
              adaptiveTapePrefix tape coordinate
                (adaptiveTapeVisitCount previous coordinate) hcount := by
          have hcountEq :
              adaptiveTapeVisitCount
                  (adaptiveTapeEvents tape scheduler (rounds + 1) hrounds) coordinate =
                adaptiveTapeVisitCount previous coordinate := by
            have hpreviousEq :
                adaptiveTapeEvents tape scheduler rounds (Nat.le_of_succ_le hrounds) = previous := rfl
            have hselectedPrev : scheduler previous ≠ coordinate := by
              simpa [selected] using hselected
            rw [adaptiveTapeEvents_succ tape scheduler rounds hrounds]
            simp [adaptiveTapeVisitCount_append_singleton, hselectedPrev, hpreviousEq]
          unfold adaptiveTapeConsumedPrefix
          exact adaptiveTapePrefix_congr tape coordinate hcountEq _ hcount
        rw [adaptiveTapeObservations_append_singleton]
        simp only [if_neg hselected]
        rw [hprefix]
        have ih' := ih hprevious coordinate
        change adaptiveTapeObservations previous coordinate =
          adaptiveTapeConsumedPrefix tape scheduler rounds hprevious coordinate at ih'
        rw [ih']
        unfold adaptiveTapeConsumedPrefix
        apply adaptiveTapePrefix_congr tape coordinate
        rfl

/--
Any failure predicate triggered by adaptively observed data already occurs on
one deterministic-length prefix of the underlying coordinate tape.  This is
the pathwise reduction that permits a finite union bound over all possible
visit counts; it makes no independence claim about the selected count.
-/
theorem adaptiveTapeObservation_bad_implies_exists_prefix_bad
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data)
    (rounds : ℕ) (hrounds : rounds ≤ visitBudget) (coordinate : Coordinate)
    (bad : List Data → Prop)
    (hbad : bad (adaptiveTapeObservations
      (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate)) :
    ∃ count : ℕ, ∃ hcount : count ≤ visitBudget,
      bad (adaptiveTapePrefix tape coordinate count hcount) := by
  let count := adaptiveTapeVisitCount
    (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate
  let hcount := adaptiveTapeVisitCount_adaptiveTapeEvents_le
    tape scheduler rounds hrounds coordinate
  refine ⟨count, hcount, ?_⟩
  rw [adaptiveTapeObservations_adaptiveTapeEvents_eq_consumedPrefix
    tape scheduler rounds hrounds coordinate] at hbad
  exact hbad

end AppliedModelingLib
