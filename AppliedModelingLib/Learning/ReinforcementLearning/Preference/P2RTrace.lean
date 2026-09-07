import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueryInvariants
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Confidence
import Mathlib.Tactic

/-!
# Finite execution traces for a preference-to-reward interface

The P2R interface memoizes its first label for every trajectory.  This module
turns a chronological list of returned labels into a single deterministic
reward function: previously seen trajectories receive their memoized label,
and unseen trajectories receive the true relative reward.  The construction
is useful whenever an adaptive learner expects a fixed reward function rather
than a stream of locally certified labels.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- Every occurrence of the same trajectory in a returned-label history has
the same label.  Algorithm 1 obtains this invariant from its cache branch. -/
def P2RHistoryConsistent {Trajectory : Type*}
    (history : List (Trajectory × ℝ)) : Prop :=
  ∀ first ∈ history, ∀ second ∈ history,
    first.1 = second.1 → first.2 = second.2

/-- Every label in a finite P2R history is accurate for the true reward
relative to the fixed reference trajectory. -/
def P2RHistoryAccurate {Trajectory : Type*}
    (truth : Trajectory → ℝ) (reference : Trajectory) (tolerance : ℝ)
    (history : List (Trajectory × ℝ)) : Prop :=
  ∀ datum ∈ history,
    |datum.2 - relativeTrajectoryReward truth datum.1 reference| ≤ tolerance

/-- A chronological history certificate that mirrors Algorithm 1: the latest
return is either copied from the preceding cache or is independently proved
accurate, and the preceding history has the same property. -/
def P2RReturnedHistoryValid {Trajectory : Type*}
    (truth : Trajectory → ℝ) (reference : Trajectory) (tolerance : ℝ) :
    List (Trajectory × ℝ) → Prop
  | [] => True
  | datum :: prior =>
      (datum ∈ prior ∨
        |datum.2 - relativeTrajectoryReward truth datum.1 reference| ≤ tolerance) ∧
      P2RReturnedHistoryValid truth reference tolerance prior

/-- Cached returns inherit the accuracy of their original return; fresh
returns use their local P2R query/no-query proof. -/
theorem p2rReturnedHistoryValid_implies_accurate {Trajectory : Type*}
    (truth : Trajectory → ℝ) (reference : Trajectory) (tolerance : ℝ)
    (history : List (Trajectory × ℝ))
    (hvalid : P2RReturnedHistoryValid truth reference tolerance history) :
    P2RHistoryAccurate truth reference tolerance history := by
  induction history with
  | nil => simp [P2RHistoryAccurate]
  | cons datum prior ih =>
      intro selected hselected
      simp only [List.mem_cons] at hselected
      rcases hvalid with ⟨hdatum, hprior⟩
      rcases hselected with hselected | hselected
      · subst selected
        rcases hdatum with hcached | hfresh
        · exact ih hprior _ hcached
        · exact hfresh
      · exact ih hprior selected hselected

/-- The deterministic reward represented by a memoized finite P2R history.
It agrees with the true relative reward away from the observed trajectories. -/
noncomputable def p2rHistoryReward {Trajectory : Type*}
    (truth : Trajectory → ℝ) (reference : Trajectory)
    (history : List (Trajectory × ℝ)) (trajectory : Trajectory) : ℝ := by
  classical
  exact if h : ∃ datum ∈ history, datum.1 = trajectory then (Classical.choose h).2
    else relativeTrajectoryReward truth trajectory reference

/-- Consistency makes the represented reward agree with every stored label,
independently of which existential witness is chosen. -/
theorem p2rHistoryReward_eq_of_mem {Trajectory : Type*}
    (truth : Trajectory → ℝ) (reference : Trajectory)
    (history : List (Trajectory × ℝ))
    (hconsistent : P2RHistoryConsistent history)
    (datum : Trajectory × ℝ) (hdatum : datum ∈ history) :
    p2rHistoryReward truth reference history datum.1 = datum.2 := by
  classical
  have hexists : ∃ stored ∈ history, stored.1 = datum.1 := ⟨datum, hdatum, rfl⟩
  rw [p2rHistoryReward, dif_pos hexists]
  have hselected : (Classical.choose hexists) ∈ history :=
    (Classical.choose_spec hexists).1
  have hselectedTrajectory : (Classical.choose hexists).1 = datum.1 :=
    (Classical.choose_spec hexists).2
  exact hconsistent (Classical.choose hexists) hselected datum hdatum hselectedTrajectory

/-- Accurate, consistent memoized labels extend to a globally defined reward
function uniformly close to the true relative reward. -/
theorem p2rHistoryReward_uniformError {Trajectory : Type*}
    (truth : Trajectory → ℝ) (reference : Trajectory)
    (history : List (Trajectory × ℝ)) (tolerance : ℝ)
    (htolerance : 0 ≤ tolerance)
    (hconsistent : P2RHistoryConsistent history)
    (haccurate : P2RHistoryAccurate truth reference tolerance history) :
    ∀ trajectory,
      |p2rHistoryReward truth reference history trajectory -
        relativeTrajectoryReward truth trajectory reference| ≤ tolerance := by
  classical
  intro trajectory
  by_cases hseen : ∃ datum ∈ history, datum.1 = trajectory
  · obtain ⟨datum, hdatum, htrajectory⟩ := hseen
    subst htrajectory
    rw [p2rHistoryReward_eq_of_mem truth reference history hconsistent datum hdatum]
    exact haccurate datum hdatum
  · simpa [p2rHistoryReward, hseen] using htolerance

/--
On a successful finite adaptive query run, every label appended to the P2R
queried-history projection is accurate for the fixed reference trajectory.
The adaptive state may contain an arbitrary learner/controller history; the
only required execution bridge is the concrete one-step equation saying that
each query appends its current trajectory and estimated label.
-/
theorem adaptiveQueriedHistory_accurate_of_success
    {State Outcome Trajectory : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (queriedHistory : State → List (Trajectory × ℝ))
    (queriedTrajectory : ℕ → State → Trajectory)
    (queriedLabel : ℕ → State → Outcome → ℝ)
    (truth : Trajectory → ℝ) (reference : Trajectory) (tolerance : ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, queriedHistory state = [])
    (hadvance : ∀ queryIndex state outcome,
      queriedHistory (advance queryIndex state outcome) =
        (queriedTrajectory queryIndex state, queriedLabel queryIndex state outcome) ::
          queriedHistory state)
    (queryCount : ℕ) (stateFailure : State × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance
        (fun queryIndex state outcome => tolerance <
          |queriedLabel queryIndex state outcome -
            relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|)
        queryCount).support)
    (hsuccess : stateFailure.2 = false) :
    P2RHistoryAccurate truth reference tolerance (queriedHistory stateFailure.1) := by
  let bad : ℕ → State → Outcome → Prop := fun queryIndex state outcome =>
    tolerance < |queriedLabel queryIndex state outcome -
      relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|
  have hinvariant : ∀ state ∈ initialStateLaw.support,
      (false = false → P2RHistoryAccurate truth reference tolerance (queriedHistory state)) := by
    intro state hstate _ datum hdatum
    rw [hinitial state hstate] at hdatum
    simp at hdatum
  have hadvanceInvariant : ∀ (queryIndex : ℕ) (state : State) (flag : Bool) (outcome : Outcome),
      (flag = false → P2RHistoryAccurate truth reference tolerance (queriedHistory state)) →
      ((flag || decide (bad queryIndex state outcome)) = false →
        P2RHistoryAccurate truth reference tolerance
          (queriedHistory (advance queryIndex state outcome))) := by
    intro queryIndex state flag outcome hinvariant hnext datum hdatum
    have hprevious : flag = false := by
      cases flag <;> simp_all
    have hnotBad : ¬ bad queryIndex state outcome := by
      intro hbad
      simp [hbad] at hnext
    rw [hadvance queryIndex state outcome] at hdatum
    simp only [List.mem_cons] at hdatum
    rcases hdatum with hcurrent | hprior
    · subst datum
      exact le_of_not_gt hnotBad
    · exact hinvariant hprevious _ hprior
  have hsupportInvariant := adaptiveQueryStateLaw_support_invariant
    initialStateLaw outcomeLaw advance bad
    (fun _ state flag => flag = false →
      P2RHistoryAccurate truth reference tolerance (queriedHistory state))
    hinvariant hadvanceInvariant queryCount stateFailure (by
      simpa [bad] using hsupport)
  exact hsupportInvariant hsuccess

/--
An adaptive P2R execution has a valid complete returned-label history on its
simultaneous queried-label success event.  At each call, the returned datum is
either an already cached datum or is locally accurate whenever the newly
queried label is accurate.  The latter alternative covers both a fresh oracle
return and a no-query confidence-set return; callers establish it from their
concrete algorithm branch conditions rather than treating returned-history
validity as an assumption.
-/
theorem adaptiveReturnedHistory_valid_of_success
    {State Outcome Trajectory : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (returnedHistory : State → List (Trajectory × ℝ))
    (returnedDatum : ℕ → State → Outcome → Trajectory × ℝ)
    (queriedTrajectory : ℕ → State → Trajectory)
    (queriedLabel : ℕ → State → Outcome → ℝ)
    (truth : Trajectory → ℝ) (reference : Trajectory)
    (queryTolerance returnedTolerance : ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, returnedHistory state = [])
    (hadvance : ∀ queryIndex state outcome,
      returnedHistory (advance queryIndex state outcome) =
        returnedDatum queryIndex state outcome :: returnedHistory state)
    (hreturned : ∀ queryIndex state outcome,
      returnedDatum queryIndex state outcome ∈ returnedHistory state ∨
        (¬ (queryTolerance < |queriedLabel queryIndex state outcome -
          relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|) →
          |(returnedDatum queryIndex state outcome).2 -
            relativeTrajectoryReward truth (returnedDatum queryIndex state outcome).1
              reference| ≤ returnedTolerance))
    (queryCount : ℕ) (stateFailure : State × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance
        (fun queryIndex state outcome => queryTolerance <
          |queriedLabel queryIndex state outcome -
            relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|)
        queryCount).support)
    (hsuccess : stateFailure.2 = false) :
    P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory stateFailure.1) := by
  let bad : ℕ → State → Outcome → Prop := fun queryIndex state outcome =>
    queryTolerance < |queriedLabel queryIndex state outcome -
      relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|
  have hinvariant : ∀ state ∈ initialStateLaw.support,
      (false = false →
        P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state)) := by
    intro state hstate _
    rw [hinitial state hstate]
    trivial
  have hadvanceInvariant : ∀ queryIndex state flag outcome,
      (flag = false →
        P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state)) →
      ((flag || decide (bad queryIndex state outcome)) = false →
        P2RReturnedHistoryValid truth reference returnedTolerance
          (returnedHistory (advance queryIndex state outcome))) := by
    intro queryIndex state flag outcome hinvariant hnext
    have hprevious : flag = false := by
      cases flag <;> simp_all
    have hnotBad : ¬ bad queryIndex state outcome := by
      intro hbad
      simp [hbad] at hnext
    rw [hadvance queryIndex state outcome]
    constructor
    · rcases hreturned queryIndex state outcome with hcached | hlocal
      · exact Or.inl hcached
      · exact Or.inr (hlocal (by simpa [bad] using hnotBad))
    · exact hinvariant hprevious
  have hsupportInvariant := adaptiveQueryStateLaw_support_invariant
    initialStateLaw outcomeLaw advance bad
    (fun _ state flag => flag = false →
      P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state))
    hinvariant hadvanceInvariant queryCount stateFailure (by
      simpa [bad] using hsupport)
  exact hsupportInvariant hsuccess

/--
The returned-history success invariant with an explicit live state invariant.
Unlike the unconditional convenience theorem above, this form only requires
the concrete P2R confidence/history invariant along a prefix on which no
queried-label failure has occurred.  That is the exact shape of the B.6--B.8
induction: a failed label need not preserve truth membership in the evolving
confidence set.
-/
theorem adaptiveReturnedHistory_valid_of_success_of_stateInvariant
    {State Outcome Trajectory : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (returnedHistory : State → List (Trajectory × ℝ))
    (returnedDatum : ℕ → State → Outcome → Trajectory × ℝ)
    (queriedTrajectory : ℕ → State → Trajectory)
    (queriedLabel : ℕ → State → Outcome → ℝ)
    (truth : Trajectory → ℝ) (reference : Trajectory)
    (queryTolerance returnedTolerance : ℝ)
    (stateGood : State → Prop)
    (hgoodInitial : ∀ state ∈ initialStateLaw.support, stateGood state)
    (hgoodAdvance : ∀ queryIndex state outcome,
      stateGood state →
      ¬ (queryTolerance < |queriedLabel queryIndex state outcome -
        relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|) →
      stateGood (advance queryIndex state outcome))
    (hinitial : ∀ state ∈ initialStateLaw.support, returnedHistory state = [])
    (hadvance : ∀ queryIndex state outcome,
      returnedHistory (advance queryIndex state outcome) =
        returnedDatum queryIndex state outcome :: returnedHistory state)
    (hreturned : ∀ queryIndex state outcome, stateGood state →
      returnedDatum queryIndex state outcome ∈ returnedHistory state ∨
        (¬ (queryTolerance < |queriedLabel queryIndex state outcome -
          relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|) →
          |(returnedDatum queryIndex state outcome).2 -
            relativeTrajectoryReward truth (returnedDatum queryIndex state outcome).1
              reference| ≤ returnedTolerance))
    (queryCount : ℕ) (stateFailure : State × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance
        (fun queryIndex state outcome => queryTolerance <
          |queriedLabel queryIndex state outcome -
            relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|)
        queryCount).support)
    (hsuccess : stateFailure.2 = false) :
    P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory stateFailure.1) := by
  let bad : ℕ → State → Outcome → Prop := fun queryIndex state outcome =>
    queryTolerance < |queriedLabel queryIndex state outcome -
      relativeTrajectoryReward truth (queriedTrajectory queryIndex state) reference|
  have hinvariant : ∀ state ∈ initialStateLaw.support,
      (false = false →
        stateGood state ∧
        P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state)) := by
    intro state hstate _
    refine ⟨hgoodInitial state hstate, ?_⟩
    rw [hinitial state hstate]
    trivial
  have hadvanceInvariant : ∀ queryIndex state flag outcome,
      (flag = false → stateGood state ∧
        P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state)) →
      ((flag || decide (bad queryIndex state outcome)) = false →
        stateGood (advance queryIndex state outcome) ∧
        P2RReturnedHistoryValid truth reference returnedTolerance
          (returnedHistory (advance queryIndex state outcome))) := by
    intro queryIndex state flag outcome hinvariant hnext
    have hprevious : flag = false := by
      cases flag <;> simp_all
    have hnotBad : ¬ bad queryIndex state outcome := by
      intro hbad
      simp [hbad] at hnext
    have hpreviousInvariant := hinvariant hprevious
    refine ⟨hgoodAdvance queryIndex state outcome hpreviousInvariant.1
      (by simpa [bad] using hnotBad), ?_⟩
    rw [hadvance queryIndex state outcome]
    constructor
    · rcases hreturned queryIndex state outcome hpreviousInvariant.1 with hcached | hlocal
      · exact Or.inl hcached
      · exact Or.inr (hlocal (by simpa [bad] using hnotBad))
    · exact hpreviousInvariant.2
  have hsupportInvariant := adaptiveQueryStateLaw_support_invariant
    initialStateLaw outcomeLaw advance bad
    (fun _ state flag => flag = false →
      stateGood state ∧
      P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state))
    hinvariant hadvanceInvariant queryCount stateFailure (by
      simpa [bad] using hsupport)
  exact (hsupportInvariant hsuccess).2

/--
The state-invariant returned-history theorem for an arbitrary monitored query
failure event.  This is the form used by a mixed scheduler: cache and
confidence-only steps may have deterministic outcomes with `bad = False`,
while a fresh comparison batch supplies the only monitored failure event.
-/
theorem adaptiveReturnedHistory_valid_of_success_of_stateInvariant_of_bad
    {State Outcome Trajectory : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (returnedHistory : State → List (Trajectory × ℝ))
    (returnedDatum : ℕ → State → Outcome → Trajectory × ℝ)
    (truth : Trajectory → ℝ) (reference : Trajectory)
    (returnedTolerance : ℝ)
    (stateGood : State → Prop)
    (hgoodInitial : ∀ state ∈ initialStateLaw.support, stateGood state)
    (hgoodAdvance : ∀ queryIndex state outcome,
      stateGood state →
      outcome ∈ (outcomeLaw queryIndex state).support →
      ¬ bad queryIndex state outcome →
      stateGood (advance queryIndex state outcome))
    (hinitial : ∀ state ∈ initialStateLaw.support, returnedHistory state = [])
    (hadvance : ∀ queryIndex state outcome,
      returnedHistory (advance queryIndex state outcome) =
        returnedDatum queryIndex state outcome :: returnedHistory state)
    (hreturned : ∀ queryIndex state outcome, stateGood state →
      outcome ∈ (outcomeLaw queryIndex state).support →
      returnedDatum queryIndex state outcome ∈ returnedHistory state ∨
        (¬ bad queryIndex state outcome →
          |(returnedDatum queryIndex state outcome).2 -
            relativeTrajectoryReward truth (returnedDatum queryIndex state outcome).1
              reference| ≤ returnedTolerance))
    (queryCount : ℕ) (stateFailure : State × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support)
    (hsuccess : stateFailure.2 = false) :
    P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory stateFailure.1) := by
  have hinvariant : ∀ state ∈ initialStateLaw.support,
      (false = false →
        stateGood state ∧
        P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state)) := by
    intro state hstate _
    refine ⟨hgoodInitial state hstate, ?_⟩
    rw [hinitial state hstate]
    trivial
  have hadvanceInvariant : ∀ queryIndex state flag outcome,
      (flag = false → stateGood state ∧
        P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state)) →
      outcome ∈ (outcomeLaw queryIndex state).support →
      ((flag || decide (bad queryIndex state outcome)) = false →
        stateGood (advance queryIndex state outcome) ∧
        P2RReturnedHistoryValid truth reference returnedTolerance
          (returnedHistory (advance queryIndex state outcome))) := by
    intro queryIndex state flag outcome hinvariant houtcome hnext
    have hprevious : flag = false := by
      cases flag <;> simp_all
    have hnotBad : ¬ bad queryIndex state outcome := by
      intro hbad
      simp [hbad] at hnext
    have hpreviousInvariant := hinvariant hprevious
    refine ⟨hgoodAdvance queryIndex state outcome hpreviousInvariant.1 houtcome hnotBad, ?_⟩
    rw [hadvance queryIndex state outcome]
    constructor
    · rcases hreturned queryIndex state outcome hpreviousInvariant.1 houtcome with hcached | hlocal
      · exact Or.inl hcached
      · exact Or.inr (hlocal hnotBad)
    · exact hpreviousInvariant.2
  have hsupportInvariant := adaptiveQueryStateLaw_support_invariant_of_outcomeSupport
    initialStateLaw outcomeLaw advance bad
    (fun _ state flag => flag = false →
      stateGood state ∧
      P2RReturnedHistoryValid truth reference returnedTolerance (returnedHistory state))
    hinvariant hadvanceInvariant queryCount stateFailure hsupport
  exact (hsupportInvariant hsuccess).2

/--
The cache invariant of a finite P2R execution.  Whenever a newly prepended
returned datum has a trajectory already present in the history, it has that
stored label.  Thus every positive-mass execution state has a consistent
memoized returned-label history, independently of whether a concentration
failure has occurred.
-/
theorem adaptiveReturnedHistory_consistent_of_support
    {State Outcome Trajectory : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (returnedHistory : State → List (Trajectory × ℝ))
    (returnedDatum : ℕ → State → Outcome → Trajectory × ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, returnedHistory state = [])
    (hadvance : ∀ queryIndex state outcome,
      returnedHistory (advance queryIndex state outcome) =
        returnedDatum queryIndex state outcome :: returnedHistory state)
    (hcache : ∀ queryIndex state outcome datum,
      datum ∈ returnedHistory state →
      datum.1 = (returnedDatum queryIndex state outcome).1 →
      datum.2 = (returnedDatum queryIndex state outcome).2)
    (queryCount : ℕ) (stateFailure : State × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support) :
    P2RHistoryConsistent (returnedHistory stateFailure.1) := by
  have hinvariant : ∀ state ∈ initialStateLaw.support,
      P2RHistoryConsistent (returnedHistory state) := by
    intro state hstate
    rw [hinitial state hstate]
    simp [P2RHistoryConsistent]
  have hadvanceInvariant : ∀ (queryIndex : ℕ) (state : State) (flag : Bool) (outcome : Outcome),
      P2RHistoryConsistent (returnedHistory state) →
      P2RHistoryConsistent (returnedHistory (advance queryIndex state outcome)) := by
    intro queryIndex state _ outcome hprevious
    rw [hadvance queryIndex state outcome]
    intro first hfirst second hsecond hsame
    simp only [List.mem_cons] at hfirst hsecond
    rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
    · subst first
      subst second
      rfl
    · subst first
      exact (hcache queryIndex state outcome second hsecond hsame.symm).symm
    · subst second
      exact hcache queryIndex state outcome first hfirst hsame
    · exact hprevious first hfirst second hsecond hsame
  exact adaptiveQueryStateLaw_support_invariant
    initialStateLaw outcomeLaw advance bad
    (fun _ state _ => P2RHistoryConsistent (returnedHistory state))
    hinvariant hadvanceInvariant queryCount stateFailure hsupport

/--
The cache-consistency invariant in the exact Algorithm-1 form.  A returned
datum is either copied from the existing history, or its trajectory is fresh
relative to that history.  This weaker, operational premise is sufficient to
preserve unique labels because a copied datum inherits consistency from the
prior history.
-/
theorem adaptiveReturnedHistory_consistent_of_cachedOrFresh_support
    {State Outcome Trajectory : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (returnedHistory : State → List (Trajectory × ℝ))
    (returnedDatum : ℕ → State → Outcome → Trajectory × ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, returnedHistory state = [])
    (hadvance : ∀ queryIndex state outcome,
      returnedHistory (advance queryIndex state outcome) =
        returnedDatum queryIndex state outcome :: returnedHistory state)
    (hcacheOrFresh : ∀ queryIndex state outcome,
      returnedDatum queryIndex state outcome ∈ returnedHistory state ∨
        ∀ datum ∈ returnedHistory state,
          datum.1 ≠ (returnedDatum queryIndex state outcome).1)
    (queryCount : ℕ) (stateFailure : State × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support) :
    P2RHistoryConsistent (returnedHistory stateFailure.1) := by
  have hinvariant : ∀ state ∈ initialStateLaw.support,
      P2RHistoryConsistent (returnedHistory state) := by
    intro state hstate
    rw [hinitial state hstate]
    simp [P2RHistoryConsistent]
  have hadvanceInvariant : ∀ (queryIndex : ℕ) (state : State) (flag : Bool) (outcome : Outcome),
      P2RHistoryConsistent (returnedHistory state) →
      P2RHistoryConsistent (returnedHistory (advance queryIndex state outcome)) := by
    intro queryIndex state _ outcome hprevious
    rw [hadvance queryIndex state outcome]
    intro first hfirst second hsecond hsame
    simp only [List.mem_cons] at hfirst hsecond
    rcases hcacheOrFresh queryIndex state outcome with hcached | hfresh
    · rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
      · subst first
        subst second
        rfl
      · subst first
        exact hprevious (returnedDatum queryIndex state outcome) hcached second hsecond hsame
      · subst second
        exact (hprevious (returnedDatum queryIndex state outcome) hcached first hfirst
          hsame.symm).symm
      · exact hprevious first hfirst second hsecond hsame
    · rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
      · subst first
        subst second
        rfl
      · subst first
        exact False.elim (hfresh second hsecond hsame.symm)
      · subst second
        exact False.elim (hfresh first hfirst hsame)
      · exact hprevious first hfirst second hsecond hsame
  exact adaptiveQueryStateLaw_support_invariant
    initialStateLaw outcomeLaw advance bad
    (fun _ state _ => P2RHistoryConsistent (returnedHistory state))
    hinvariant hadvanceInvariant queryCount stateFailure hsupport

end PreferenceRL

end AppliedModelingLib
