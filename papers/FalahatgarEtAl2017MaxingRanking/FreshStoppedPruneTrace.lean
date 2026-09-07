import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneRounds
import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneRetention

/-!
# Fresh stopped Prune traces

The finite stopped execution records the active set immediately before each
scheduled round.  This trace makes Algorithm 2's exact comparison count part
of the same finite-PMF success event as its cardinality guarantee.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The current active set and finite pre-round active-set trace of Algorithm 2. -/
abbrev stoppedPruneTraceState (Arm : Type*) (roundCount : ℕ) :=
  Finset Arm × (Fin roundCount → Finset Arm)

/-- The trace initially contains no completed-round active sets. -/
noncomputable def initialStoppedPruneTraceState {Arm : Type*} [DecidableEq Arm]
    (roundCount : ℕ) (initial : Finset Arm) : stoppedPruneTraceState Arm roundCount :=
  (initial, fun _ => ∅)

/-- One stopped-Prune transition together with its pre-round active-set record. -/
noncomputable def stoppedPruneTraceAdvance
    {Arm Outcome : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) :
    AdaptiveStateUpdate (stoppedPruneTraceState Arm roundCount) Outcome :=
  fun round state outcome =>
    let next := stoppedPruneAdvance cutoff decision round state.1 outcome
    if hround : round < roundCount then
      (next, Function.update state.2 ⟨round, hround⟩ state.1)
    else (next, state.2)

/-- The literal number of comparisons charged by a finite stopped-Prune trace. -/
noncomputable def stoppedPruneTraceComparisonCount {Arm : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (lower upper delta : ℝ)
    (trace : Fin roundCount → Finset Arm) : ℕ :=
  ∑ round : Fin roundCount,
    if (trace round).card ≤ 2 * cutoff then 0 else
      (trace round).card *
        fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val)

/-- The adaptive PMF law of stopped Prune together with its finite active-set trace. -/
noncomputable def freshStoppedPruneTraceStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    PMF (stoppedPruneTraceState Arm roundCount × Bool) := by
  classical
  exact adaptiveQueryStateLaw
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1)
    (stoppedPruneTraceAdvance roundCount cutoff decision)
    (fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round state.1 outcome)).card : ℝ))
    roundCount

/--
The actual stopped-Prune trace law, without the auxiliary contraction-failure
monitor used by the probability proof.
-/
noncomputable def freshStoppedPruneTraceLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (cutoff : ℕ) (initial : Finset Arm)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    PMF (stoppedPruneTraceState Arm roundCount) :=
  adaptiveQueryActiveLaw
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1)
    (stoppedPruneTraceAdvance roundCount cutoff decision)
    roundCount

/-- Erasing the proof-only monitor recovers the actual stopped trace law. -/
theorem freshStoppedPruneTraceStateLaw_map_traceLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
      decision roundCount).map Prod.fst =
      freshStoppedPruneTraceLaw cutoff initial outcomeLaw decision roundCount := by
  classical
  unfold freshStoppedPruneTraceStateLaw freshStoppedPruneTraceLaw
  exact adaptiveQueryStateLaw_map_fst_eq_activeLaw
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1)
    (stoppedPruneTraceAdvance roundCount cutoff decision)
    (fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round state.1 outcome)).card : ℝ))
    roundCount

/-- The active component of a trace transition is exactly the stopped-Prune transition. -/
theorem stoppedPruneTraceAdvance_fst
    {Arm Outcome : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (round : ℕ) (state : stoppedPruneTraceState Arm roundCount) (outcome : Outcome) :
    (stoppedPruneTraceAdvance roundCount cutoff decision round state outcome).1 =
      stoppedPruneAdvance cutoff decision round state.1 outcome := by
  unfold stoppedPruneTraceAdvance
  split <;> rfl

/--
Erasing the trace and contraction flag recovers the same stopped-Prune active
set PMF.  Thus a resource trace can be coupled to the candidate-set execution
used by the later OPT-Maximize phases without an independence assumption.
-/
theorem freshStoppedPruneTraceStateLaw_map_activeLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
      decision roundCount).map (fun stateFailure => stateFailure.1.1) =
      freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount := by
  classical
  let traceInitial : PMF (stoppedPruneTraceState Arm roundCount) :=
    PMF.pure (initialStoppedPruneTraceState roundCount initial)
  let traceOutcomeLaw : AdaptiveOutcomeKernel (stoppedPruneTraceState Arm roundCount) Outcome :=
    fun round state => outcomeLaw round state.1
  let traceAdvance : AdaptiveStateUpdate (stoppedPruneTraceState Arm roundCount) Outcome :=
    stoppedPruneTraceAdvance roundCount cutoff decision
  let traceBad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round state.1 outcome)).card : ℝ)
  have hflag :
      (adaptiveQueryStateLaw traceInitial traceOutcomeLaw traceAdvance traceBad roundCount).map
        Prod.fst =
      adaptiveQueryActiveLaw traceInitial traceOutcomeLaw traceAdvance roundCount := by
    exact adaptiveQueryStateLaw_map_fst_eq_activeLaw traceInitial traceOutcomeLaw traceAdvance
      traceBad roundCount
  have hactive : ∀ queryCount,
      (adaptiveQueryActiveLaw traceInitial traceOutcomeLaw traceAdvance queryCount).map Prod.fst =
        adaptiveQueryActiveLaw (PMF.pure initial) outcomeLaw
          (stoppedPruneAdvance cutoff decision) queryCount := by
    intro queryCount
    induction queryCount with
    | zero =>
        change (PMF.pure (initialStoppedPruneTraceState roundCount initial)).map Prod.fst =
          PMF.pure initial
        rw [PMF.pure_map]
        rfl
    | succ queryCount ih =>
        rw [adaptiveQueryActiveLaw, adaptiveQueryActiveLaw, PMF.map_bind]
        simp_rw [PMF.map_comp]
        dsimp only [traceOutcomeLaw, traceAdvance]
        let step : Finset Arm → PMF (Finset Arm) := fun active =>
          (outcomeLaw queryCount active).map fun outcome =>
            stoppedPruneAdvance cutoff decision queryCount active outcome
        have hkernel : (fun state : stoppedPruneTraceState Arm roundCount =>
            (outcomeLaw queryCount state.1).map
              (Prod.fst ∘ fun outcome =>
                stoppedPruneTraceAdvance roundCount cutoff decision queryCount state outcome)) =
              step ∘ Prod.fst := by
          funext state
          dsimp only [step]
          congr 1
          funext outcome
          exact stoppedPruneTraceAdvance_fst roundCount cutoff decision queryCount state outcome
        rw [hkernel, ← PMF.bind_map, ih]
  change
    (adaptiveQueryStateLaw traceInitial traceOutcomeLaw traceAdvance traceBad roundCount).map
      (fun stateFailure => stateFailure.1.1) =
      adaptiveQueryActiveLaw (PMF.pure initial) outcomeLaw
        (stoppedPruneAdvance cutoff decision) roundCount
  calc
    (adaptiveQueryStateLaw traceInitial traceOutcomeLaw traceAdvance traceBad roundCount).map
        (fun stateFailure => stateFailure.1.1) =
        ((adaptiveQueryStateLaw traceInitial traceOutcomeLaw traceAdvance traceBad roundCount).map
          Prod.fst).map Prod.fst := by
            rw [PMF.map_comp]
            rfl
    _ = (adaptiveQueryActiveLaw traceInitial traceOutcomeLaw traceAdvance roundCount).map
        Prod.fst := by rw [hflag]
    _ = adaptiveQueryActiveLaw (PMF.pure initial) outcomeLaw
        (stoppedPruneAdvance cutoff decision) roundCount := hactive roundCount

/--
The stopped trace with a joint contraction-and-retention flag.  Its active
component evolves by the same transitions as Algorithm 2; the trace only
records the pre-round sets needed for the literal comparison count.
-/
noncomputable def freshStoppedPruneTraceCardAndMaxStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    PMF (stoppedPruneTraceState Arm roundCount × Bool) := by
  classical
  exact adaptiveQueryStateLaw
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1)
    (stoppedPruneTraceAdvance roundCount cutoff decision)
    (fun round state outcome =>
      (¬ state.1.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round state.1 outcome)).card : ℝ)) ∨
      (¬ state.1.card ≤ 2 * cutoff ∧ maximum ∈ state.1 ∧
        decision round state.1 outcome maximum ≠ .upper))
    roundCount

/--
Erasing only the resource trace (and retaining the joint Boolean flag) gives
the existing joint stopped-Prune execution.  This is the coupling that allows
its maximum-retention result and the trace's exact cost to be conjoined on one
finite PMF rather than on independent runs.
-/
theorem freshStoppedPruneTraceCardAndMaxStateLaw_map_activeFlagLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
      initial outcomeLaw decision roundCount).map (fun stateFailure =>
        (stateFailure.1.1, stateFailure.2)) =
      freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
        initial outcomeLaw decision roundCount := by
  classical
  let traceInitial : PMF (stoppedPruneTraceState Arm roundCount) :=
    PMF.pure (initialStoppedPruneTraceState roundCount initial)
  let traceOutcomeLaw : AdaptiveOutcomeKernel (stoppedPruneTraceState Arm roundCount) Outcome :=
    fun round state => outcomeLaw round state.1
  let traceAdvance : AdaptiveStateUpdate (stoppedPruneTraceState Arm roundCount) Outcome :=
    stoppedPruneTraceAdvance roundCount cutoff decision
  let traceBad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome =>
      (¬ state.1.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round state.1 outcome)).card : ℝ)) ∨
      (¬ state.1.card ≤ 2 * cutoff ∧ maximum ∈ state.1 ∧
        decision round state.1 outcome maximum ≠ .upper)
  let activeBad : ℕ → Finset Arm → Outcome → Prop :=
    fun round active outcome =>
      (¬ active.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ∨
      (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
        decision round active outcome maximum ≠ .upper)
  let eraseTrace : (stoppedPruneTraceState Arm roundCount × Bool) → Finset Arm × Bool :=
    fun stateFailure => (stateFailure.1.1, stateFailure.2)
  have hcoupling : ∀ queryCount,
      (adaptiveQueryStateLaw traceInitial traceOutcomeLaw traceAdvance traceBad queryCount).map
        eraseTrace =
      adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
        (stoppedPruneAdvance cutoff decision) activeBad queryCount := by
    intro queryCount
    induction queryCount with
    | zero =>
        simp only [adaptiveQueryStateLaw, traceInitial]
        rw [PMF.map_comp, PMF.pure_map, PMF.pure_map]
        rfl
    | succ queryCount ih =>
        rw [adaptiveQueryStateLaw, adaptiveQueryStateLaw, PMF.map_bind]
        simp_rw [PMF.map_comp]
        let step : Finset Arm × Bool → PMF (Finset Arm × Bool) := fun stateFailure =>
          (outcomeLaw queryCount stateFailure.1).map fun outcome =>
            (stoppedPruneAdvance cutoff decision queryCount stateFailure.1 outcome,
              stateFailure.2 || decide (activeBad queryCount stateFailure.1 outcome))
        have hkernel : (fun stateFailure : stoppedPruneTraceState Arm roundCount × Bool =>
            (traceOutcomeLaw queryCount stateFailure.1).map
              (eraseTrace ∘ fun outcome =>
                (traceAdvance queryCount stateFailure.1 outcome,
                  stateFailure.2 || decide (traceBad queryCount stateFailure.1 outcome)))) =
              step ∘ eraseTrace := by
          funext stateFailure
          dsimp only [traceOutcomeLaw, traceAdvance, eraseTrace, step, traceBad, activeBad]
          congr 1
          funext outcome
          simp only [Function.comp_apply, stoppedPruneTraceAdvance_fst]
        rw [hkernel, ← PMF.bind_map, ih]
  change
    (adaptiveQueryStateLaw traceInitial traceOutcomeLaw traceAdvance traceBad roundCount).map
      eraseTrace =
      adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
        (stoppedPruneAdvance cutoff decision) activeBad roundCount
  exact hcoupling roundCount

/-- The joint trace law has the same active-set marginal as Algorithm 2. -/
theorem freshStoppedPruneTraceCardAndMaxStateLaw_map_activeLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
      initial outcomeLaw decision roundCount).map (fun stateFailure => stateFailure.1.1) =
      freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount := by
  calc
    (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
      initial outcomeLaw decision roundCount).map (fun stateFailure => stateFailure.1.1) =
        ((freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial outcomeLaw decision roundCount).map (fun stateFailure =>
            (stateFailure.1.1, stateFailure.2))).map Prod.fst := by
          rw [PMF.map_comp]
          rfl
    _ = (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial outcomeLaw decision roundCount).map Prod.fst := by
          rw [freshStoppedPruneTraceCardAndMaxStateLaw_map_activeFlagLaw]
    _ = freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount :=
      freshStoppedPruneRoundsCardAndMaxStateLaw_map_fst_eq_activeLaw preferenceGap lower delta
        cutoff anchor maximum initial outcomeLaw decision roundCount

/-- The currently active set is recorded at the matching scheduled trace index. -/
theorem stoppedPruneTraceAdvance_trace_apply_of_lt
    {Arm Outcome : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (round : ℕ) (hround : round < roundCount)
    (state : stoppedPruneTraceState Arm roundCount) (outcome : Outcome) :
    (stoppedPruneTraceAdvance roundCount cutoff decision round state outcome).2
      ⟨round, hround⟩ = state.1 := by
  simp [stoppedPruneTraceAdvance, hround]

/-- A trace index other than the current round is preserved by the transition. -/
theorem stoppedPruneTraceAdvance_trace_apply_ne
    {Arm Outcome : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (round : ℕ) (hround : round < roundCount)
    (state : stoppedPruneTraceState Arm roundCount) (outcome : Outcome)
    (index : Fin roundCount) (hne : index.val ≠ round) :
    (stoppedPruneTraceAdvance roundCount cutoff decision round state outcome).2 index =
      state.2 index := by
  simp [stoppedPruneTraceAdvance, hround, Fin.ext_iff, hne]

/-- After the scheduling horizon, a trace transition cannot alter the trace. -/
theorem stoppedPruneTraceAdvance_trace_eq_of_not_lt
    {Arm Outcome : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (round : ℕ) (hround : ¬ round < roundCount)
    (state : stoppedPruneTraceState Arm roundCount) (outcome : Outcome) :
    (stoppedPruneTraceAdvance roundCount cutoff decision round state outcome).2 = state.2 := by
  simp [stoppedPruneTraceAdvance, hround]

/--
On a support point of the joint trace law, a false flag certifies all three
properties needed to compose Algorithm 2: the cardinality endpoint, retention
of the designated maximum, and the literal stopped comparison envelope.
-/
theorem freshStoppedPruneTraceCardAndMaxStateLaw_card_size_cost_and_max_of_support
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (delta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (roundCount : ℕ) (upper : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hdelta : 0 ≤ delta)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff)
    (stateFailure : stoppedPruneTraceState Arm roundCount × Bool)
    (hsupport : stateFailure ∈
      (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
        initial outcomeLaw decision roundCount).support)
    (hflag : stateFailure.2 = false) :
    stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
      (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
        stateFailure.1.2 : ℝ) ≤
        ∑ round : Fin roundCount,
          ((cutoff : ℝ) + delta ^ round.val *
            ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
            (fixedSampleBudget lower upper
              (adaptivePruneRoundDelta delta round.val) : ℝ) := by
  classical
  let badCount : Finset Arm → ℝ := fun active =>
    ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
  let activeAdvance : AdaptiveStateUpdate (Finset Arm) Outcome := stoppedPruneAdvance cutoff decision
  let advance : AdaptiveStateUpdate (stoppedPruneTraceState Arm roundCount) Outcome :=
    stoppedPruneTraceAdvance roundCount cutoff decision
  let contractionBad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧ cutoff < badCount state.1 ∧
        delta * badCount state.1 < badCount (activeAdvance round state.1 outcome)
  let retentionBad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧ maximum ∈ state.1 ∧
        decision round state.1 outcome maximum ≠ .upper
  let bad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome => contractionBad round state outcome ∨ retentionBad round state outcome
  let roundCost : ℕ → Finset Arm → ℝ := fun round active =>
    (if active.card ≤ 2 * cutoff then 0 else
      active.card * fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) : ℕ)
  let envelope : ℕ → ℝ := fun round =>
    ((cutoff : ℝ) + delta ^ round * badCount initial) *
      (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) : ℝ)
  let invariant : ℕ → stoppedPruneTraceState Arm roundCount → Bool → Prop :=
    fun round state flag =>
      flag = false →
        (state.1.card ≤ 2 * cutoff ∨ badCount state.1 ≤ cutoff ∨
          badCount state.1 ≤ delta ^ round * badCount initial) ∧
        maximum ∈ state.1 ∧
        ∀ index, index.val < round → roundCost index.val (state.2 index) ≤ envelope index.val
  have hinitial : ∀ state ∈
      (PMF.pure (initialStoppedPruneTraceState roundCount initial)).support,
      invariant 0 state false := by
    intro state hstate _
    simp [initialStoppedPruneTraceState] at hstate
    subst state
    refine ⟨?_, hmaximum, ?_⟩
    · right; right
      simp [badCount]
    · intro index hindex
      omega
  have hbadMonotone : ∀ round active outcome,
      badCount (activeAdvance round active outcome) ≤ badCount active := by
    intro round active outcome
    dsimp [badCount, activeAdvance]
    exact_mod_cast Finset.card_le_card
      (pruneBadArms_subset_of_subset preferenceGap lower anchor
        (stoppedPruneAdvance_subset cutoff decision round active outcome))
  have hroundCostBound : ∀ round active,
      (active.card ≤ 2 * cutoff ∨ badCount active ≤ cutoff ∨
        badCount active ≤ delta ^ round * badCount initial) →
      roundCost round active ≤ envelope round := by
    intro round active hstate
    by_cases hstopped : active.card ≤ 2 * cutoff
    · simp only [roundCost, if_pos hstopped, Nat.cast_zero, envelope]
      exact mul_nonneg
        (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hdelta _) (Nat.cast_nonneg _)))
        (Nat.cast_nonneg _)
    · simp only [roundCost, if_neg hstopped]
      push_cast
      have hgeometric : badCount active ≤ delta ^ round * badCount initial := by
        rcases hstate with hstop | hsmall | hgeometric
        · exact (hstopped hstop).elim
        · have hcard : active.card ≤ 2 * cutoff :=
            pruneActive_card_le_two_mul_of_goodAnchor_and_badArms preferenceGap lower cutoff anchor
              active hanchor ((Nat.cast_le (α := ℝ)).mp hsmall)
          exact (hstopped hcard).elim
        · exact hgeometric
      have hactiveCard : (active.card : ℝ) ≤
          (cutoff : ℝ) + delta ^ round * badCount initial := by
        calc
          (active.card : ℝ) ≤ (cutoff : ℝ) + badCount active := by
            change (active.card : ℝ) ≤ (cutoff : ℝ) +
              ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
            exact_mod_cast (active_card_le_cutoff_add_badCard_of_goodAnchor
              preferenceGap lower cutoff anchor active hanchor)
          _ ≤ (cutoff : ℝ) + delta ^ round * badCount initial := by gcongr
      exact mul_le_mul_of_nonneg_right hactiveCard (Nat.cast_nonneg _)
  have hadvance : ∀ round state flag outcome,
      invariant round state flag →
      invariant (round + 1) (advance round state outcome)
        (flag || decide (bad round state outcome)) := by
    intro round state flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round state outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round state outcome := by simpa using hbadFalse
    have hnotContraction : ¬ contractionBad round state outcome := fun hbad =>
      hnotBad (Or.inl hbad)
    have hnotRetention : ¬ retentionBad round state outcome := fun hbad =>
      hnotBad (Or.inr hbad)
    rcases hinvariant hflag with ⟨hstate, hmax, htrace⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [stoppedPruneTraceAdvance_fst]
      rcases hstate with hstopped | hsmall | hgeometric
      · left
        simp [stoppedPruneAdvance, hstopped]
      · right; left
        exact (hbadMonotone round state.1 outcome).trans hsmall
      · by_cases hsmall : badCount state.1 ≤ cutoff
        · right; left
          exact (hbadMonotone round state.1 outcome).trans hsmall
        · by_cases hstopped : state.1.card ≤ 2 * cutoff
          · left
            simp [stoppedPruneAdvance, hstopped]
          · right; right
            have hcontract : badCount (activeAdvance round state.1 outcome) ≤
                delta * badCount state.1 := by
              apply le_of_not_gt
              intro htooMany
              exact hnotContraction ⟨hstopped, lt_of_not_ge hsmall, htooMany⟩
            calc
              badCount (activeAdvance round state.1 outcome) ≤ delta * badCount state.1 := hcontract
              _ ≤ delta * (delta ^ round * badCount initial) :=
                mul_le_mul_of_nonneg_left hgeometric hdelta
              _ = delta ^ (round + 1) * badCount initial := by
                rw [pow_succ]
                ring
    · by_cases hstopped : state.1.card ≤ 2 * cutoff
      · rw [stoppedPruneTraceAdvance_fst]
        simpa [stoppedPruneAdvance, hstopped] using hmax
      · have hadvance : activeAdvance round state.1 outcome =
            pruneRound state.1 (decision round state.1 outcome) := by
              simp [activeAdvance, stoppedPruneAdvance, hstopped]
        rw [stoppedPruneTraceAdvance_fst]
        change maximum ∈ activeAdvance round state.1 outcome
        rw [hadvance]
        apply mem_pruneRound_of_upper state.1 (decision round state.1 outcome) maximum hmax
        by_contra hnotUpper
        exact hnotRetention ⟨hstopped, hmax, hnotUpper⟩
    · intro index hindex
      by_cases hround : round < roundCount
      · by_cases hindexEq : index.val = round
        · have heq : index = ⟨round, hround⟩ := Fin.ext hindexEq
          rw [heq, stoppedPruneTraceAdvance_trace_apply_of_lt]
          exact hroundCostBound round state.1 hstate
        · have hprior : index.val < round := by omega
          rw [stoppedPruneTraceAdvance_trace_apply_ne
            roundCount cutoff decision round hround state outcome index hindexEq]
          exact htrace index hprior
      · have hprior : index.val < round := by
          exact lt_of_lt_of_le index.isLt (Nat.le_of_not_gt hround)
        rw [stoppedPruneTraceAdvance_trace_eq_of_not_lt
          roundCount cutoff decision round hround state outcome]
        exact htrace index hprior
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1) advance bad invariant hinitial hadvance
  have hresult := hinvariantSupport roundCount stateFailure (by
    simpa only [freshStoppedPruneTraceCardAndMaxStateLaw, advance, bad,
      contractionBad, retentionBad, badCount, activeAdvance] using hsupport) hflag
  rcases hresult with ⟨hsize, hmax, htrace⟩
  refine ⟨?_, hmax, ?_⟩
  · rcases hsize with hstopped | hsmall | hgeometric
    · exact hstopped
    · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
        preferenceGap lower cutoff anchor stateFailure.1.1 hanchor
      exact (Nat.cast_le (α := ℝ)).mp hsmall
    · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
        preferenceGap lower cutoff anchor stateFailure.1.1 hanchor
      exact (Nat.cast_le (α := ℝ)).mp (by
        calc
          badCount stateFailure.1.1 ≤ delta ^ roundCount * badCount initial := hgeometric
          _ ≤ cutoff := by simpa [badCount] using htarget)
  · unfold stoppedPruneTraceComparisonCount
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro index hindex
    simpa [roundCost, envelope] using htrace index index.isLt

/--
The shared finite-PMF version of stopped Prune's joint guarantee: any
probability bound for the contraction-and-retention execution lifts to the
same execution augmented with its literal comparison trace.
-/
theorem freshStoppedPruneTraceCardAndMaxStateLaw_card_size_cost_and_max_probability_of_joint
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (delta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (roundCount : ℕ) (upper : ℝ) (successBound : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hdelta : 0 ≤ delta)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff)
    (hjoint : successBound ≤
      pmfProb
        (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1)) :
    successBound ≤
      pmfProb
        (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  let traceLaw :=
    freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
      initial outcomeLaw decision roundCount
  let baseEvent : stoppedPruneTraceState Arm roundCount × Bool → Prop := fun stateFailure =>
    stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1
  let fullEvent : stoppedPruneTraceState Arm roundCount × Bool → Prop := fun stateFailure =>
    stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
      (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
        stateFailure.1.2 : ℝ) ≤
        ∑ round : Fin roundCount,
          ((cutoff : ℝ) + delta ^ round.val *
            ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
            (fixedSampleBudget lower upper
              (adaptivePruneRoundDelta delta round.val) : ℝ)
  have hmap := freshStoppedPruneTraceCardAndMaxStateLaw_map_activeFlagLaw
    preferenceGap lower delta cutoff anchor maximum initial outcomeLaw decision roundCount
  have hbase : successBound ≤ pmfProb traceLaw baseEvent := by
    calc
      successBound ≤
          pmfProb
            (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
              initial outcomeLaw decision roundCount)
            (fun stateFailure => stateFailure.2 = false ∧
              stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := hjoint
      _ = pmfProb (traceLaw.map (fun stateFailure => (stateFailure.1.1, stateFailure.2)))
            (fun stateFailure => stateFailure.2 = false ∧
              stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
              rw [hmap]
      _ = pmfProb traceLaw baseEvent := by
            rw [pmfProb_map]
  have hequal : pmfProb traceLaw baseEvent = pmfProb traceLaw fullEvent := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hbaseEvent
      rcases freshStoppedPruneTraceCardAndMaxStateLaw_card_size_cost_and_max_of_support
        preferenceGap lower cutoff anchor maximum initial delta outcomeLaw decision roundCount upper
        hanchor hmaximum hdelta htarget stateFailure (by simpa [traceLaw] using hsupport)
        hbaseEvent.1 with ⟨hcard, hmax, hcost⟩
      exact ⟨hbaseEvent.1, hcard, hmax, hcost⟩
    · exact fun hfullEvent => ⟨hfullEvent.1, hfullEvent.2.1, hfullEvent.2.2.1⟩
  exact hbase.trans_eq hequal

/--
On all finite-PMF paths without an executed-round contraction failure, the
recorded Algorithm-2 trace simultaneously certifies the final size and the
exact stopped comparison envelope.
-/
theorem freshStoppedPruneTrace_card_size_two_costs_success_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (contraction scheduleDelta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ) (upper : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hcontraction : 0 ≤ contraction)
    (hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ≤
        failureBudget round)
    (htarget : contraction ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ) ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              (2 * contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) := by
  classical
  let badCount : Finset Arm → ℝ := fun active =>
    ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
  let activeAdvance : AdaptiveStateUpdate (Finset Arm) Outcome := stoppedPruneAdvance cutoff decision
  let advance : AdaptiveStateUpdate (stoppedPruneTraceState Arm roundCount) Outcome :=
    stoppedPruneTraceAdvance roundCount cutoff decision
  let bad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧ cutoff < badCount state.1 ∧
        contraction * badCount state.1 <
          badCount (activeAdvance round state.1 outcome)
  let roundCost : ℕ → Finset Arm → ℝ := fun round active =>
    (if active.card ≤ 2 * cutoff then 0 else
      active.card * fixedSampleBudget lower upper
        (adaptivePruneRoundDelta scheduleDelta round) : ℕ)
  let cutoffEnvelope : ℕ → ℝ := fun round =>
    ((cutoff : ℝ) + contraction ^ round * badCount initial) *
      (fixedSampleBudget lower upper (adaptivePruneRoundDelta scheduleDelta round) : ℝ)
  let rateEnvelope : ℕ → ℝ := fun round =>
    (2 * contraction ^ round * badCount initial) *
      (fixedSampleBudget lower upper (adaptivePruneRoundDelta scheduleDelta round) : ℝ)
  let invariant : ℕ → stoppedPruneTraceState Arm roundCount → Bool → Prop :=
    fun round state flag =>
      flag = false →
        (state.1.card ≤ 2 * cutoff ∨ badCount state.1 ≤ cutoff ∨
          badCount state.1 ≤ contraction ^ round * badCount initial) ∧
        ∀ index, index.val < round →
          roundCost index.val (state.2 index) ≤ cutoffEnvelope index.val ∧
          roundCost index.val (state.2 index) ≤ rateEnvelope index.val
  have hinitial : ∀ state ∈
      (PMF.pure (initialStoppedPruneTraceState roundCount initial)).support,
      invariant 0 state false := by
    intro state hstate _
    simp [initialStoppedPruneTraceState] at hstate
    subst state
    constructor
    · right; right
      simp [badCount]
    · intro index hindex
      omega
  have hbadMonotone : ∀ round active outcome,
      badCount (activeAdvance round active outcome) ≤ badCount active := by
    intro round active outcome
    dsimp [badCount, activeAdvance]
    exact_mod_cast Finset.card_le_card
      (pruneBadArms_subset_of_subset preferenceGap lower anchor
        (stoppedPruneAdvance_subset cutoff decision round active outcome))
  have hroundCostBound : ∀ round active,
      (active.card ≤ 2 * cutoff ∨ badCount active ≤ cutoff ∨
        badCount active ≤ contraction ^ round * badCount initial) →
      roundCost round active ≤ cutoffEnvelope round ∧
        roundCost round active ≤ rateEnvelope round := by
    intro round active hstate
    by_cases hstopped : active.card ≤ 2 * cutoff
    · simp only [roundCost, if_pos hstopped, Nat.cast_zero, cutoffEnvelope, rateEnvelope]
      constructor
      · exact mul_nonneg
          (add_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (pow_nonneg hcontraction _) (Nat.cast_nonneg _)))
          (Nat.cast_nonneg _)
      · exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hcontraction _))
            (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
    · simp only [roundCost, if_neg hstopped]
      push_cast
      have hgeometric : badCount active ≤ contraction ^ round * badCount initial := by
        rcases hstate with hstop | hsmall | hgeometric
        · exact (hstopped hstop).elim
        · have hcard : active.card ≤ 2 * cutoff :=
            pruneActive_card_le_two_mul_of_goodAnchor_and_badArms preferenceGap lower cutoff anchor
              active hanchor ((Nat.cast_le (α := ℝ)).mp hsmall)
          exact (hstopped hcard).elim
        · exact hgeometric
      have hactiveCardCutoff : (active.card : ℝ) ≤
          (cutoff : ℝ) + contraction ^ round * badCount initial := by
        calc
          (active.card : ℝ) ≤ (cutoff : ℝ) + badCount active := by
            change (active.card : ℝ) ≤ (cutoff : ℝ) +
              ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
            exact_mod_cast (active_card_le_cutoff_add_badCard_of_goodAnchor
              preferenceGap lower cutoff anchor active hanchor)
          _ ≤ (cutoff : ℝ) + contraction ^ round * badCount initial := by gcongr
      have hcutoffLtBad : (cutoff : ℝ) < badCount active := by
        simpa [badCount] using cutoff_lt_badCard_of_goodAnchor_and_running
          preferenceGap lower cutoff anchor active hanchor hstopped
      have hactiveCardRate : (active.card : ℝ) ≤
          2 * contraction ^ round * badCount initial := by
        have hactiveBad : (active.card : ℝ) ≤ (cutoff : ℝ) + badCount active := by
          change (active.card : ℝ) ≤ (cutoff : ℝ) +
            ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
          exact_mod_cast (active_card_le_cutoff_add_badCard_of_goodAnchor
            preferenceGap lower cutoff anchor active hanchor)
        calc
          (active.card : ℝ) ≤ (cutoff : ℝ) + badCount active := hactiveBad
          _ ≤ 2 * badCount active := by linarith
          _ ≤ 2 * (contraction ^ round * badCount initial) := by gcongr
          _ = 2 * contraction ^ round * badCount initial := by ring
      constructor
      · exact mul_le_mul_of_nonneg_right hactiveCardCutoff (Nat.cast_nonneg _)
      · exact mul_le_mul_of_nonneg_right hactiveCardRate (Nat.cast_nonneg _)
  have hadvance : ∀ round state flag outcome,
      invariant round state flag →
      invariant (round + 1) (advance round state outcome)
        (flag || decide (bad round state outcome)) := by
    intro round state flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round state outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round state outcome := by simpa using hbadFalse
    rcases hinvariant hflag with ⟨hstate, htrace⟩
    constructor
    · rw [stoppedPruneTraceAdvance_fst]
      rcases hstate with hstopped | hsmall | hgeometric
      · left
        simp [stoppedPruneAdvance, hstopped]
      · right; left
        exact (hbadMonotone round state.1 outcome).trans hsmall
      · by_cases hsmall : badCount state.1 ≤ cutoff
        · right; left
          exact (hbadMonotone round state.1 outcome).trans hsmall
        · by_cases hstopped : state.1.card ≤ 2 * cutoff
          · left
            simp [stoppedPruneAdvance, hstopped]
          · right; right
            have hcontract : badCount (activeAdvance round state.1 outcome) ≤
                contraction * badCount state.1 := by
                  apply le_of_not_gt
                  intro htooMany
                  exact hnotBad ⟨hstopped, lt_of_not_ge hsmall, htooMany⟩
            calc
              badCount (activeAdvance round state.1 outcome) ≤
                  contraction * badCount state.1 := hcontract
              _ ≤ contraction * (contraction ^ round * badCount initial) :=
                mul_le_mul_of_nonneg_left hgeometric hcontraction
              _ = contraction ^ (round + 1) * badCount initial := by
                rw [pow_succ]
                ring
    · intro index hindex
      by_cases hround : round < roundCount
      · by_cases hindexEq : index.val = round
        · have heq : index = ⟨round, hround⟩ := Fin.ext hindexEq
          rw [heq, stoppedPruneTraceAdvance_trace_apply_of_lt]
          exact hroundCostBound round state.1 hstate
        · have hprior : index.val < round := by omega
          rw [stoppedPruneTraceAdvance_trace_apply_ne
            roundCount cutoff decision round hround state outcome index hindexEq]
          exact htrace index hprior
      · have hprior : index.val < round := by
          exact lt_of_lt_of_le index.isLt (Nat.le_of_not_gt hround)
        rw [stoppedPruneTraceAdvance_trace_eq_of_not_lt
          roundCount cutoff decision round hround state outcome]
        exact htrace index hprior
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1) advance bad invariant hinitial hadvance
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1) advance bad failureBudget (by
      intro round state
      simpa [bad, badCount, activeAdvance] using hfailure round state.1) roundCount
  have hsuccessEvent : ∀ stateFailure ∈
      (adaptiveQueryStateLaw
        (PMF.pure (initialStoppedPruneTraceState roundCount initial))
        (fun round state => outcomeLaw round state.1) advance bad roundCount).support,
      stateFailure.2 = false →
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
          stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount, cutoffEnvelope round.val ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
          stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount, rateEnvelope round.val := by
    intro stateFailure hsupport hflag
    rcases hinvariantSupport roundCount stateFailure hsupport hflag with ⟨hstate, htrace⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases hstate with hstopped | hsmall | hgeometric
      · exact hstopped
      · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
          preferenceGap lower cutoff anchor stateFailure.1.1 hanchor
        exact (Nat.cast_le (α := ℝ)).mp hsmall
      · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
          preferenceGap lower cutoff anchor stateFailure.1.1 hanchor
        exact (Nat.cast_le (α := ℝ)).mp (by
          calc
            badCount stateFailure.1.1 ≤
                contraction ^ roundCount * badCount initial := hgeometric
            _ ≤ cutoff := by simpa [badCount] using htarget)
    · unfold stoppedPruneTraceComparisonCount
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro index hindex
      simpa [roundCost, cutoffEnvelope] using (htrace index index.isLt).1
    · unfold stoppedPruneTraceComparisonCount
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro index hindex
      simpa [roundCost, rateEnvelope] using (htrace index index.isLt).2
  have hequal : pmfProb
      (adaptiveQueryStateLaw
        (PMF.pure (initialStoppedPruneTraceState roundCount initial))
        (fun round state => outcomeLaw round state.1) advance bad roundCount)
      (fun stateFailure => stateFailure.2 = false) =
      pmfProb
        (adaptiveQueryStateLaw
          (PMF.pure (initialStoppedPruneTraceState roundCount initial))
          (fun round state => outcomeLaw round state.1) advance bad roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount, cutoffEnvelope round.val ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount, rateEnvelope round.val) := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hflag
      exact ⟨hflag, (hsuccessEvent stateFailure hsupport hflag).1,
        (hsuccessEvent stateFailure hsupport hflag).2.1,
        (hsuccessEvent stateFailure hsupport hflag).2.2⟩
    · exact fun h => h.1
  simpa only [freshStoppedPruneTraceStateLaw, advance, bad, cutoffEnvelope, rateEnvelope] using
    hsuccess.trans_eq hequal

/-- The legacy cutoff-plus-geometric envelope projected from the joint trace invariant. -/
theorem freshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (contraction scheduleDelta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ) (upper : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hcontraction : 0 ≤ contraction)
    (hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ≤
        failureBudget round)
    (htarget : contraction ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) := by
  exact (freshStoppedPruneTrace_card_size_two_costs_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor initial contraction scheduleDelta outcomeLaw decision
    failureBudget roundCount upper hanchor hcontraction hfailure htarget).trans
      (pmfProb_le_of_imp _ _ _ (by
        intro stateFailure h
        exact ⟨h.1, h.2.1, h.2.2.1⟩))

/-- The executed-round geometric envelope projected from the joint trace invariant. -/
theorem freshStoppedPruneTrace_card_size_rate_cost_success_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (contraction scheduleDelta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ) (upper : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hcontraction : 0 ≤ contraction)
    (hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ≤
        failureBudget round)
    (htarget : contraction ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              (2 * contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) := by
  exact (freshStoppedPruneTrace_card_size_two_costs_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor initial contraction scheduleDelta outcomeLaw decision
    failureBudget roundCount upper hanchor hcontraction hfailure htarget).trans
      (pmfProb_le_of_imp _ _ _ (by
        intro stateFailure h
        exact ⟨h.1, h.2.1, h.2.2.2⟩))

/--
The canonical finite Bernoulli stopped execution jointly satisfies Lemma 15's
size conclusion and its exact finite geometric comparison envelope with
probability at least `1 - n⁻²`.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq_of_schedule_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper scheduleDelta contraction : ℝ)
    (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta scheduleDelta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper)
    (hschedule : 0 < scheduleDelta) (hscheduleLeOne : scheduleDelta ≤ 1)
    (hcontraction : 0 < contraction) (hscheduleLeContraction : scheduleDelta ≤ contraction)
    (hcard : 2 ≤ Fintype.card Arm) (hroundCount : roundCount ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hcontractionLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ contraction)
    (htarget : contraction ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper scheduleDelta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) := by
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then 1 / (Fintype.card Arm : ℝ) ^ 3 else 1
  have hfailure : ∀ round active,
      pmfProb
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
          lower upper scheduleDelta maxBatch hbudget round active)
        (fun outcome =>
          ¬ active.card ≤ 2 * cutoff ∧
            cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
            contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (stoppedPruneAdvance cutoff
                  (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
                  round active outcome)).card : ℝ)) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · simpa [failureBudget, hround] using
        (canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube_of_schedule_le
          preferenceGap hprobability roundCount anchor lower upper scheduleDelta contraction
          maxBatch cutoff hbudget round hround active hseparation hschedule hscheduleLeOne
          hcontraction hscheduleLeContraction hcard hcutoff hcontractionLower)
    · simpa [failureBudget, hround] using
        (pmfProb_le_one
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper scheduleDelta maxBatch hbudget round active)
          (fun outcome =>
            ¬ active.card ≤ 2 * cutoff ∧
              cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
              contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                ((pruneBadArms preferenceGap lower anchor
                  (stoppedPruneAdvance cutoff
                    (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
                    round active outcome)).card : ℝ)))
  have hfresh := freshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor initial contraction scheduleDelta
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper scheduleDelta maxBatch hbudget)
    (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
    failureBudget roundCount upper hanchor hcontraction.le hfailure htarget
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
    calc
      (∑ round ∈ Finset.range roundCount, failureBudget round) =
          ∑ round ∈ Finset.range roundCount, 1 / (Fintype.card Arm : ℝ) ^ 3 := by
            apply Finset.sum_congr rfl
            intro round hround
            simp [failureBudget, Finset.mem_range.mp hround]
      _ = (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by simp
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hinvNonneg : 0 ≤ 1 / (Fintype.card Arm : ℝ) ^ 3 := by positivity
  have hsumLe : ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      1 / (Fintype.card Arm : ℝ) ^ 2 := by
    rw [hsum]
    calc
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) ≤
          (Fintype.card Arm : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hroundCount
            · exact hinvNonneg
      _ = 1 / (Fintype.card Arm : ℝ) ^ 2 := by
            field_simp [ne_of_gt hcardPos]
  calc
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by
          linarith
    _ ≤ pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper scheduleDelta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) := hfresh

/--
The same canonical stopped execution with the cutoff-independent executed-round
envelope.  A running round has more bad arms than the cutoff, so its whole
active set is at most twice its bad population; the no-failure flag then makes
that population geometrically summable.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_rate_cost_success_probability_ge_one_sub_card_inv_sq_of_schedule_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper scheduleDelta contraction : ℝ)
    (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta scheduleDelta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper)
    (hschedule : 0 < scheduleDelta) (hscheduleLeOne : scheduleDelta ≤ 1)
    (hcontraction : 0 < contraction) (hscheduleLeContraction : scheduleDelta ≤ contraction)
    (hcard : 2 ≤ Fintype.card Arm) (hroundCount : roundCount ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hcontractionLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ contraction)
    (htarget : contraction ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper scheduleDelta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              (2 * contraction ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) := by
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then 1 / (Fintype.card Arm : ℝ) ^ 3 else 1
  have hfailure : ∀ round active,
      pmfProb
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
          lower upper scheduleDelta maxBatch hbudget round active)
        (fun outcome =>
          ¬ active.card ≤ 2 * cutoff ∧
            cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
            contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (stoppedPruneAdvance cutoff
                  (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
                  round active outcome)).card : ℝ)) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · simpa [failureBudget, hround] using
        (canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube_of_schedule_le
          preferenceGap hprobability roundCount anchor lower upper scheduleDelta contraction
          maxBatch cutoff hbudget round hround active hseparation hschedule hscheduleLeOne
          hcontraction hscheduleLeContraction hcard hcutoff hcontractionLower)
    · simpa [failureBudget, hround] using
        (pmfProb_le_one
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper scheduleDelta maxBatch hbudget round active)
          (fun outcome =>
            ¬ active.card ≤ 2 * cutoff ∧
              cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
              contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                ((pruneBadArms preferenceGap lower anchor
                  (stoppedPruneAdvance cutoff
                    (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
                    round active outcome)).card : ℝ)))
  have hfresh := freshStoppedPruneTrace_card_size_rate_cost_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor initial contraction scheduleDelta
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper scheduleDelta maxBatch hbudget)
    (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
    failureBudget roundCount upper hanchor hcontraction.le hfailure htarget
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
    calc
      (∑ round ∈ Finset.range roundCount, failureBudget round) =
          ∑ round ∈ Finset.range roundCount, 1 / (Fintype.card Arm : ℝ) ^ 3 := by
            apply Finset.sum_congr rfl
            intro round hround
            simp [failureBudget, Finset.mem_range.mp hround]
      _ = (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by simp
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hinvNonneg : 0 ≤ 1 / (Fintype.card Arm : ℝ) ^ 3 := by positivity
  have hsumLe : ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      1 / (Fintype.card Arm : ℝ) ^ 2 := by
    rw [hsum]
    calc
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) ≤
          (Fintype.card Arm : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hroundCount
            · exact hinvNonneg
      _ = 1 / (Fintype.card Arm : ℝ) ^ 2 := by
            field_simp [ne_of_gt hcardPos]
  calc
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by
          linarith
    _ ≤ _ := hfresh

theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcard : 2 ≤ Fintype.card Arm) (hroundCount : roundCount ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then 1 / (Fintype.card Arm : ℝ) ^ 3 else 1
  have hfailure : ∀ round active,
      pmfProb
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
          lower upper delta maxBatch hbudget round active)
        (fun outcome =>
          ¬ active.card ≤ 2 * cutoff ∧
            cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
            delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (stoppedPruneAdvance cutoff
                  (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                  round active outcome)).card : ℝ)) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · simpa [failureBudget, hround] using
        (canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube
          preferenceGap hprobability roundCount anchor lower upper delta maxBatch cutoff hbudget
          round hround active hseparation hdelta hdeltaLeOne hcard hcutoff hdeltaLower)
    · simpa [failureBudget, hround] using
        (pmfProb_le_one
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget round active)
          (fun outcome =>
            ¬ active.card ≤ 2 * cutoff ∧
              cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
              delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                ((pruneBadArms preferenceGap lower anchor
                  (stoppedPruneAdvance cutoff
                    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                    round active outcome)).card : ℝ)))
  have hfresh := freshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor initial delta delta
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper delta maxBatch hbudget)
    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
    failureBudget roundCount upper hanchor hdelta.le hfailure htarget
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
    calc
      (∑ round ∈ Finset.range roundCount, failureBudget round) =
          ∑ round ∈ Finset.range roundCount, 1 / (Fintype.card Arm : ℝ) ^ 3 := by
            apply Finset.sum_congr rfl
            intro round hround
            simp [failureBudget, Finset.mem_range.mp hround]
      _ = (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by simp
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hinvNonneg : 0 ≤ 1 / (Fintype.card Arm : ℝ) ^ 3 := by positivity
  have hsumLe : ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      1 / (Fintype.card Arm : ℝ) ^ 2 := by
    rw [hsum]
    calc
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) ≤
          (Fintype.card Arm : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hroundCount
            · exact hinvNonneg
      _ = 1 / (Fintype.card Arm : ℝ) ^ 2 := by
            field_simp [ne_of_gt hcardPos]
  calc
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by
          linarith
    _ ≤ pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := hfresh

/--
Lemma 15's printed size probability together with the exact stopped-trace
resource envelope in the source-normalized `delta ≤ 1 / 2` regime.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_delta_half_of_sourceLemma15
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (Fintype.card Arm) cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin (Fintype.card Arm),
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  have hcutoffPosReal : 0 < (cutoff : ℝ) :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  have hcutoffPos : 0 < cutoff := by exact_mod_cast hcutoffPosReal
  have htarget := sourceLemma15_card_round_geometric_target preferenceGap lower anchor initial
    cutoff delta hcutoffPos hdelta.le hdeltaHalf
  have hcore := canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq
    preferenceGap hprobability (Fintype.card Arm) anchor lower upper delta maxBatch cutoff hbudget
    initial hanchor hseparation hdelta (hdeltaHalf.trans (by norm_num)) hcard (le_refl _)
    hcutoff hdeltaLower htarget
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hcutoffOne : 1 ≤ (cutoff : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hcutoffPos
  have hcardTwo : (2 : ℝ) ≤ (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hdeltaTail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 2 := by
    have hscale : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card Arm : ℝ))).mpr
      field_simp [ne_of_gt hcardPos]
      nlinarith [hcardTwo, hcutoffOne]
    calc
      1 / (Fintype.card Arm : ℝ) ^ 2 ≤
          (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := hscale
      _ = ((cutoff : ℝ) / (Fintype.card Arm : ℝ)) / 2 := by ring
      _ ≤ delta / 2 := by gcongr
  calc
    1 - delta / 2 ≤ 1 - 1 / (Fintype.card Arm : ℝ) ^ 2 := by linarith
    _ ≤ _ := hcore

/--
If the input already meets Prune's stopping rule, every scheduled transition
is a no-op.  The trace therefore has zero comparison cost and succeeds with
probability one at an arbitrary finite horizon.
-/
theorem freshStoppedPruneTrace_initial_small_state_success_probability
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower scheduleDelta contraction : ℝ)
    (cutoff : ℕ) (anchor : Arm) (initial : Finset Arm)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (roundCount : ℕ) (upper resourceBound : ℝ)
    (hsize : initial.card ≤ 2 * cutoff)
    (hresource : 0 ≤ resourceBound) :
    pmfProb
      (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
        outcomeLaw decision roundCount)
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1 = initial ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
          stateFailure.1.2 : ℝ) ≤ resourceBound) = 1 := by
  classical
  let advance : AdaptiveStateUpdate (stoppedPruneTraceState Arm roundCount) Outcome :=
    stoppedPruneTraceAdvance roundCount cutoff decision
  let bad : ℕ → stoppedPruneTraceState Arm roundCount → Outcome → Prop :=
    fun round state outcome =>
      ¬ state.1.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) ∧
        contraction * ((pruneBadArms preferenceGap lower anchor state.1).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round state.1 outcome)).card : ℝ)
  let invariant : ℕ → stoppedPruneTraceState Arm roundCount → Bool → Prop :=
    fun completed state flag =>
      flag = false ∧ state.1 = initial ∧
        ∀ index : Fin roundCount, index.val < completed → state.2 index = initial
  have hinitial : ∀ state ∈
      (PMF.pure (initialStoppedPruneTraceState roundCount initial)).support,
      invariant 0 state false := by
    intro state hstate
    have hstateEq : state = initialStoppedPruneTraceState roundCount initial := by
      simpa using hstate
    subst state
    refine ⟨rfl, rfl, ?_⟩
    intro index hindex
    omega
  have hadvance : ∀ completed state flag outcome,
      invariant completed state flag →
      invariant (completed + 1) (advance completed state outcome)
        (flag || decide (bad completed state outcome)) := by
    intro completed state flag outcome hstate
    rcases hstate with ⟨hflag, hactive, htrace⟩
    have hstateSmall : state.1.card ≤ 2 * cutoff := by simpa [hactive] using hsize
    refine ⟨?_, ?_, ?_⟩
    · simp [bad, hflag, hstateSmall]
    · rw [stoppedPruneTraceAdvance_fst]
      rw [show stoppedPruneAdvance cutoff decision completed state.1 outcome = state.1 by
        simp [stoppedPruneAdvance, hstateSmall]]
      exact hactive
    · intro index hindex
      by_cases hcompleted : completed < roundCount
      · by_cases heq : index.val = completed
        · have hindexEq : index = ⟨completed, hcompleted⟩ := Fin.ext heq
          rw [hindexEq, stoppedPruneTraceAdvance_trace_apply_of_lt]
          exact hactive
        · rw [stoppedPruneTraceAdvance_trace_apply_ne
            roundCount cutoff decision completed hcompleted state outcome index heq]
          exact htrace index (by omega)
      · rw [stoppedPruneTraceAdvance_trace_eq_of_not_lt
          roundCount cutoff decision completed hcompleted state outcome]
        exact htrace index (by omega)
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure (initialStoppedPruneTraceState roundCount initial))
    (fun round state => outcomeLaw round state.1) advance bad invariant hinitial hadvance
  let law := freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
    outcomeLaw decision roundCount
  let event : stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun stateFailure => stateFailure.2 = false ∧
      stateFailure.1.1 = initial ∧
      stateFailure.1.1.card ≤ 2 * cutoff ∧
      (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
        stateFailure.1.2 : ℝ) ≤ resourceBound
  have hevent : ∀ stateFailure ∈ law.support, event stateFailure := by
    intro stateFailure hsupport
    have hstate := hinvariantSupport roundCount stateFailure (by
      simpa only [law, freshStoppedPruneTraceStateLaw, advance, bad] using hsupport)
    rcases hstate with ⟨hflag, hactive, htrace⟩
    have hcostZero : stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
        stateFailure.1.2 = 0 := by
      unfold stoppedPruneTraceComparisonCount
      apply Finset.sum_eq_zero
      intro index _hindex
      rw [htrace index index.isLt]
      simp [hsize]
    exact ⟨hflag, hactive, by simpa [hactive] using hsize,
      by simpa [hcostZero] using hresource⟩
  calc
    pmfProb law event = pmfProb law (fun _ => True) := by
      apply pmfProb_eq_of_support_iff
      intro stateFailure hsupport
      exact ⟨fun _ => trivial, fun _ => hevent stateFailure hsupport⟩
    _ = 1 := pmfProb_eq_one_of_forall law (fun _ => True) (fun _ => trivial)

/--
If the input already meets Prune's stopping rule, the usual stopped-trace
size and resource event succeeds with probability one.  This compatibility
projection deliberately forgets the stronger active-set identity above.
-/
theorem freshStoppedPruneTrace_initial_small_success_probability
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower scheduleDelta contraction : ℝ)
    (cutoff : ℕ) (anchor : Arm) (initial : Finset Arm)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (roundCount : ℕ) (upper resourceBound : ℝ)
    (hsize : initial.card ≤ 2 * cutoff)
    (hresource : 0 ≤ resourceBound) :
    pmfProb
      (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
        outcomeLaw decision roundCount)
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
          stateFailure.1.2 : ℝ) ≤ resourceBound) = 1 := by
  have hstrong := freshStoppedPruneTrace_initial_small_state_success_probability
    preferenceGap lower scheduleDelta contraction cutoff anchor initial outcomeLaw decision
    roundCount upper resourceBound hsize hresource
  apply le_antisymm (pmfProb_le_one _ _)
  calc
    1 = pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1 = initial ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤ resourceBound) := hstrong.symm
    _ ≤ pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper scheduleDelta
            stateFailure.1.2 : ℝ) ≤ resourceBound) := by
      apply pmfProb_le_of_imp
      intro stateFailure hsuccess
      exact ⟨hsuccess.1, hsuccess.2.2.1, hsuccess.2.2.2⟩

/-- With zero scheduled rounds, the stopped trace succeeds deterministically when the input is small. -/
theorem freshStoppedPruneTrace_zero_round_success_probability
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower upper delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (hsize : initial.card ≤ 2 * cutoff) :
    pmfProb
      (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
        decision 0)
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount 0 cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
          ∑ round : Fin 0,
            ((cutoff : ℝ) + delta ^ round.val *
              ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
              (fixedSampleBudget lower upper
                (adaptivePruneRoundDelta delta round.val) : ℝ)) = 1 := by
  rw [show freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
      decision 0 = PMF.pure ((initialStoppedPruneTraceState 0 initial), false) by
        simp [freshStoppedPruneTraceStateLaw, adaptiveQueryStateLaw,
          initialStoppedPruneTraceState, PMF.pure_map]]
  have hevent :
      ((initialStoppedPruneTraceState 0 initial), false).2 = false ∧
        ((initialStoppedPruneTraceState 0 initial), false).1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount 0 cutoff lower upper delta
          ((initialStoppedPruneTraceState 0 initial), false).1.2 : ℝ) ≤
          ∑ round : Fin 0,
            ((cutoff : ℝ) + delta ^ round.val *
              ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
              (fixedSampleBudget lower upper
                (adaptivePruneRoundDelta delta round.val) : ℝ) := by
    simp [initialStoppedPruneTraceState, stoppedPruneTraceComparisonCount, hsize]
  simp [pmfProb, hevent]

/--
With no scheduled Prune rounds, the joint trace has deterministic size,
retention, and zero-cost success whenever the initial set is already small.
-/
theorem freshStoppedPruneTraceCardAndMaxStateLaw_zero_round_success_probability
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower upper delta : ℝ) (cutoff : ℕ)
    (anchor maximum : Arm) (initial : Finset Arm)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (hsize : initial.card ≤ 2 * cutoff) (hmaximum : maximum ∈ initial) :
    pmfProb
      (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
        initial outcomeLaw decision 0)
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
        (stoppedPruneTraceComparisonCount 0 cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
          ∑ round : Fin 0,
            ((cutoff : ℝ) + delta ^ round.val *
              ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
              (fixedSampleBudget lower upper
                (adaptivePruneRoundDelta delta round.val) : ℝ)) = 1 := by
  rw [show freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
      initial outcomeLaw decision 0 = PMF.pure ((initialStoppedPruneTraceState 0 initial), false) by
        simp [freshStoppedPruneTraceCardAndMaxStateLaw, adaptiveQueryStateLaw,
          initialStoppedPruneTraceState, PMF.pure_map]]
  have hevent :
      ((initialStoppedPruneTraceState 0 initial), false).2 = false ∧
        ((initialStoppedPruneTraceState 0 initial), false).1.1.card ≤ 2 * cutoff ∧
        maximum ∈ ((initialStoppedPruneTraceState 0 initial), false).1.1 ∧
        (stoppedPruneTraceComparisonCount 0 cutoff lower upper delta
          ((initialStoppedPruneTraceState 0 initial), false).1.2 : ℝ) ≤
          ∑ round : Fin 0,
            ((cutoff : ℝ) + delta ^ round.val *
              ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
              (fixedSampleBudget lower upper
                (adaptivePruneRoundDelta delta round.val) : ℝ) := by
    simp [initialStoppedPruneTraceState, stoppedPruneTraceComparisonCount, hsize, hmaximum]
  simp [pmfProb, hevent]

end FalahatgarEtAl2017MaxingRanking
