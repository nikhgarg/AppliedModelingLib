import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration
import AppliedModelingLib.Foundations.Probability.PMFKernel
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC
import Mathlib.Tactic

/-!
# Finite adaptive query processes

This module gives a finite-PMF execution model for a sequential query process.
Each fresh outcome law may depend on the full current state.  The state carries
an explicit failure flag, which makes the usual adaptive union bound a direct
induction rather than an independence assumption between query calls.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- The history-dependent fresh-outcome law at each query step. -/
abbrev AdaptiveOutcomeKernel (State Outcome : Type*) :=
  ℕ → PMFKernel State Outcome

/-- A deterministic state update after one fresh query outcome. -/
abbrev AdaptiveStateUpdate (State Outcome : Type*) :=
  ℕ → State → Outcome → State

/--
The distribution of the adaptive state together with a flag recording whether
any query failure has occurred in the first `queryCount` steps.
-/
noncomputable def adaptiveQueryStateLaw
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)] :
    ℕ → PMF (State × Bool)
  | 0 => initialStateLaw.map fun state => (state, false)
  | queryCount + 1 =>
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).bind
        fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome))

/-- The state marginal of an adaptive execution, with no auxiliary failure
flag.  This is the operational recursion when an analysis records failures
without allowing them to affect either the next-outcome kernel or the state
update. -/
noncomputable def adaptiveQueryStateValueLaw
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) :
    ℕ → PMF State
  | 0 => initialStateLaw
  | queryCount + 1 =>
      (adaptiveQueryStateValueLaw initialStateLaw outcomeLaw advance queryCount).bind
        fun state => (outcomeLaw queryCount state).map (advance queryCount state)

/-- Recording an adaptive failure flag does not alter the state marginal.
The flag is purely observational: the outcome kernel and state update remain
those of the underlying execution. -/
theorem adaptiveQueryStateLaw_map_fst_eq_valueLaw
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)] :
    ∀ queryCount,
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).map Prod.fst =
        adaptiveQueryStateValueLaw initialStateLaw outcomeLaw advance queryCount := by
  intro queryCount
  induction queryCount with
  | zero =>
      change (initialStateLaw.map (fun state => (state, false))).map Prod.fst = initialStateLaw
      rw [PMF.map_comp]
      exact PMF.map_id initialStateLaw
  | succ queryCount ih =>
      let previousLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
      let stateStep : State × Bool → PMF State := fun stateFailure =>
        (outcomeLaw queryCount stateFailure.1).map (advance queryCount stateFailure.1)
      let valueStep : State → PMF State := fun state =>
        (outcomeLaw queryCount state).map (advance queryCount state)
      change
        (previousLaw.bind fun stateFailure =>
          (outcomeLaw queryCount stateFailure.1).map fun outcome =>
            (advance queryCount stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryCount stateFailure.1 outcome))).map Prod.fst =
          (adaptiveQueryStateValueLaw initialStateLaw outcomeLaw advance queryCount).bind valueStep
      calc
        (previousLaw.bind fun stateFailure =>
            (outcomeLaw queryCount stateFailure.1).map fun outcome =>
              (advance queryCount stateFailure.1 outcome,
                stateFailure.2 || decide (bad queryCount stateFailure.1 outcome))).map Prod.fst =
            previousLaw.bind stateStep := by
              rw [PMF.map_bind]
              congr 1
              funext stateFailure
              rw [PMF.map_comp]
              rfl
        _ = (previousLaw.map Prod.fst).bind valueStep := by
              simpa only [Function.comp_apply, stateStep, valueStep] using
                (PMF.bind_map previousLaw Prod.fst valueStep).symm
        _ = (adaptiveQueryStateValueLaw initialStateLaw outcomeLaw advance queryCount).bind
            valueStep := by
              rw [show previousLaw =
                adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount from rfl]
              rw [ih]

/-- An adaptive execution is invariant under an exact projection of each
fresh outcome, provided that both its state update and its failure monitor
only read that projection.  The source outcome may retain latent information
that is useful for a semantic ledger while the projected outcome is the one
used by an operational trace. -/
theorem adaptiveQueryStateLaw_eq_of_outcomeProjection
    {State SourceOutcome ObservedOutcome : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype SourceOutcome] [DecidableEq SourceOutcome]
    [Fintype ObservedOutcome] [DecidableEq ObservedOutcome]
    (initialStateLaw : PMF State)
    (sourceOutcomeLaw : AdaptiveOutcomeKernel State SourceOutcome)
    (observedOutcomeLaw : AdaptiveOutcomeKernel State ObservedOutcome)
    (outcomeProjection : SourceOutcome → ObservedOutcome)
    (sourceAdvance : AdaptiveStateUpdate State SourceOutcome)
    (observedAdvance : AdaptiveStateUpdate State ObservedOutcome)
    (sourceBad : ℕ → State → SourceOutcome → Prop)
    (observedBad : ℕ → State → ObservedOutcome → Prop)
    [∀ queryIndex state outcome, Decidable (sourceBad queryIndex state outcome)]
    [∀ queryIndex state outcome, Decidable (observedBad queryIndex state outcome)]
    (houtcome : ∀ queryIndex state,
      (sourceOutcomeLaw queryIndex state).map outcomeProjection =
        observedOutcomeLaw queryIndex state)
    (hadvance : ∀ queryIndex state outcome,
      sourceAdvance queryIndex state outcome =
        observedAdvance queryIndex state (outcomeProjection outcome))
    (hbad : ∀ queryIndex state outcome,
      decide (sourceBad queryIndex state outcome) =
        decide (observedBad queryIndex state (outcomeProjection outcome))) :
    ∀ queryCount,
      adaptiveQueryStateLaw initialStateLaw sourceOutcomeLaw sourceAdvance sourceBad queryCount =
        adaptiveQueryStateLaw initialStateLaw observedOutcomeLaw observedAdvance observedBad
          queryCount := by
  intro queryCount
  induction queryCount with
  | zero => rfl
  | succ queryCount ih =>
      change
        (adaptiveQueryStateLaw initialStateLaw sourceOutcomeLaw sourceAdvance sourceBad
          queryCount).bind
          (fun stateFailure =>
            (sourceOutcomeLaw queryCount stateFailure.1).map fun outcome =>
              (sourceAdvance queryCount stateFailure.1 outcome,
                stateFailure.2 || decide (sourceBad queryCount stateFailure.1 outcome))) =
          (adaptiveQueryStateLaw initialStateLaw observedOutcomeLaw observedAdvance observedBad
            queryCount).bind
            (fun stateFailure =>
              (observedOutcomeLaw queryCount stateFailure.1).map fun outcome =>
                (observedAdvance queryCount stateFailure.1 outcome,
                  stateFailure.2 || decide (observedBad queryCount stateFailure.1 outcome)))
      rw [ih]
      congr 1
      funext stateFailure
      calc
        ((sourceOutcomeLaw queryCount stateFailure.1).map
          (fun outcome =>
            (sourceAdvance queryCount stateFailure.1 outcome,
              stateFailure.2 || decide (sourceBad queryCount stateFailure.1 outcome)))) =
          ((sourceOutcomeLaw queryCount stateFailure.1).map outcomeProjection).map
            (fun outcome =>
              (observedAdvance queryCount stateFailure.1 outcome,
                stateFailure.2 || decide (observedBad queryCount stateFailure.1 outcome))) := by
            rw [PMF.map_comp]
            congr 1
            funext outcome
            simp only [Function.comp_apply]
            rw [hadvance, hbad]
        _ = (observedOutcomeLaw queryCount stateFailure.1).map
            (fun outcome =>
              (observedAdvance queryCount stateFailure.1 outcome,
                stateFailure.2 || decide (observedBad queryCount stateFailure.1 outcome))) := by
            rw [houtcome]

/-- The finite adaptive recursion is independent of the particular decision
procedures chosen for finite states, outcomes, and its Boolean boundary. -/
theorem adaptiveQueryStateLaw_congr_instances
    {State Outcome : Type*} [Fintype State] [Fintype Outcome]
    (stateDecidableEq₁ stateDecidableEq₂ : DecidableEq State)
    (outcomeDecidableEq₁ outcomeDecidableEq₂ : DecidableEq Outcome)
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    (badDecidable₁ badDecidable₂ :
      ∀ queryIndex state outcome, Decidable (bad queryIndex state outcome))
    (queryCount : ℕ) :
    @adaptiveQueryStateLaw State Outcome _ stateDecidableEq₁
      _ outcomeDecidableEq₁ initialStateLaw outcomeLaw advance bad badDecidable₁ queryCount =
    @adaptiveQueryStateLaw State Outcome _ stateDecidableEq₂
      _ outcomeDecidableEq₂ initialStateLaw outcomeLaw advance bad badDecidable₂ queryCount := by
  have hstate : stateDecidableEq₁ = stateDecidableEq₂ := Subsingleton.elim _ _
  have houtcome : outcomeDecidableEq₁ = outcomeDecidableEq₂ := Subsingleton.elim _ _
  have hbad : badDecidable₁ = badDecidable₂ := Subsingleton.elim _ _
  subst stateDecidableEq₂
  subst outcomeDecidableEq₂
  subst badDecidable₂
  rfl

/-- A classical finite-event probability is invariant under the choice of
finite decision procedures used to build the same adaptive recursion. -/
theorem pmfProbClassical_adaptiveQueryStateLaw_congr_instances
    {State Outcome : Type*} [Fintype State] [Fintype Outcome]
    (stateDecidableEq₁ stateDecidableEq₂ : DecidableEq State)
    (outcomeDecidableEq₁ outcomeDecidableEq₂ : DecidableEq Outcome)
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    (badDecidable₁ badDecidable₂ :
      ∀ queryIndex state outcome, Decidable (bad queryIndex state outcome))
    (event : State × Bool → Prop) (queryCount : ℕ) :
    pmfProbClassical
      (@adaptiveQueryStateLaw State Outcome _ stateDecidableEq₁ _ outcomeDecidableEq₁
        initialStateLaw outcomeLaw advance bad badDecidable₁ queryCount) event =
    pmfProbClassical
      (@adaptiveQueryStateLaw State Outcome _ stateDecidableEq₂ _ outcomeDecidableEq₂
        initialStateLaw outcomeLaw advance bad badDecidable₂ queryCount) event := by
  rw [adaptiveQueryStateLaw_congr_instances
    stateDecidableEq₁ stateDecidableEq₂ outcomeDecidableEq₁ outcomeDecidableEq₂
    initialStateLaw outcomeLaw advance bad badDecidable₁ badDecidable₂ queryCount]

/-- The probability that at least one failure has occurred by a given query count. -/
noncomputable def adaptiveQueryFailureProbability
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (queryCount : ℕ) : ℝ :=
  pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
    (fun stateFailure => stateFailure.2 = true)

/--
At one adaptive step, the probability that the carried failure flag is set is
at most its earlier probability plus the historywise fresh-query budget.
-/
theorem adaptiveQueryFailureProbability_succ_le
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → ℝ)
    (hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤
        failureBudget queryIndex)
    (queryCount : ℕ) :
    adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad (queryCount + 1) ≤
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
        failureBudget queryCount := by
  let currentLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
  have hpoint : ∀ stateFailure : State × Bool,
      pmfProb (outcomeLaw queryCount stateFailure.1)
          (fun outcome =>
            (stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)) = true) ≤
        (if stateFailure.2 = true then 1 else 0) + failureBudget queryCount := by
    rintro ⟨state, flag⟩
    by_cases hflag : flag = true
    · have hbudgetNonneg : 0 ≤ failureBudget queryCount :=
        (pmfProb_nonneg (outcomeLaw queryCount state) (bad queryCount state)).trans
          (hfailure queryCount state)
      have hprobOne :
          pmfProb (outcomeLaw queryCount state) (fun _ : Outcome => True) = 1 :=
        by simp [pmfProb]
      simpa [hflag, hprobOne] using hbudgetNonneg
    · have hflagFalse : flag = false := Bool.eq_false_of_not_eq_true hflag
      simpa [hflagFalse] using hfailure queryCount state
  change pmfProb
      (currentLaw.bind fun stateFailure =>
        (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)))
      (fun stateFailure => stateFailure.2 = true) ≤
        adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
          failureBudget queryCount
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  calc
    pmfExp currentLaw (fun stateFailure =>
        pmfProb (outcomeLaw queryCount stateFailure.1) (fun outcome =>
          (stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)) = true)) ≤
      pmfExp currentLaw (fun stateFailure =>
        (if stateFailure.2 = true then 1 else 0) + failureBudget queryCount) :=
      FiniteMarkovKernel.pmfExp_mono currentLaw hpoint
    _ = adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
        failureBudget queryCount := by
      rw [pmfExp_add, pmfExp_const]
      rfl

/--
The accumulated state-dependent budget for a finite adaptive execution.  The
state carries the complete realized history, while the Boolean component of
the adaptive law records whether a prior query failure has already occurred.
-/
noncomputable def adaptiveQueryStateBudgetTotal
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ) (queryCount : ℕ) : ℝ :=
  ∑ queryIndex ∈ Finset.range queryCount,
    pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex)
      (failureBudget queryIndex)

/--
At one adaptive step, a history-dependent error budget is charged only at the
realized state.  The budget may be zero after the failure flag is set, provided
it is nonnegative there; this supports stopped analyses without charging
post-failure transitions.
-/
theorem adaptiveQueryFailureProbability_succ_le_stateBudget
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ)
    (hbudgetNonneg : ∀ queryIndex stateFailure, 0 ≤ failureBudget queryIndex stateFailure)
    (hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤
        failureBudget queryIndex (state, false))
    (queryCount : ℕ) :
    adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad (queryCount + 1) ≤
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (failureBudget queryCount) := by
  let currentLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
  have hpoint : ∀ stateFailure : State × Bool,
      pmfProb (outcomeLaw queryCount stateFailure.1)
          (fun outcome =>
            (stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)) = true) ≤
        (if stateFailure.2 = true then 1 else 0) + failureBudget queryCount stateFailure := by
    rintro ⟨state, flag⟩
    by_cases hflag : flag = true
    · have hnonneg := hbudgetNonneg queryCount (state, flag)
      have hprobOne :
          pmfProb (outcomeLaw queryCount state) (fun _ : Outcome => True) = 1 := by
        simp [pmfProb]
      simpa [hflag, hprobOne] using hnonneg
    · have hflagFalse : flag = false := Bool.eq_false_of_not_eq_true hflag
      simpa [hflagFalse] using hfailure queryCount state
  change pmfProb
      (currentLaw.bind fun stateFailure =>
        (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)))
      (fun stateFailure => stateFailure.2 = true) ≤
        adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
          pmfExp currentLaw (failureBudget queryCount)
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  calc
    pmfExp currentLaw (fun stateFailure =>
        pmfProb (outcomeLaw queryCount stateFailure.1) (fun outcome =>
          (stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)) = true)) ≤
      pmfExp currentLaw (fun stateFailure =>
        (if stateFailure.2 = true then 1 else 0) + failureBudget queryCount stateFailure) :=
      FiniteMarkovKernel.pmfExp_mono currentLaw hpoint
    _ = adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
        pmfExp currentLaw (failureBudget queryCount) := by
      rw [pmfExp_add]
      rfl

/--
The finite adaptive union bound with a budget that may depend on the complete
realized state and the carried failure flag.
-/
theorem adaptiveQueryFailureProbability_le_stateBudgetTotal
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ)
    (hbudgetNonneg : ∀ queryIndex stateFailure, 0 ≤ failureBudget queryIndex stateFailure)
    (hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤
        failureBudget queryIndex (state, false)) :
    ∀ queryCount,
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount ≤
        adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount := by
  intro queryCount
  induction queryCount with
  | zero =>
      unfold adaptiveQueryFailureProbability adaptiveQueryStateBudgetTotal adaptiveQueryStateLaw
      rw [pmfProb_map]
      simp [pmfProb]
  | succ queryCount ih =>
      calc
        adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad
            (queryCount + 1) ≤
          adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
              (failureBudget queryCount) :=
          adaptiveQueryFailureProbability_succ_le_stateBudget initialStateLaw outcomeLaw advance
            bad failureBudget hbudgetNonneg hfailure queryCount
        _ ≤ adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad
              failureBudget queryCount +
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
              (failureBudget queryCount) :=
          add_le_add ih le_rfl
        _ = adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad
              failureBudget (queryCount + 1) := by
          simp [adaptiveQueryStateBudgetTotal, Finset.sum_range_succ]

/--
The complementary state-budget form of the finite adaptive union bound.
-/
theorem adaptiveQuerySuccessProbability_ge_one_sub_stateBudgetTotal
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ)
    (hbudgetNonneg : ∀ queryIndex stateFailure, 0 ≤ failureBudget queryIndex stateFailure)
    (hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤
        failureBudget queryIndex (state, false))
    (queryCount : ℕ) :
    1 - adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount ≤
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => stateFailure.2 = false) := by
  have hfailureBound := adaptiveQueryFailureProbability_le_stateBudgetTotal
    initialStateLaw outcomeLaw advance bad failureBudget hbudgetNonneg hfailure queryCount
  have hsuccess :
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = false) =
        1 - adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount := by
    calc
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = false) =
        pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => ¬ stateFailure.2 = true) := by
            apply pmfProb_congr
            intro stateFailure
            cases stateFailure.2 <;> simp
      _ = 1 - pmfProb
          (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = true) :=
        pmfProb_compl _ _
      _ = 1 - adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount :=
        rfl
  rw [hsuccess]
  linarith

/--
Any upper bound on the recorded adaptive failure probability yields the
corresponding lower bound on the no-failure state event.  This separates the
event-complement arithmetic from the particular union-bound or potential
argument used to establish the failure bound.
-/
theorem adaptiveQuerySuccessProbability_ge_one_sub_of_failureProbabilityBound
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (queryCount : ℕ) (failureBound : ℝ)
    (hfailure : adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount ≤
      failureBound) :
    1 - failureBound ≤
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => stateFailure.2 = false) := by
  have hsuccess :
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = false) =
        1 - adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount := by
    calc
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = false) =
        pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => ¬ stateFailure.2 = true) := by
            apply pmfProb_congr
            intro stateFailure
            cases stateFailure.2 <;> simp
      _ = 1 - pmfProb
          (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = true) :=
        pmfProb_compl _ _
      _ = 1 - adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount :=
        rfl
  rw [hsuccess]
  linarith

/--
An event that holds at every supported no-failure terminal state inherits the
same lower probability bound as the adaptive success event.  The event need
not have a computable decision procedure in the public interface.
-/
theorem adaptiveQueryEventProbability_ge_one_sub_of_failureProbabilityBound
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (queryCount : ℕ) (failureBound : ℝ)
    (hfailure : adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount ≤
      failureBound)
    (event : State × Bool → Prop)
    (hevent : ∀ stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support,
      stateFailure.2 = false → event stateFailure) :
    1 - failureBound ≤
      pmfProbClassical (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount) event := by
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_of_failureProbabilityBound
    initialStateLaw outcomeLaw advance bad queryCount failureBound hfailure
  rw [← pmfProbClassical_eq_pmfProb] at hsuccess
  exact hsuccess.trans (pmfProbClassical_le_of_support_imp
    (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
    (fun stateFailure => stateFailure.2 = false) event hevent)

/--
The probability of any failure in a finite adaptive query execution is bounded
by the sum of the historywise per-query budgets.  No independence among the
adaptively selected calls is assumed.
-/
theorem adaptiveQueryFailureProbability_le_sum
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → ℝ)
    (hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤
        failureBudget queryIndex) :
    ∀ queryCount,
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount ≤
        ∑ queryIndex ∈ Finset.range queryCount, failureBudget queryIndex := by
  intro queryCount
  induction queryCount with
  | zero =>
      unfold adaptiveQueryFailureProbability adaptiveQueryStateLaw
      rw [pmfProb_map]
      simp [pmfProb]
  | succ queryCount ih =>
      calc
        adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad
            (queryCount + 1) ≤
          adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
            failureBudget queryCount :=
          adaptiveQueryFailureProbability_succ_le initialStateLaw outcomeLaw advance bad
            failureBudget hfailure queryCount
        _ ≤ (∑ queryIndex ∈ Finset.range queryCount, failureBudget queryIndex) +
            failureBudget queryCount :=
          add_le_add ih (le_refl _)
        _ = ∑ queryIndex ∈ Finset.range (queryCount + 1), failureBudget queryIndex := by
          rw [Finset.sum_range_succ]

/--
The complementary all-success event in a finite adaptive query process has
probability at least one minus the sum of its historywise failure budgets.
-/
theorem adaptiveQuerySuccessProbability_ge_one_sub_sum
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → ℝ)
    (hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤
        failureBudget queryIndex)
    (queryCount : ℕ) :
    1 - ∑ queryIndex ∈ Finset.range queryCount, failureBudget queryIndex ≤
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => stateFailure.2 = false) := by
  have hfailureBound := adaptiveQueryFailureProbability_le_sum
    initialStateLaw outcomeLaw advance bad failureBudget hfailure queryCount
  have hsuccess :
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = false) =
        1 - adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount := by
    calc
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = false) =
        pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => ¬ stateFailure.2 = true) := by
            apply pmfProb_congr
            intro stateFailure
            cases stateFailure.2 <;> simp
      _ = 1 - pmfProb
          (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure => stateFailure.2 = true) :=
        pmfProb_compl _ _
      _ = 1 - adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount :=
        rfl
  rw [hsuccess]
  linarith

end PreferenceRL

end AppliedModelingLib
