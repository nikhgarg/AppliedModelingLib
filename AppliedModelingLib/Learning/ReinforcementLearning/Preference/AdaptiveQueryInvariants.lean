import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueries

/-!
# Invariants for finite adaptive query processes

The support induction for `adaptiveQueryStateLaw`: a deterministic invariant
holds on every positive-mass state when it holds initially and each fresh
query update preserves it.
-/

namespace AppliedModelingLib.PreferenceRL

/--
Finite-PMF event probabilities agree when the two predicates agree throughout
the law's support.  Values outside the support have zero mass.
-/
theorem pmfProb_eq_of_support_iff
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    [DecidablePred first] [DecidablePred second]
    (hiff : ∀ outcome ∈ law.support, first outcome ↔ second outcome) :
    pmfProb law first = pmfProb law second := by
  unfold pmfProb pmfExp
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hsupport : outcome ∈ law.support
  · simp [hiff outcome hsupport]
  · have hzero : law outcome = 0 := by
      by_contra hnonzero
      exact hsupport ((law.mem_support_iff outcome).mpr hnonzero)
    simp [hzero]

/-- A finite-PMF expectation is monotone when the pointwise comparison holds on support. -/
theorem pmfExp_mono_of_support
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) {first second : Outcome → ℝ}
    (hle : ∀ outcome ∈ law.support, first outcome ≤ second outcome) :
    pmfExp law first ≤ pmfExp law second := by
  unfold pmfExp
  apply Finset.sum_le_sum
  intro outcome _
  by_cases hsupport : outcome ∈ law.support
  · exact mul_le_mul_of_nonneg_left (hle outcome hsupport) ENNReal.toReal_nonneg
  · have hzero : law outcome = 0 := by
      by_contra hnonzero
      exact hsupport ((law.mem_support_iff outcome).mpr hnonzero)
    simp [hzero]

/-- Finite-PMF expectations agree when their integrands agree on the support. -/
theorem pmfExp_eq_of_support
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (first second : Outcome → ℝ)
    (heq : ∀ outcome ∈ law.support, first outcome = second outcome) :
    pmfExp law first = pmfExp law second := by
  unfold pmfExp
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hsupport : outcome ∈ law.support
  · rw [heq outcome hsupport]
  · have hzero : law outcome = 0 := by
      by_contra hnonzero
      exact hsupport ((law.mem_support_iff outcome).mpr hnonzero)
    simp [hzero]

/--
An adaptive state budget is bounded by a terminal potential when the potential
starts at zero on the initial support and each realized transition increases it
by exactly that step's charged budget.  This is a finite-PMF telescoping
principle; it does not require independence between adaptive steps.
-/
theorem adaptiveQueryStateBudgetTotal_le_of_potential
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ) (potential : State × Bool → ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, potential (state, false) = 0)
    (hadvance : ∀ queryIndex stateFailure outcome,
      potential
          (advance queryIndex stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryIndex stateFailure.1 outcome)) =
        potential stateFailure + failureBudget queryIndex stateFailure)
    (queryCount : ℕ) (bound : ℝ)
    (hterminal : ∀ stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support,
      potential stateFailure ≤ bound) :
    adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount ≤
      bound := by
  have hinitialExp : pmfExp initialStateLaw (fun state => potential (state, false)) = 0 := by
    unfold pmfExp
    apply Finset.sum_eq_zero
    intro state _
    by_cases hstate : state ∈ initialStateLaw.support
    · simp [hinitial state hstate]
    · have hzero : initialStateLaw state = 0 := by
        by_contra hnonzero
        exact hstate ((initialStateLaw.mem_support_iff state).mpr hnonzero)
      simp [hzero]
  have htelescoping : ∀ count,
      adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count =
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count) potential := by
    intro count
    induction count with
    | zero =>
        simp only [adaptiveQueryStateBudgetTotal, Finset.sum_range_zero,
          adaptiveQueryStateLaw]
        rw [pmfExp_map]
        exact hinitialExp.symm
    | succ count ih =>
        have hsplit :
            adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget
                (count + 1) =
              adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count +
                pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
                  (failureBudget count) := by
          simp [adaptiveQueryStateBudgetTotal, Finset.sum_range_succ]
        rw [hsplit]
        rw [ih]
        change pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count) potential +
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (failureBudget count) =
          pmfExp
            ((adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count).bind
              fun stateFailure => (outcomeLaw count stateFailure.1).map fun outcome =>
                (advance count stateFailure.1 outcome,
                  stateFailure.2 || decide (bad count stateFailure.1 outcome)))
            potential
        rw [pmfExp_bind]
        simp_rw [pmfExp_map]
        apply Eq.symm
        calc
          pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (fun stateFailure =>
                pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                  potential
                    (advance count stateFailure.1 outcome,
                      stateFailure.2 || decide (bad count stateFailure.1 outcome)))) =
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (fun stateFailure => potential stateFailure + failureBudget count stateFailure) := by
                apply pmfExp_congr
                intro stateFailure
                calc
                  pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                      potential
                        (advance count stateFailure.1 outcome,
                          stateFailure.2 || decide (bad count stateFailure.1 outcome))) =
                    pmfExp (outcomeLaw count stateFailure.1)
                      (fun _ => potential stateFailure + failureBudget count stateFailure) := by
                        apply pmfExp_congr
                        intro outcome
                        exact hadvance count stateFailure outcome
                  _ = _ := by rw [pmfExp_const]
          _ = _ := by rw [pmfExp_add]
  calc
    adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount =
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount) potential :=
      htelescoping queryCount
    _ ≤ pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun _ => bound) :=
      pmfExp_mono_of_support
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        hterminal
    _ = bound := by rw [pmfExp_const]

/--
The support-restricted potential form of adaptive budget accounting.  It is
the appropriate form for stopped executions: behavior on states or outcomes
that have zero probability under the current prefix need not be specified.
-/
theorem adaptiveQueryStateBudgetTotal_le_of_potential_of_support
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ) (potential : State × Bool → ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, potential (state, false) = 0)
    (hadvance : ∀ queryIndex stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      ∀ outcome ∈ (outcomeLaw queryIndex stateFailure.1).support,
        potential
            (advance queryIndex stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryIndex stateFailure.1 outcome)) =
          potential stateFailure + failureBudget queryIndex stateFailure)
    (queryCount : ℕ) (bound : ℝ)
    (hterminal : ∀ stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support,
      potential stateFailure ≤ bound) :
    adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount ≤
      bound := by
  have hinitialExp : pmfExp initialStateLaw (fun state => potential (state, false)) = 0 := by
    unfold pmfExp
    apply Finset.sum_eq_zero
    intro state _
    by_cases hstate : state ∈ initialStateLaw.support
    · simp [hinitial state hstate]
    · have hzero : initialStateLaw state = 0 := by
        by_contra hnonzero
        exact hstate ((initialStateLaw.mem_support_iff state).mpr hnonzero)
      simp [hzero]
  have htelescoping : ∀ count,
      adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count =
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count) potential := by
    intro count
    induction count with
    | zero =>
        simp only [adaptiveQueryStateBudgetTotal, Finset.sum_range_zero,
          adaptiveQueryStateLaw]
        rw [pmfExp_map]
        exact hinitialExp.symm
    | succ count ih =>
        have hsplit :
            adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget
                (count + 1) =
              adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count +
                pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
                  (failureBudget count) := by
          simp [adaptiveQueryStateBudgetTotal, Finset.sum_range_succ]
        rw [hsplit, ih]
        change pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count) potential +
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (failureBudget count) =
          pmfExp
            ((adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count).bind
              fun stateFailure => (outcomeLaw count stateFailure.1).map fun outcome =>
                (advance count stateFailure.1 outcome,
                  stateFailure.2 || decide (bad count stateFailure.1 outcome)))
            potential
        rw [pmfExp_bind]
        simp_rw [pmfExp_map]
        apply Eq.symm
        calc
          pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (fun stateFailure =>
                pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                  potential
                    (advance count stateFailure.1 outcome,
                      stateFailure.2 || decide (bad count stateFailure.1 outcome)))) =
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (fun stateFailure => potential stateFailure + failureBudget count stateFailure) := by
                apply pmfExp_eq_of_support
                intro stateFailure hstateFailure
                calc
                  pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                      potential
                        (advance count stateFailure.1 outcome,
                          stateFailure.2 || decide (bad count stateFailure.1 outcome))) =
                    pmfExp (outcomeLaw count stateFailure.1)
                      (fun _ => potential stateFailure + failureBudget count stateFailure) := by
                        apply pmfExp_eq_of_support
                        intro outcome houtcome
                        exact hadvance count stateFailure hstateFailure outcome houtcome
                  _ = _ := by rw [pmfExp_const]
          _ = _ := by rw [pmfExp_add]
  calc
    adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount =
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount) potential :=
      htelescoping queryCount
    _ ≤ pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun _ => bound) :=
      pmfExp_mono_of_support
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        hterminal
    _ = bound := by rw [pmfExp_const]

/--
The support-restricted potential form with one-sided step accounting.  A
potential may jump upwards when an execution first leaves its live region;
that is exactly what is needed to stop charging a query budget after the
first recorded failure without prescribing arbitrary later state updates.
-/
theorem adaptiveQueryStateBudgetTotal_le_of_potentialLowerBound_of_support
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → State × Bool → ℝ) (potential : State × Bool → ℝ)
    (hinitial : ∀ state ∈ initialStateLaw.support, potential (state, false) = 0)
    (hadvance : ∀ queryIndex stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      ∀ outcome ∈ (outcomeLaw queryIndex stateFailure.1).support,
        potential
            (advance queryIndex stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryIndex stateFailure.1 outcome)) ≥
          potential stateFailure + failureBudget queryIndex stateFailure)
    (queryCount : ℕ) (bound : ℝ)
    (hterminal : ∀ stateFailure ∈
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support,
      potential stateFailure ≤ bound) :
    adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount ≤
      bound := by
  have hinitialExp : pmfExp initialStateLaw (fun state => potential (state, false)) = 0 := by
    unfold pmfExp
    apply Finset.sum_eq_zero
    intro state _
    by_cases hstate : state ∈ initialStateLaw.support
    · simp [hinitial state hstate]
    · have hzero : initialStateLaw state = 0 := by
        by_contra hnonzero
        exact hstate ((initialStateLaw.mem_support_iff state).mpr hnonzero)
      simp [hzero]
  have htelescoping : ∀ count,
      adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count ≤
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count) potential := by
    intro count
    induction count with
    | zero =>
        simp only [adaptiveQueryStateBudgetTotal, Finset.sum_range_zero,
          adaptiveQueryStateLaw]
        rw [pmfExp_map]
        exact le_of_eq hinitialExp.symm
    | succ count ih =>
        have hsplit :
            adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget
                (count + 1) =
              adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count +
                pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
                  (failureBudget count) := by
          simp [adaptiveQueryStateBudgetTotal, Finset.sum_range_succ]
        rw [hsplit]
        calc
          adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget count +
              pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
                (failureBudget count) ≤
            pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count) potential +
              pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
                (failureBudget count) := add_le_add ih le_rfl
          _ = pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (fun stateFailure => potential stateFailure + failureBudget count stateFailure) := by
                rw [pmfExp_add]
          _ ≤ pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
              (fun stateFailure =>
                pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                  potential
                    (advance count stateFailure.1 outcome,
                      stateFailure.2 || decide (bad count stateFailure.1 outcome)))) := by
                apply pmfExp_mono_of_support
                intro stateFailure hstateFailure
                calc
                  potential stateFailure + failureBudget count stateFailure =
                    pmfExp (outcomeLaw count stateFailure.1)
                      (fun _ => potential stateFailure + failureBudget count stateFailure) := by
                        rw [pmfExp_const]
                  _ ≤ pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                      potential
                        (advance count stateFailure.1 outcome,
                          stateFailure.2 || decide (bad count stateFailure.1 outcome))) := by
                        apply pmfExp_mono_of_support
                        intro outcome houtcome
                        exact hadvance count stateFailure hstateFailure outcome houtcome
          _ = pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad (count + 1))
              potential := by
                change pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count)
                    (fun stateFailure =>
                      pmfExp (outcomeLaw count stateFailure.1) (fun outcome =>
                        potential
                          (advance count stateFailure.1 outcome,
                            stateFailure.2 || decide (bad count stateFailure.1 outcome)))) =
                  pmfExp
                    ((adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad count).bind
                      fun stateFailure => (outcomeLaw count stateFailure.1).map fun outcome =>
                        (advance count stateFailure.1 outcome,
                          stateFailure.2 || decide (bad count stateFailure.1 outcome)))
                    potential
                rw [pmfExp_bind]
                simp_rw [pmfExp_map]
  calc
    adaptiveQueryStateBudgetTotal initialStateLaw outcomeLaw advance bad failureBudget queryCount ≤
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount) potential :=
      htelescoping queryCount
    _ ≤ pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun _ => bound) :=
      pmfExp_mono_of_support
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        hterminal
    _ = bound := by rw [pmfExp_const]

/-- If a state event is invariant under every adaptive update after a chosen
prefix, its probability is unchanged by running additional queries.  This is
the common-law bridge used to compare prefix statistics on a full adaptive
execution without an independence assumption. -/
theorem adaptiveQueryStateLaw_event_probability_add_eq
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (event : State × Bool → Prop) [DecidablePred event]
    (prefixCount additional : ℕ)
    (hpreserve : ∀ queryIndex, prefixCount ≤ queryIndex →
      ∀ (stateFailure : State × Bool) outcome,
        event
            (advance queryIndex stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryIndex stateFailure.1 outcome)) ↔
          event stateFailure) :
    pmfProb
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad
          (prefixCount + additional)) event =
      pmfProb
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad prefixCount) event := by
  classical
  induction additional with
  | zero => simp
  | succ additional ih =>
      let queryIndex := prefixCount + additional
      let currentLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex
      have hqueryIndex : prefixCount ≤ queryIndex := Nat.le_add_right prefixCount additional
      have hconditional : ∀ stateFailure : State × Bool,
          pmfProb (outcomeLaw queryIndex stateFailure.1)
              (fun outcome ↦
                event
                  (advance queryIndex stateFailure.1 outcome,
                    stateFailure.2 || decide (bad queryIndex stateFailure.1 outcome))) =
            if event stateFailure then 1 else 0 := by
        intro stateFailure
        by_cases hevent : event stateFailure
        · calc
            pmfProb (outcomeLaw queryIndex stateFailure.1)
                (fun outcome ↦ event
                  (advance queryIndex stateFailure.1 outcome,
                    stateFailure.2 || decide
                      (bad queryIndex stateFailure.1 outcome))) =
                pmfProb (outcomeLaw queryIndex stateFailure.1)
                  (fun _outcome ↦ True) := by
                    apply pmfProb_congr
                    intro outcome
                    simpa [hevent] using
                      hpreserve queryIndex hqueryIndex stateFailure outcome
            _ = if event stateFailure then 1 else 0 := by simp [hevent, pmfProb]
        · calc
            pmfProb (outcomeLaw queryIndex stateFailure.1)
                (fun outcome ↦ event
                  (advance queryIndex stateFailure.1 outcome,
                    stateFailure.2 || decide
                      (bad queryIndex stateFailure.1 outcome))) =
                pmfProb (outcomeLaw queryIndex stateFailure.1)
                  (fun _outcome ↦ False) := by
                    apply pmfProb_congr
                    intro outcome
                    simpa [hevent] using
                      hpreserve queryIndex hqueryIndex stateFailure outcome
            _ = if event stateFailure then 1 else 0 := by simp [hevent, pmfProb]
      rw [show prefixCount + (additional + 1) = queryIndex + 1 by
        dsimp [queryIndex]
        omega]
      change pmfProb
          (currentLaw.bind fun stateFailure =>
            (outcomeLaw queryIndex stateFailure.1).map fun outcome =>
              (advance queryIndex stateFailure.1 outcome,
                stateFailure.2 || decide (bad queryIndex stateFailure.1 outcome))) event = _
      rw [pmfProb_bind]
      simp_rw [pmfProb_map]
      calc
        pmfExp currentLaw (fun stateFailure =>
            pmfProb (outcomeLaw queryIndex stateFailure.1)
              (fun outcome ↦ event
                (advance queryIndex stateFailure.1 outcome,
                  stateFailure.2 || decide
                    (bad queryIndex stateFailure.1 outcome)))) =
            pmfExp currentLaw (fun stateFailure =>
              if event stateFailure then 1 else 0) := by
                apply pmfExp_congr
                exact hconditional
        _ = pmfProb currentLaw event := rfl
        _ = pmfProb
            (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad prefixCount) event := by
              simpa [currentLaw, queryIndex] using ih

/--
Two finite randomized stages compose without a false independence assumption:
if the first state is good except with mass `deltaState`, and conditional on
every good state the fresh second stage is good except with mass
`deltaOutcome`, their joint success has mass at least `1 - deltaState -
deltaOutcome`.
-/
theorem pmfProb_bind_map_pair_joint_ge_one_sub
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (stateLaw : PMF State) (outcomeLaw : State → PMF Outcome)
    (stateGood : State → Prop) (outcomeGood : State → Outcome → Prop)
    [DecidablePred stateGood] [∀ state, DecidablePred (outcomeGood state)]
    (deltaState deltaOutcome : ℝ)
    (hdeltaState : 0 ≤ deltaState) (hdeltaOutcome : 0 ≤ deltaOutcome)
    (hdeltaOutcomeLeOne : deltaOutcome ≤ 1)
    (hstate : 1 - deltaState ≤ pmfProb stateLaw stateGood)
    (hconditional : ∀ state, stateGood state →
      1 - deltaOutcome ≤ pmfProb (outcomeLaw state) (outcomeGood state)) :
    1 - (deltaState + deltaOutcome) ≤
      pmfProb (stateLaw.bind fun state =>
        (outcomeLaw state).map fun outcome => (state, outcome))
        (fun stateOutcome => stateGood stateOutcome.1 ∧
          outcomeGood stateOutcome.1 stateOutcome.2) := by
  classical
  let conditionalProbability : State → ℝ := fun state =>
    pmfProb (outcomeLaw state) (outcomeGood state)
  have hpoint : ∀ state,
      (if stateGood state then 1 - deltaOutcome else 0) ≤
        (if stateGood state then conditionalProbability state else 0) := by
    intro state
    by_cases hgood : stateGood state
    · simpa [hgood, conditionalProbability] using hconditional state hgood
    · simp [hgood]
  have hconditionalExpectation :
      pmfExp stateLaw (fun state => if stateGood state then 1 - deltaOutcome else 0) ≤
        pmfExp stateLaw (fun state => if stateGood state then conditionalProbability state else 0) :=
    pmfExp_le_pmfExp_of_forall_le stateLaw _ _ hpoint
  have hindicatorExpectation :
      pmfExp stateLaw (fun state => if stateGood state then 1 - deltaOutcome else 0) =
        pmfProb stateLaw stateGood * (1 - deltaOutcome) := by
    calc
      pmfExp stateLaw (fun state => if stateGood state then 1 - deltaOutcome else 0) =
          pmfProb stateLaw stateGood * (1 - deltaOutcome) +
            (1 - pmfProb stateLaw stateGood) * 0 := by
              apply pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
              intro state
              rfl
      _ = _ := by ring
  have hjointRewrite :
      pmfProb (stateLaw.bind fun state =>
        (outcomeLaw state).map fun outcome => (state, outcome))
        (fun stateOutcome => stateGood stateOutcome.1 ∧
          outcomeGood stateOutcome.1 stateOutcome.2) =
        pmfExp stateLaw (fun state =>
          if stateGood state then conditionalProbability state else 0) := by
    rw [pmfProb_bind]
    apply pmfExp_congr
    intro state
    rw [pmfProb_map]
    by_cases hgood : stateGood state
    · simp [hgood, conditionalProbability]
    · simp [hgood]
  calc
    1 - (deltaState + deltaOutcome) ≤
        (1 - deltaState) * (1 - deltaOutcome) := by
          nlinarith [mul_nonneg hdeltaState hdeltaOutcome]
    _ ≤ pmfProb stateLaw stateGood * (1 - deltaOutcome) :=
      mul_le_mul_of_nonneg_right hstate (by linarith)
    _ = pmfExp stateLaw (fun state => if stateGood state then 1 - deltaOutcome else 0) :=
      hindicatorExpectation.symm
    _ ≤ pmfExp stateLaw (fun state => if stateGood state then conditionalProbability state else 0) :=
      hconditionalExpectation
    _ = _ := hjointRewrite.symm

/--
One adaptive failure step only needs its fresh-query bound on positive-mass
states of the preceding execution law.
-/
theorem adaptiveQueryFailureProbability_succ_le_of_support
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → ℝ)
    (hfailure : ∀ queryIndex (stateFailure : State × Bool),
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfProb (outcomeLaw queryIndex stateFailure.1)
        (bad queryIndex stateFailure.1) ≤ failureBudget queryIndex)
    (queryCount : ℕ) :
    adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad (queryCount + 1) ≤
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
        failureBudget queryCount := by
  let currentLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
  have hpoint : ∀ stateFailure ∈ currentLaw.support,
      pmfProb (outcomeLaw queryCount stateFailure.1)
          (fun outcome =>
            (stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)) = true) ≤
        (if stateFailure.2 = true then 1 else 0) + failureBudget queryCount := by
    rintro ⟨state, flag⟩ hsupport
    by_cases hflag : flag = true
    · have hbudgetNonneg : 0 ≤ failureBudget queryCount :=
        (pmfProb_nonneg (outcomeLaw queryCount state) (bad queryCount state)).trans
          (hfailure queryCount ⟨state, flag⟩ (by simpa [currentLaw] using hsupport))
      have hprobOne :
          pmfProb (outcomeLaw queryCount state) (fun _ : Outcome => True) = 1 :=
        by simp [pmfProb]
      simpa [hflag, hprobOne] using hbudgetNonneg
    · have hflagFalse : flag = false := Bool.eq_false_of_not_eq_true hflag
      simpa [hflagFalse] using
        (hfailure queryCount ⟨state, flag⟩ (by simpa [currentLaw] using hsupport))
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
      pmfExp_mono_of_support currentLaw hpoint
    _ = adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount +
        failureBudget queryCount := by
      rw [pmfExp_add, pmfExp_const]
      rfl

/-- An adaptive failure flag is absorbing, so its probability cannot decrease
after one additional query. -/
theorem adaptiveQueryFailureProbability_le_succ
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (queryCount : ℕ) :
    adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad queryCount ≤
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad (queryCount + 1) := by
  let currentLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
  change pmfProb currentLaw (fun stateFailure => stateFailure.2 = true) ≤
    pmfProb
      (currentLaw.bind fun stateFailure =>
        (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)))
      (fun stateFailure => stateFailure.2 = true)
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  change pmfExp currentLaw (fun stateFailure =>
      if stateFailure.2 = true then 1 else 0) ≤
    pmfExp currentLaw (fun stateFailure =>
      pmfProb (outcomeLaw queryCount stateFailure.1) (fun outcome =>
        (stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)) = true))
  apply pmfExp_mono_of_support
  rintro ⟨state, flag⟩ _
  cases flag with
  | false =>
      simpa using
        (pmfProb_nonneg (outcomeLaw queryCount state)
          (fun outcome => decide (bad queryCount state outcome) = true))
  | true => simp [pmfProb]

/-- The absorbing adaptive failure probability is monotone over finite query
prefixes. -/
theorem adaptiveQueryFailureProbability_mono
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)] :
    Monotone (adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance bad) := by
  intro first second hle
  induction second, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ second _ ih =>
      exact ih.trans (adaptiveQueryFailureProbability_le_succ
        initialStateLaw outcomeLaw advance bad second)

/--
The adaptive finite union bound with fresh-query estimates required only on
states in the support of each preceding adaptive execution law.
-/
theorem adaptiveQueryFailureProbability_le_sum_of_support
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → ℝ)
    (hfailure : ∀ queryIndex (stateFailure : State × Bool),
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfProb (outcomeLaw queryIndex stateFailure.1)
        (bad queryIndex stateFailure.1) ≤ failureBudget queryIndex) :
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
          adaptiveQueryFailureProbability_succ_le_of_support initialStateLaw outcomeLaw advance
            bad failureBudget hfailure queryCount
        _ ≤ (∑ queryIndex ∈ Finset.range queryCount, failureBudget queryIndex) +
            failureBudget queryCount := add_le_add ih (le_refl _)
        _ = ∑ queryIndex ∈ Finset.range (queryCount + 1), failureBudget queryIndex := by
          rw [Finset.sum_range_succ]

/-- The complementary support-restricted finite adaptive union bound. -/
theorem adaptiveQuerySuccessProbability_ge_one_sub_sum_of_support
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (failureBudget : ℕ → ℝ)
    (hfailure : ∀ queryIndex (stateFailure : State × Bool),
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfProb (outcomeLaw queryIndex stateFailure.1)
        (bad queryIndex stateFailure.1) ≤ failureBudget queryIndex)
    (queryCount : ℕ) :
    1 - ∑ queryIndex ∈ Finset.range queryCount, failureBudget queryIndex ≤
      pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => stateFailure.2 = false) := by
  have hfailureBound := adaptiveQueryFailureProbability_le_sum_of_support
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

/--
An invariant holds at every positive-mass adaptive-query state if it holds
initially and is preserved by each state update.  The failure flag is part of
the invariant when a caller tracks historywise error events.
-/
theorem adaptiveQueryStateLaw_support_invariant
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (invariant : ℕ → State → Bool → Prop)
    (hinitial : ∀ state ∈ initialStateLaw.support, invariant 0 state false)
    (hadvance : ∀ queryIndex state flag outcome,
      invariant queryIndex state flag →
      invariant (queryIndex + 1) (advance queryIndex state outcome)
        (flag || decide (bad queryIndex state outcome))) :
    ∀ queryCount stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support →
      invariant queryCount stateFailure.1 stateFailure.2 := by
  intro queryCount
  induction queryCount with
  | zero =>
      intro stateFailure hsupport
      change stateFailure ∈
        (initialStateLaw.map fun state => (state, false)).support at hsupport
      rcases (PMF.mem_support_map_iff (fun state => (state, false)) initialStateLaw
        stateFailure).mp hsupport with ⟨state, hstate, rfl⟩
      exact hinitial state hstate
  | succ queryCount ih =>
      intro stateFailure hsupport
      change stateFailure ∈
        ((adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).bind
          fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
            (advance queryCount stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryCount stateFailure.1 outcome))).support at hsupport
      rcases (PMF.mem_support_bind_iff
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)))
        stateFailure).mp hsupport with ⟨previous, hprevious, hnext⟩
      rcases (PMF.mem_support_map_iff
        (fun outcome =>
          (advance queryCount previous.1 outcome,
            previous.2 || decide (bad queryCount previous.1 outcome)))
        (outcomeLaw queryCount previous.1) stateFailure).mp hnext with
        ⟨outcome, _houtcome, hresult⟩
      rw [← hresult]
      exact hadvance queryCount previous.1 previous.2 outcome
        (ih previous hprevious)

/--
Support-restricted adaptive invariant induction.  A source execution need
only specify preservation for outcomes that its current kernel can actually
produce; this is essential for mixed deterministic/stochastic schedulers.
-/
theorem adaptiveQueryStateLaw_support_invariant_of_outcomeSupport
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (invariant : ℕ → State → Bool → Prop)
    (hinitial : ∀ state ∈ initialStateLaw.support, invariant 0 state false)
    (hadvance : ∀ queryIndex state flag outcome,
      invariant queryIndex state flag →
      outcome ∈ (outcomeLaw queryIndex state).support →
      invariant (queryIndex + 1) (advance queryIndex state outcome)
        (flag || decide (bad queryIndex state outcome))) :
    ∀ queryCount stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support →
      invariant queryCount stateFailure.1 stateFailure.2 := by
  intro queryCount
  induction queryCount with
  | zero =>
      intro stateFailure hsupport
      change stateFailure ∈
        (initialStateLaw.map fun state => (state, false)).support at hsupport
      rcases (PMF.mem_support_map_iff (fun state => (state, false)) initialStateLaw
        stateFailure).mp hsupport with ⟨state, hstate, rfl⟩
      exact hinitial state hstate
  | succ queryCount ih =>
      intro stateFailure hsupport
      change stateFailure ∈
        ((adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).bind
          fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
            (advance queryCount stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryCount stateFailure.1 outcome))).support at hsupport
      rcases (PMF.mem_support_bind_iff
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)))
        stateFailure).mp hsupport with ⟨previous, hprevious, hnext⟩
      rcases (PMF.mem_support_map_iff
        (fun outcome =>
          (advance queryCount previous.1 outcome,
            previous.2 || decide (bad queryCount previous.1 outcome)))
        (outcomeLaw queryCount previous.1) stateFailure).mp hnext with
        ⟨outcome, houtcome, hresult⟩
      rw [← hresult]
      exact hadvance queryCount previous.1 previous.2 outcome
        (ih previous hprevious) houtcome

/--
Update one common adaptive state while retaining a Boolean monitor for every
member of a finite index family.  Each coordinate records whether its own
history-level event has occurred; the base state is updated only once.
-/
noncomputable def adaptiveQueryIndexedMonitorAdvance
    {Index State Outcome : Type*}
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : Index → ℕ → State → Outcome → Prop)
    [∀ index queryIndex state outcome, Decidable (bad index queryIndex state outcome)] :
    AdaptiveStateUpdate (State × (Index → Bool)) Outcome :=
  fun queryIndex state outcome =>
    (advance queryIndex state.1 outcome,
      fun index => state.2 index || decide (bad index queryIndex state.1 outcome))

/--
Projecting a finite family of adaptive event monitors to one coordinate gives
exactly the ordinary adaptive failure process for that coordinate.  Thus a
finite union can be taken on one common history law rather than across
separately augmented executions.
-/
theorem adaptiveQueryStateLaw_indexedMonitor_projection_eq
    {Index State Outcome : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : Index → ℕ → State → Outcome → Prop)
    [∀ index queryIndex state outcome, Decidable (bad index queryIndex state outcome)]
    (index : Index) (queryCount : ℕ) :
    (adaptiveQueryStateLaw
        (initialStateLaw.map fun state => (state, fun _ => false))
        (fun queryIndex state => outcomeLaw queryIndex state.1)
        (adaptiveQueryIndexedMonitorAdvance advance bad)
        (fun _ _ _ => False)
        queryCount).map
      (fun stateFailure => (stateFailure.1.1, stateFailure.1.2 index)) =
      adaptiveQueryStateLaw initialStateLaw outcomeLaw advance (bad index) queryCount := by
  classical
  induction queryCount with
  | zero =>
      change ((initialStateLaw.map fun state => (state, fun _ => false)).map
        fun state => (state, false)).map
        (fun stateFailure => (stateFailure.1.1, stateFailure.1.2 index)) =
        initialStateLaw.map fun state => (state, false)
      rw [PMF.map_comp, PMF.map_comp]
      exact congrArg (fun stateMap => initialStateLaw.map stateMap) (by
        funext state
        simp [Function.comp_def])
  | succ queryCount ih =>
      let monitorLaw := adaptiveQueryStateLaw
        (initialStateLaw.map fun state => (state, fun _ => false))
        (fun currentQuery state => outcomeLaw currentQuery state.1)
        (adaptiveQueryIndexedMonitorAdvance advance bad)
        (fun _ _ _ => False)
        queryCount
      let individualLaw := adaptiveQueryStateLaw initialStateLaw outcomeLaw advance
        (bad index) queryCount
      let monitorStep : (State × (Index → Bool)) × Bool →
          PMF ((State × (Index → Bool)) × Bool) := fun stateFailure =>
        (outcomeLaw queryCount stateFailure.1.1).map fun outcome =>
          (adaptiveQueryIndexedMonitorAdvance advance bad queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (False))
      let individualStep : State × Bool → PMF (State × Bool) := fun stateFailure =>
        (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad index queryCount stateFailure.1 outcome))
      let projection : ((State × (Index → Bool)) × Bool) → State × Bool :=
        fun stateFailure => (stateFailure.1.1, stateFailure.1.2 index)
      have hstep : ∀ stateFailure,
          (monitorStep stateFailure).map projection =
            individualStep (projection stateFailure) := by
        intro stateFailure
        rw [PMF.map_comp]
        congr 1
      have hpreviousLaw : monitorLaw.map projection = individualLaw := by
        dsimp [monitorLaw, individualLaw, projection]
        exact ih
      change (monitorLaw.bind monitorStep).map projection =
        individualLaw.bind individualStep
      calc
        (monitorLaw.bind monitorStep).map projection =
            monitorLaw.bind (fun stateFailure => (monitorStep stateFailure).map projection) :=
              PMF.map_bind monitorLaw monitorStep projection
        _ = monitorLaw.bind (fun stateFailure => individualStep (projection stateFailure)) := by
              congr 1
              funext stateFailure
              exact hstep stateFailure
        _ = (monitorLaw.map projection).bind individualStep := by
              simpa only [Function.comp_apply] using
                (PMF.bind_map monitorLaw projection individualStep).symm
        _ = individualLaw.bind individualStep := by rw [hpreviousLaw]

/--
The terminal flag of one coordinate in the common indexed monitor has the
same probability as that coordinate's ordinary adaptive failure event.
-/
theorem adaptiveQueryStateLaw_indexedMonitor_coordinateFailure_eq
    {Index State Outcome : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : Index → ℕ → State → Outcome → Prop)
    [∀ index queryIndex state outcome, Decidable (bad index queryIndex state outcome)]
    (index : Index) (queryCount : ℕ) :
    pmfProb
      (adaptiveQueryStateLaw
        (initialStateLaw.map fun state => (state, fun _ => false))
        (fun queryIndex state => outcomeLaw queryIndex state.1)
        (adaptiveQueryIndexedMonitorAdvance advance bad)
        (fun _ _ _ => False)
        queryCount)
      (fun stateFailure => stateFailure.1.2 index = true) =
      adaptiveQueryFailureProbability initialStateLaw outcomeLaw advance (bad index) queryCount := by
  unfold adaptiveQueryFailureProbability
  rw [← adaptiveQueryStateLaw_indexedMonitor_projection_eq
    initialStateLaw outcomeLaw advance bad index queryCount]
  rw [pmfProb_map]

/--
If a coordinate of the indexed monitor is still false after one more query,
the immediately preceding query did not satisfy that coordinate's event.  The
conclusion also exposes the supported predecessor and outcome producing the
terminal base state, which lets paper-specific arguments read a last-step
event from a common monitored execution.
-/
theorem adaptiveQueryIndexedMonitor_support_coordinate_false_not_bad_at_last
    {Index State Outcome : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome)
    (bad : Index → ℕ → State → Outcome → Prop)
    [∀ index queryIndex state outcome, Decidable (bad index queryIndex state outcome)]
    (index : Index) (queryIndex : ℕ)
    (stateFailure : (State × (Index → Bool)) × Bool)
    (hsupport : stateFailure ∈
      (adaptiveQueryStateLaw
        (initialStateLaw.map fun state => (state, fun _ => false))
        (fun currentQuery state => outcomeLaw currentQuery state.1)
        (adaptiveQueryIndexedMonitorAdvance advance bad)
        (fun _ _ _ => False)
        (queryIndex + 1)).support)
    (hflag : stateFailure.1.2 index = false) :
    ∃ previous outcome,
      previous ∈
        (adaptiveQueryStateLaw
          (initialStateLaw.map fun state => (state, fun _ => false))
          (fun currentQuery state => outcomeLaw currentQuery state.1)
          (adaptiveQueryIndexedMonitorAdvance advance bad)
          (fun _ _ _ => False)
          queryIndex).support ∧
      outcome ∈ (outcomeLaw queryIndex previous.1.1).support ∧
      stateFailure.1.1 = advance queryIndex previous.1.1 outcome ∧
      ¬ bad index queryIndex previous.1.1 outcome := by
  change stateFailure ∈
      ((adaptiveQueryStateLaw
        (initialStateLaw.map fun state => (state, fun _ => false))
        (fun currentQuery state => outcomeLaw currentQuery state.1)
        (adaptiveQueryIndexedMonitorAdvance advance bad)
        (fun _ _ _ => False)
        queryIndex).bind fun previous =>
          (outcomeLaw queryIndex previous.1.1).map fun outcome =>
            (adaptiveQueryIndexedMonitorAdvance advance bad queryIndex previous.1 outcome,
              previous.2 || decide (False))).support at hsupport
  rcases (PMF.mem_support_bind_iff
    (adaptiveQueryStateLaw
      (initialStateLaw.map fun state => (state, fun _ => false))
      (fun currentQuery state => outcomeLaw currentQuery state.1)
      (adaptiveQueryIndexedMonitorAdvance advance bad)
      (fun _ _ _ => False)
      queryIndex)
    (fun previous =>
      (outcomeLaw queryIndex previous.1.1).map fun outcome =>
        (adaptiveQueryIndexedMonitorAdvance advance bad queryIndex previous.1 outcome,
          previous.2 || decide (False)))
    stateFailure).mp hsupport with ⟨previous, hprevious, hnext⟩
  rcases (PMF.mem_support_map_iff
    (fun outcome =>
      (adaptiveQueryIndexedMonitorAdvance advance bad queryIndex previous.1 outcome,
        previous.2 || decide (False)))
    (outcomeLaw queryIndex previous.1.1) stateFailure).mp hnext with
      ⟨outcome, houtcome, hstate⟩
  refine ⟨previous, outcome, hprevious, houtcome, ?_, ?_⟩
  · simpa [adaptiveQueryIndexedMonitorAdvance] using
      (congrArg (fun monitorFailure => monitorFailure.1.1) hstate).symm
  · intro hbad
    have hflagUpdate := congrArg (fun monitorFailure => monitorFailure.1.2 index) hstate
    change (previous.1.2 index || decide (bad index queryIndex previous.1.1 outcome)) =
      stateFailure.1.2 index at hflagUpdate
    have hflagTrue : stateFailure.1.2 index = true := by
      simpa [hbad] using (Eq.symm hflagUpdate)
    rw [hflag] at hflagTrue
    cases hflagTrue

end AppliedModelingLib.PreferenceRL
