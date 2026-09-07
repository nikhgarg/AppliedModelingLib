import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueries
import AppliedModelingLib.Foundations.Probability.FinitePinsker

/-!
# Finite adaptive concentration

This module supplies the paper-neutral exponential-supermartingale layer for
finite adaptive data collection.  A fresh outcome kernel may depend on the
entire current history.  Conditional centering and a pointwise increment
bound are therefore imposed history by history; no independence across rounds
is assumed.
-/

namespace AppliedModelingLib
namespace PreferenceRL

noncomputable section

/-- A zero-mean finite-PMF variable bounded in absolute value by `bound` has
the usual Hoeffding moment bound. -/
theorem pmfExp_exp_mul_le_exp_half_bound_sq_mul_sq
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (increment : Outcome → ℝ) (bound step : ℝ)
    (hbound : 0 ≤ bound)
    (hmean : pmfExp law increment = 0)
    (hincrement : ∀ outcome, |increment outcome| ≤ bound) :
    pmfExp law (fun outcome ↦ Real.exp (step * increment outcome)) ≤
      Real.exp (bound ^ 2 * step ^ 2 / 2) := by
  by_cases hboundZero : bound = 0
  · have hincrementZero : ∀ outcome, increment outcome = 0 := by
      intro outcome
      have habs : |increment outcome| = 0 :=
        le_antisymm (by simpa [hboundZero] using hincrement outcome) (abs_nonneg _)
      exact abs_eq_zero.mp habs
    simp [hincrementZero, hboundZero]
  · have hboundPos : 0 < bound := lt_of_le_of_ne hbound (Ne.symm hboundZero)
    let normalized : Outcome → ℝ := fun outcome ↦ increment outcome / bound
    have hnormalizedLower : ∀ outcome, -1 ≤ normalized outcome := by
      intro outcome
      have hlower : -bound ≤ increment outcome := (abs_le.mp (hincrement outcome)).1
      exact (le_div_iff₀ hboundPos).2 (by simpa using hlower)
    have hnormalizedUpper : ∀ outcome, normalized outcome ≤ 1 := by
      intro outcome
      have hupper : increment outcome ≤ bound := (abs_le.mp (hincrement outcome)).2
      exact (div_le_one hboundPos).2 hupper
    have hnormalizedMean : pmfExp law normalized = 0 := by
      dsimp [normalized]
      rw [show (fun outcome ↦ increment outcome / bound) =
          (fun outcome ↦ increment outcome * bound⁻¹) by
        funext outcome
        rw [div_eq_mul_inv]]
      rw [pmfExp_mul_const, hmean, zero_mul]
    have hmgf := finiteMGF_centered_le_exp_half_sq law normalized
      hnormalizedLower hnormalizedUpper (step * bound)
    rw [hnormalizedMean] at hmgf
    simp only [sub_zero] at hmgf
    calc
      pmfExp law (fun outcome ↦ Real.exp (step * increment outcome)) =
          Probability.finiteMGF law normalized (step * bound) := by
            unfold pmfExp Probability.finiteMGF
            apply Finset.sum_congr rfl
            intro outcome _
            congr 2
            dsimp [normalized]
            field_simp
      _ ≤ Real.exp ((step * bound) ^ 2 / 2) := hmgf
      _ = Real.exp (bound ^ 2 * step ^ 2 / 2) := by
        congr 1
        ring

/-- A time-indexed exponential potential transports through a finite adaptive
query process when its one-step conditional expectation contracts on every
reachable history. -/
theorem adaptiveQueryStateLaw_timeIndexedExpPotential_le_initial_of_support
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (potential : ℕ → State → ℝ)
    (hstep : ∀ queryIndex stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfExp (outcomeLaw queryIndex stateFailure.1)
          (fun outcome ↦ Real.exp
            (potential (queryIndex + 1) (advance queryIndex stateFailure.1 outcome))) ≤
        Real.exp (potential queryIndex stateFailure.1)) :
    ∀ queryCount,
      pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
          (fun stateFailure ↦ Real.exp (potential queryCount stateFailure.1)) ≤
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
  intro queryCount
  induction queryCount with
  | zero =>
      unfold adaptiveQueryStateLaw
      rw [pmfExp_map]
  | succ queryCount ih =>
      rw [adaptiveQueryStateLaw, pmfExp_bind]
      simp_rw [pmfExp_map]
      calc
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
            (fun stateFailure ↦
              pmfExp (outcomeLaw queryCount stateFailure.1)
                (fun outcome ↦ Real.exp
                  (potential (queryCount + 1)
                    (advance queryCount stateFailure.1 outcome)))) ≤
          pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
            (fun stateFailure ↦ Real.exp (potential queryCount stateFailure.1)) := by
              apply pmfExp_le_pmfExp_of_support_forall_le
              intro stateFailure hsupport
              exact hstep queryCount stateFailure hsupport
        _ ≤ pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := ih

/-- Fixed-horizon form of the preceding transport theorem.  The one-step
bound is required only before the requested terminal query. -/
theorem adaptiveQueryStateLaw_timeIndexedExpPotential_le_initial_of_support_up_to
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (potential : ℕ → State → ℝ) (queryCount : ℕ)
    (hstep : ∀ queryIndex, queryIndex < queryCount → ∀ stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfExp (outcomeLaw queryIndex stateFailure.1)
          (fun outcome ↦ Real.exp
            (potential (queryIndex + 1) (advance queryIndex stateFailure.1 outcome))) ≤
        Real.exp (potential queryIndex stateFailure.1)) :
    pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure ↦ Real.exp (potential queryCount stateFailure.1)) ≤
      pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
  induction queryCount with
  | zero =>
      unfold adaptiveQueryStateLaw
      rw [pmfExp_map]
  | succ queryCount ih =>
      rw [adaptiveQueryStateLaw, pmfExp_bind]
      simp_rw [pmfExp_map]
      calc
        pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
            (fun stateFailure ↦
              pmfExp (outcomeLaw queryCount stateFailure.1)
                (fun outcome ↦ Real.exp
                  (potential (queryCount + 1)
                    (advance queryCount stateFailure.1 outcome)))) ≤
          pmfExp (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
            (fun stateFailure ↦ Real.exp (potential queryCount stateFailure.1)) := by
              apply pmfExp_le_pmfExp_of_support_forall_le
              intro stateFailure hsupport
              exact hstep queryCount (Nat.lt_succ_self queryCount) stateFailure hsupport
        _ ≤ pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
          apply ih
          intro earlierQuery hearlier stateFailure hsupport
          exact hstep earlierQuery (by omega) stateFailure hsupport

/-- Fixed-horizon Markov inequality for a reachable-history exponential
potential. -/
theorem adaptiveQueryStateLaw_timeIndexedPotential_ge_probability_le
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (potential : ℕ → State → ℝ)
    (hstep : ∀ queryIndex stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfExp (outcomeLaw queryIndex stateFailure.1)
          (fun outcome ↦ Real.exp
            (potential (queryIndex + 1) (advance queryIndex stateFailure.1 outcome))) ≤
        Real.exp (potential queryIndex stateFailure.1))
    (queryCount : ℕ) (threshold : ℝ) :
    pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure ↦ threshold ≤ potential queryCount stateFailure.1) ≤
      Real.exp (-threshold) *
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
  let terminalLaw :=
    adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
  have hpoint : ∀ stateFailure : State × Bool,
      (if threshold ≤ potential queryCount stateFailure.1 then (1 : ℝ) else 0) ≤
        Real.exp (-threshold) * Real.exp (potential queryCount stateFailure.1) := by
    intro stateFailure
    by_cases hlarge : threshold ≤ potential queryCount stateFailure.1
    · rw [if_pos hlarge]
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (-threshold + potential queryCount stateFailure.1) := by
          exact Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (-threshold) * Real.exp (potential queryCount stateFailure.1) :=
          Real.exp_add _ _
    · simp only [if_neg hlarge]
      positivity
  calc
    pmfProb terminalLaw
        (fun stateFailure ↦ threshold ≤ potential queryCount stateFailure.1) =
      pmfExp terminalLaw
        (fun stateFailure ↦
          if threshold ≤ potential queryCount stateFailure.1 then (1 : ℝ) else 0) := rfl
    _ ≤ pmfExp terminalLaw
        (fun stateFailure ↦ Real.exp (-threshold) *
          Real.exp (potential queryCount stateFailure.1)) :=
      pmfExp_le_pmfExp_of_forall_le terminalLaw _ _ hpoint
    _ = Real.exp (-threshold) *
        pmfExp terminalLaw
          (fun stateFailure ↦ Real.exp (potential queryCount stateFailure.1)) := by
      rw [pmfExp_const_mul]
    _ ≤ Real.exp (-threshold) *
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
      gcongr
      exact adaptiveQueryStateLaw_timeIndexedExpPotential_le_initial_of_support
        initialStateLaw outcomeLaw advance bad potential hstep queryCount

/-- Fixed-horizon Markov tail whose local exponential contraction is required
only before the terminal query. -/
theorem adaptiveQueryStateLaw_timeIndexedPotential_ge_probability_le_up_to
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (potential : ℕ → State → ℝ) (queryCount : ℕ)
    (hstep : ∀ queryIndex, queryIndex < queryCount → ∀ stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryIndex).support →
      pmfExp (outcomeLaw queryIndex stateFailure.1)
          (fun outcome ↦ Real.exp
            (potential (queryIndex + 1) (advance queryIndex stateFailure.1 outcome))) ≤
        Real.exp (potential queryIndex stateFailure.1))
    (threshold : ℝ) :
    pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure ↦ threshold ≤ potential queryCount stateFailure.1) ≤
      Real.exp (-threshold) *
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
  let terminalLaw :=
    adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount
  have hpoint : ∀ stateFailure : State × Bool,
      (if threshold ≤ potential queryCount stateFailure.1 then (1 : ℝ) else 0) ≤
        Real.exp (-threshold) * Real.exp (potential queryCount stateFailure.1) := by
    intro stateFailure
    by_cases hlarge : threshold ≤ potential queryCount stateFailure.1
    · rw [if_pos hlarge]
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (-threshold + potential queryCount stateFailure.1) := by
          exact Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (-threshold) * Real.exp (potential queryCount stateFailure.1) :=
          Real.exp_add _ _
    · simp only [if_neg hlarge]
      positivity
  calc
    pmfProb terminalLaw
        (fun stateFailure ↦ threshold ≤ potential queryCount stateFailure.1) =
      pmfExp terminalLaw
        (fun stateFailure ↦
          if threshold ≤ potential queryCount stateFailure.1 then (1 : ℝ) else 0) := rfl
    _ ≤ pmfExp terminalLaw
        (fun stateFailure ↦ Real.exp (-threshold) *
          Real.exp (potential queryCount stateFailure.1)) :=
      pmfExp_le_pmfExp_of_forall_le terminalLaw _ _ hpoint
    _ = Real.exp (-threshold) *
        pmfExp terminalLaw
          (fun stateFailure ↦ Real.exp (potential queryCount stateFailure.1)) := by
      rw [pmfExp_const_mul]
    _ ≤ Real.exp (-threshold) *
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
      gcongr
      exact adaptiveQueryStateLaw_timeIndexedExpPotential_le_initial_of_support_up_to
        initialStateLaw outcomeLaw advance bad potential queryCount hstep

/-- A conditionally centered, bounded increment process induces the canonical
time-indexed Hoeffding potential. -/
theorem adaptiveQueryStateLaw_hoeffdingPotential_ge_probability_le
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (increment : ℕ → State → Outcome → ℝ)
    (bound : ℕ → State → ℝ) (potential : ℕ → State → ℝ)
    (hbound : ∀ queryIndex state, 0 ≤ bound queryIndex state)
    (hmean : ∀ queryIndex state,
      pmfExp (outcomeLaw queryIndex state) (increment queryIndex state) = 0)
    (hincrement : ∀ queryIndex state outcome,
      |increment queryIndex state outcome| ≤ bound queryIndex state)
    (hpotential : ∀ queryIndex state outcome,
      potential (queryIndex + 1) (advance queryIndex state outcome) =
        potential queryIndex state + increment queryIndex state outcome -
          (bound queryIndex state) ^ 2 / 2)
    (queryCount : ℕ) (threshold : ℝ) :
    pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure ↦ threshold ≤ potential queryCount stateFailure.1) ≤
      Real.exp (-threshold) *
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
  apply adaptiveQueryStateLaw_timeIndexedPotential_ge_probability_le
    initialStateLaw outcomeLaw advance bad potential ?_ queryCount threshold
  intro queryIndex stateFailure _hsupport
  let state := stateFailure.1
  let localBound := bound queryIndex state
  have hmgf :
      pmfExp (outcomeLaw queryIndex state)
          (fun outcome ↦ Real.exp (increment queryIndex state outcome)) ≤
        Real.exp (localBound ^ 2 / 2) := by
    simpa [localBound] using
      pmfExp_exp_mul_le_exp_half_bound_sq_mul_sq
        (outcomeLaw queryIndex state) (increment queryIndex state)
        localBound 1 (hbound queryIndex state) (hmean queryIndex state)
        (hincrement queryIndex state)
  have hrewrite :
      (fun outcome ↦ Real.exp
        (potential (queryIndex + 1) (advance queryIndex state outcome))) =
      fun outcome ↦
        Real.exp (potential queryIndex state - localBound ^ 2 / 2) *
          Real.exp (increment queryIndex state outcome) := by
    funext outcome
    rw [hpotential]
    rw [← Real.exp_add]
    congr 1
    dsimp [localBound]
    ring
  change pmfExp (outcomeLaw queryIndex state)
      (fun outcome ↦ Real.exp
        (potential (queryIndex + 1) (advance queryIndex state outcome))) ≤
    Real.exp (potential queryIndex state)
  rw [hrewrite, pmfExp_const_mul]
  calc
    Real.exp (potential queryIndex state - localBound ^ 2 / 2) *
        pmfExp (outcomeLaw queryIndex state)
          (fun outcome ↦ Real.exp (increment queryIndex state outcome)) ≤
      Real.exp (potential queryIndex state - localBound ^ 2 / 2) *
        Real.exp (localBound ^ 2 / 2) := by
          gcongr
    _ = Real.exp (potential queryIndex state) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Fixed-horizon Hoeffding-potential tail.  All conditional hypotheses are
needed only at the actual queries `0,…,queryCount-1`. -/
theorem adaptiveQueryStateLaw_hoeffdingPotential_ge_probability_le_up_to
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (increment : ℕ → State → Outcome → ℝ)
    (bound : ℕ → State → ℝ) (potential : ℕ → State → ℝ)
    (queryCount : ℕ)
    (hbound : ∀ queryIndex, queryIndex < queryCount → ∀ state,
      0 ≤ bound queryIndex state)
    (hmean : ∀ queryIndex, queryIndex < queryCount → ∀ state,
      pmfExp (outcomeLaw queryIndex state) (increment queryIndex state) = 0)
    (hincrement : ∀ queryIndex, queryIndex < queryCount → ∀ state outcome,
      |increment queryIndex state outcome| ≤ bound queryIndex state)
    (hpotential : ∀ queryIndex, queryIndex < queryCount → ∀ state outcome,
      potential (queryIndex + 1) (advance queryIndex state outcome) =
        potential queryIndex state + increment queryIndex state outcome -
          (bound queryIndex state) ^ 2 / 2)
    (threshold : ℝ) :
    pmfProb (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure ↦ threshold ≤ potential queryCount stateFailure.1) ≤
      Real.exp (-threshold) *
        pmfExp initialStateLaw (fun state ↦ Real.exp (potential 0 state)) := by
  apply adaptiveQueryStateLaw_timeIndexedPotential_ge_probability_le_up_to
    initialStateLaw outcomeLaw advance bad potential queryCount ?_ threshold
  intro queryIndex hquery stateFailure _hsupport
  let state := stateFailure.1
  let localBound := bound queryIndex state
  have hmgf :
      pmfExp (outcomeLaw queryIndex state)
          (fun outcome ↦ Real.exp (increment queryIndex state outcome)) ≤
        Real.exp (localBound ^ 2 / 2) := by
    simpa [localBound] using
      pmfExp_exp_mul_le_exp_half_bound_sq_mul_sq
        (outcomeLaw queryIndex state) (increment queryIndex state)
        localBound 1 (hbound queryIndex hquery state)
        (hmean queryIndex hquery state) (hincrement queryIndex hquery state)
  have hrewrite :
      (fun outcome ↦ Real.exp
        (potential (queryIndex + 1) (advance queryIndex state outcome))) =
      fun outcome ↦
        Real.exp (potential queryIndex state - localBound ^ 2 / 2) *
          Real.exp (increment queryIndex state outcome) := by
    funext outcome
    rw [hpotential queryIndex hquery]
    rw [← Real.exp_add]
    congr 1
    dsimp [localBound]
    ring
  change pmfExp (outcomeLaw queryIndex state)
      (fun outcome ↦ Real.exp
        (potential (queryIndex + 1) (advance queryIndex state outcome))) ≤
    Real.exp (potential queryIndex state)
  rw [hrewrite, pmfExp_const_mul]
  calc
    Real.exp (potential queryIndex state - localBound ^ 2 / 2) *
        pmfExp (outcomeLaw queryIndex state)
          (fun outcome ↦ Real.exp (increment queryIndex state outcome)) ≤
      Real.exp (potential queryIndex state - localBound ^ 2 / 2) *
        Real.exp (localBound ^ 2 / 2) := by
          gcongr
    _ = Real.exp (potential queryIndex state) := by
      rw [← Real.exp_add]
      congr 1
      ring

end

end PreferenceRL
end AppliedModelingLib
