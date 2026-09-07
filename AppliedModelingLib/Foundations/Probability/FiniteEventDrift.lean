import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import Mathlib.Tactic

/-!
# Finite-horizon drift bounds for IID finite-event dynamics

This module records the elementary finite-product calculation behind a
Lyapunov stopping argument.  A deterministic state update is driven by IID
draws from a finite event law.  A one-step expected descent inequality bounds
the expected accumulated nonnegative cost at every finite horizon.  No
stationary distribution or infinite-time stopping theorem is assumed here.
-/

namespace AppliedModelingLib.Probability

open scoped BigOperators

noncomputable section

variable {State Event : Type*} [Fintype Event] [DecidableEq Event]

/-- State reached after a finite sequence of events, with the last coordinate
of `Fin (n + 1)` interpreted as the newest event. -/
def finiteEventTrajectory (initial : State) (step : State → Event → State) :
    (n : ℕ) → (Fin n → Event) → State
  | 0, _ => initial
  | n + 1, sample =>
      step (finiteEventTrajectory initial step n (fun i => sample i.castSucc))
        (sample (Fin.last n))

/-- A one-step invariant holds at every finite horizon of the literal event
trajectory.  This deterministic induction is deliberately separate from the
IID drift results below, so it can also certify structural properties of a
regenerative state before any expectation is taken. -/
theorem finiteEventTrajectory_invariant
    {P : State → Prop} (initial : State) (step : State → Event → State)
    (hinitial : P initial)
    (hstep : ∀ state event, P state → P (step state event))
    (n : ℕ) (sample : Fin n → Event) :
    P (finiteEventTrajectory initial step n sample) := by
  induction n with
  | zero => simpa [finiteEventTrajectory] using hinitial
  | succ n ih =>
      simp only [finiteEventTrajectory]
      exact hstep _ _ (ih (fun i => sample i.castSucc))

/-- Extending a finite event history by one newest event has exactly the
recursive trajectory interpretation. -/
theorem finiteEventTrajectory_succ_extendDraw
    (initial : State) (step : State → Event → State)
    (n : ℕ) (sample : Fin n → Event) (event : Event) :
    finiteEventTrajectory initial step (n + 1)
      (fun j => extendDraw sample event ((optionFinEquivFinSucc n).symm j)) =
      step (finiteEventTrajectory initial step n sample) event := by
  simp [finiteEventTrajectory, extendDraw, optionFinEquivFinSucc]

/-- A literal infinite event stream gives the same next state whether its
prefix is presented as a block of length `n + 1` or as the old block followed
by its next coordinate.  This is the pathwise recursion used when a finite
regenerative excursion is telescoped before taking expectations. -/
theorem finiteEventTrajectory_succ_block
    (initial : State) (step : State → Event → State)
    (n : ℕ) (omega : ℕ → Event) :
    finiteEventTrajectory initial step (n + 1) (IIDStream.block 0 (n + 1) omega) =
      step (finiteEventTrajectory initial step n (IIDStream.block 0 n omega)) (omega n) := by
  rw [show IIDStream.block 0 (n + 1) omega =
      fun j => extendDraw (IIDStream.block 0 n omega) (omega n)
        ((optionFinEquivFinSucc n).symm j) by
    funext j
    by_cases hlast : j = Fin.last n
    · subst j
      simp [IIDStream.block, IIDStream.coordinate, extendDraw,
        optionFinEquivFinSucc]
    · simp [IIDStream.block, IIDStream.coordinate, extendDraw,
        optionFinEquivFinSucc, hlast]]
  exact finiteEventTrajectory_succ_extendDraw initial step n
    (IIDStream.block 0 n omega) (omega n)

/-- The change of any real state observable along a literal finite IID-event
prefix telescopes exactly.  No stopping, recurrence, or limit exchange is
used: this is a finite path identity. -/
theorem sum_range_finiteEventTrajectory_increment
    (initial : State) (step : State → Event → State)
    (observable : State → ℝ) (horizon : ℕ) (omega : ℕ → Event) :
    ∑ n ∈ Finset.range horizon,
      (observable (finiteEventTrajectory initial step (n + 1)
        (IIDStream.block 0 (n + 1) omega)) -
        observable (finiteEventTrajectory initial step n (IIDStream.block 0 n omega))) =
      observable (finiteEventTrajectory initial step horizon (IIDStream.block 0 horizon omega)) -
        observable initial := by
  induction horizon with
  | zero => simp [finiteEventTrajectory]
  | succ horizon ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ n ∈ Finset.range horizon,
            (observable (finiteEventTrajectory initial step (n + 1)
              (IIDStream.block 0 (n + 1) omega)) -
              observable (finiteEventTrajectory initial step n
                (IIDStream.block 0 n omega))) ) +
            (observable (finiteEventTrajectory initial step (horizon + 1)
              (IIDStream.block 0 (horizon + 1) omega)) -
              observable (finiteEventTrajectory initial step horizon
                (IIDStream.block 0 horizon omega))) =
            (observable (finiteEventTrajectory initial step horizon
              (IIDStream.block 0 horizon omega)) - observable initial) +
              (observable (finiteEventTrajectory initial step (horizon + 1)
                (IIDStream.block 0 (horizon + 1) omega)) -
                observable (finiteEventTrajectory initial step horizon
                  (IIDStream.block 0 horizon omega))) := by rw [ih]
        _ = observable (finiteEventTrajectory initial step (horizon + 1)
              (IIDStream.block 0 (horizon + 1) omega)) - observable initial := by ring

/-- One IID event step factors a finite-horizon trajectory expectation into
the previous event history and one independent newest event. -/
theorem pmfExp_finiteEventTrajectory_succ
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential : State → ℝ) (n : ℕ) :
    pmfExp (pmfProduct (Fin (n + 1)) Event law)
        (fun sample => potential (finiteEventTrajectory initial step (n + 1) sample)) =
      pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => pmfExp law
          (fun event => potential (step (finiteEventTrajectory initial step n sample) event))) := by
  let F : (Fin (n + 1) → Event) → ℝ := fun sample =>
    potential (finiteEventTrajectory initial step (n + 1) sample)
  let Foption : (Option (Fin n) → Event) → ℝ := fun sample =>
    F (fun j => sample ((optionFinEquivFinSucc n).symm j))
  calc
    pmfExp (pmfProduct (Fin (n + 1)) Event law) F =
        pmfExp (pmfProduct (Option (Fin n)) Event law) Foption := by
            exact (pmfExp_pmfProduct_equiv (optionFinEquivFinSucc n) law F).symm
    _ = pmfPairExp (pmfProduct (Fin n) Event law) law
          (fun sample event => Foption (extendDraw sample event)) := by
            exact pmfExp_pmfProduct_option_eq_pairExp law Foption
    _ = pmfExp (pmfProduct (Fin n) Event law)
          (fun sample => pmfExp law
            (fun event => potential
              (step (finiteEventTrajectory initial step n sample) event))) := by
            unfold pmfPairExp
            apply pmfExp_congr
            intro sample
            apply pmfExp_congr
            intro event
            simpa [Foption, F] using
              congrArg potential
                (finiteEventTrajectory_succ_extendDraw initial step n sample event)

/-- The expected accumulated state cost through a finite IID event horizon. -/
noncomputable def finiteEventExpectedCumulativeCost
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (cost : State → ℝ) (horizon : ℕ) : ℝ :=
  ∑ n ∈ Finset.range horizon,
    pmfExp (pmfProduct (Fin n) Event law)
      (fun sample => cost (finiteEventTrajectory initial step n sample))

/-- The finite-product probability that a state predicate holds after `n`
IID events. -/
noncomputable def finiteEventTrajectoryEventProbability
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (event : State → Prop) [DecidablePred event] (n : ℕ) : ℝ :=
  pmfExp (pmfProduct (Fin n) Event law)
    (fun sample => if event (finiteEventTrajectory initial step n sample) then 1 else 0)

/-- A finite-product state-event probability is nonnegative. -/
theorem finiteEventTrajectoryEventProbability_nonneg
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (event : State → Prop) [DecidablePred event] (n : ℕ) :
    0 ≤ finiteEventTrajectoryEventProbability law initial step event n := by
  exact pmfProb_nonneg _ _

/-- A one-step drift inequality controls potential plus the expected current
cost.  The statement is finite-horizon and therefore requires no recurrence
or integrability premise on an infinite path. -/
theorem finiteEventTrajectory_expected_potential_add_cost_le
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ)
    (hstep : ∀ state,
      pmfExp law (fun event => potential (step state event)) + cost state ≤ potential state)
    (n : ℕ) :
    pmfExp (pmfProduct (Fin (n + 1)) Event law)
        (fun sample => potential (finiteEventTrajectory initial step (n + 1) sample)) +
      pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => cost (finiteEventTrajectory initial step n sample)) ≤
      pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => potential (finiteEventTrajectory initial step n sample)) := by
  rw [pmfExp_finiteEventTrajectory_succ]
  rw [← pmfExp_add]
  apply pmfExp_le_pmfExp_of_forall_le
  intro sample
  exact hstep (finiteEventTrajectory initial step n sample)

/-- An exact one-step drift identity lifts to the corresponding finite-product
trajectory identity.  This is the equality counterpart to the Lyapunov bound
above and is useful when a generator calculation is later summed only over a
deterministic finite horizon. -/
theorem finiteEventTrajectory_expected_potential_add_cost_eq
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ)
    (hstep : ∀ state,
      pmfExp law (fun event => potential (step state event)) + cost state = potential state)
    (n : ℕ) :
    pmfExp (pmfProduct (Fin (n + 1)) Event law)
        (fun sample => potential (finiteEventTrajectory initial step (n + 1) sample)) +
      pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => cost (finiteEventTrajectory initial step n sample)) =
      pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => potential (finiteEventTrajectory initial step n sample)) := by
  rw [pmfExp_finiteEventTrajectory_succ]
  rw [← pmfExp_add]
  apply pmfExp_congr
  intro sample
  exact hstep (finiteEventTrajectory initial step n sample)

/-- Exact finite-horizon drift accounting.  No recurrence, stopping-time, or
limit interchange is hidden here: this only telescopes the one-step equality
over a prescribed finite number of IID events. -/
theorem finiteEventExpectedCumulativeCost_add_expectedPotential_eq_initial
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ)
    (hstep : ∀ state,
      pmfExp law (fun event => potential (step state event)) + cost state = potential state)
    (horizon : ℕ) :
    finiteEventExpectedCumulativeCost law initial step cost horizon +
      pmfExp (pmfProduct (Fin horizon) Event law)
        (fun sample => potential (finiteEventTrajectory initial step horizon sample)) =
      potential initial := by
  induction horizon with
  | zero =>
      simp [finiteEventExpectedCumulativeCost, finiteEventTrajectory]
  | succ horizon ih =>
      rw [finiteEventExpectedCumulativeCost, Finset.sum_range_succ]
      have hstepHorizon := finiteEventTrajectory_expected_potential_add_cost_eq
        law initial step potential cost hstep horizon
      calc
        (∑ n ∈ Finset.range horizon,
            pmfExp (pmfProduct (Fin n) Event law)
              (fun sample => cost (finiteEventTrajectory initial step n sample))) +
            pmfExp (pmfProduct (Fin horizon) Event law)
              (fun sample => cost (finiteEventTrajectory initial step horizon sample)) +
            pmfExp (pmfProduct (Fin (horizon + 1)) Event law)
              (fun sample => potential
                (finiteEventTrajectory initial step (horizon + 1) sample)) =
          (∑ n ∈ Finset.range horizon,
            pmfExp (pmfProduct (Fin n) Event law)
              (fun sample => cost (finiteEventTrajectory initial step n sample))) +
            (pmfExp (pmfProduct (Fin (horizon + 1)) Event law)
              (fun sample => potential
                (finiteEventTrajectory initial step (horizon + 1) sample)) +
            pmfExp (pmfProduct (Fin horizon) Event law)
              (fun sample => cost (finiteEventTrajectory initial step horizon sample))) := by
            ring
        _ = (∑ n ∈ Finset.range horizon,
            pmfExp (pmfProduct (Fin n) Event law)
              (fun sample => cost (finiteEventTrajectory initial step n sample))) +
            pmfExp (pmfProduct (Fin horizon) Event law)
              (fun sample => potential (finiteEventTrajectory initial step horizon sample)) := by
            rw [hstepHorizon]
        _ = potential initial := ih

/-- Finite-horizon Lyapunov accounting: a nonnegative potential and a
one-step expected descent inequality bound every expected cumulative cost by
the initial potential. -/
theorem finiteEventExpectedCumulativeCost_le_initialPotential
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ)
    (hpotential_nonneg : ∀ state, 0 ≤ potential state)
    (hstep : ∀ state,
      pmfExp law (fun event => potential (step state event)) + cost state ≤ potential state)
    (horizon : ℕ) :
    finiteEventExpectedCumulativeCost law initial step cost horizon ≤ potential initial := by
  have haccount : ∀ n : ℕ,
      pmfExp (pmfProduct (Fin n) Event law)
          (fun sample => potential (finiteEventTrajectory initial step n sample)) +
        finiteEventExpectedCumulativeCost law initial step cost n ≤ potential initial := by
    intro n
    induction n with
    | zero =>
        simp [finiteEventExpectedCumulativeCost, finiteEventTrajectory]
    | succ n ih =>
        rw [finiteEventExpectedCumulativeCost, Finset.sum_range_succ]
        have hstepn := finiteEventTrajectory_expected_potential_add_cost_le
          law initial step potential cost hstep n
        calc
          pmfExp (pmfProduct (Fin (n + 1)) Event law)
              (fun sample => potential (finiteEventTrajectory initial step (n + 1) sample)) +
            ((∑ k ∈ Finset.range n,
              pmfExp (pmfProduct (Fin k) Event law)
                (fun sample => cost (finiteEventTrajectory initial step k sample))) +
              pmfExp (pmfProduct (Fin n) Event law)
                (fun sample => cost (finiteEventTrajectory initial step n sample))) =
            (pmfExp (pmfProduct (Fin (n + 1)) Event law)
                (fun sample => potential (finiteEventTrajectory initial step (n + 1) sample)) +
              pmfExp (pmfProduct (Fin n) Event law)
                (fun sample => cost (finiteEventTrajectory initial step n sample))) +
              ∑ k ∈ Finset.range n,
                pmfExp (pmfProduct (Fin k) Event law)
                  (fun sample => cost (finiteEventTrajectory initial step k sample)) := by ring
          _ ≤ pmfExp (pmfProduct (Fin n) Event law)
                (fun sample => potential (finiteEventTrajectory initial step n sample)) +
              ∑ k ∈ Finset.range n,
                pmfExp (pmfProduct (Fin k) Event law)
                  (fun sample => cost (finiteEventTrajectory initial step k sample)) := by
                gcongr
          _ ≤ potential initial := by
                simpa [finiteEventExpectedCumulativeCost] using ih
  have hnonneg : 0 ≤
      pmfExp (pmfProduct (Fin horizon) Event law)
        (fun sample => potential (finiteEventTrajectory initial step horizon sample)) := by
    apply Finset.sum_nonneg
    intro sample _
    exact mul_nonneg ENNReal.toReal_nonneg
      (hpotential_nonneg (finiteEventTrajectory initial step horizon sample))
  linarith [haccount horizon]

/-- A finite-horizon drift bound controls the cumulative probability of a
charged state event.  This is the quantitative form of the finite-event
Lyapunov estimate. -/
theorem sum_range_finiteEventTrajectoryEventProbability_le_initialPotential_div_charge
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ) (event : State → Prop) [DecidablePred event]
    (charge : ℝ) (hcharge : 0 < charge)
    (hpotential_nonneg : ∀ state, 0 ≤ potential state)
    (hstep : ∀ state,
      pmfExp law (fun draw => potential (step state draw)) + cost state ≤ potential state)
    (hcost : ∀ state, cost state = charge * (if event state then 1 else 0))
    (horizon : ℕ) :
    ∑ n ∈ Finset.range horizon,
      finiteEventTrajectoryEventProbability law initial step event n ≤
        potential initial / charge := by
  have hbound := finiteEventExpectedCumulativeCost_le_initialPotential
    law initial step potential cost hpotential_nonneg hstep horizon
  have hrewrite : finiteEventExpectedCumulativeCost law initial step cost horizon =
      charge * ∑ n ∈ Finset.range horizon,
        finiteEventTrajectoryEventProbability law initial step event n := by
    unfold finiteEventExpectedCumulativeCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => cost (finiteEventTrajectory initial step n sample)) =
        pmfExp (pmfProduct (Fin n) Event law)
          (fun sample => charge *
            (if event (finiteEventTrajectory initial step n sample) then 1 else 0)) by
          apply pmfExp_congr
          intro sample
          exact hcost (finiteEventTrajectory initial step n sample)]
    exact pmfExp_const_mul _ charge _
  rw [hrewrite] at hbound
  have hinitial : 0 ≤ potential initial := hpotential_nonneg initial
  apply (le_div_iff₀ hcharge).mpr
  linarith

/-- A strictly positive fixed charge on a state event makes its finite-product
probabilities summable whenever the associated Lyapunov cost is controlled.
This is the finite-dimensional tail estimate that later connects to an IID
prefix stopping argument. -/
theorem summable_finiteEventTrajectoryEventProbability_of_drift
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ) (event : State → Prop) [DecidablePred event]
    (charge : ℝ) (hcharge : 0 < charge)
    (hpotential_nonneg : ∀ state, 0 ≤ potential state)
    (hstep : ∀ state,
      pmfExp law (fun draw => potential (step state draw)) + cost state ≤ potential state)
    (hcost : ∀ state, cost state = charge * (if event state then 1 else 0)) :
    Summable (finiteEventTrajectoryEventProbability law initial step event) := by
  apply summable_of_sum_range_le
  · intro n
    exact finiteEventTrajectoryEventProbability_nonneg law initial step event n
  · intro horizon
    exact sum_range_finiteEventTrajectoryEventProbability_le_initialPotential_div_charge
      law initial step potential cost event charge hcharge hpotential_nonneg hstep hcost horizon

/-- The expected total number of charged event horizons is bounded by the
initial Lyapunov potential divided by the per-event charge. -/
theorem tsum_finiteEventTrajectoryEventProbability_le_initialPotential_div_charge
    (law : PMF Event) (initial : State) (step : State → Event → State)
    (potential cost : State → ℝ) (event : State → Prop) [DecidablePred event]
    (charge : ℝ) (hcharge : 0 < charge)
    (hpotential_nonneg : ∀ state, 0 ≤ potential state)
    (hstep : ∀ state,
      pmfExp law (fun draw => potential (step state draw)) + cost state ≤ potential state)
    (hcost : ∀ state, cost state = charge * (if event state then 1 else 0)) :
    ∑' n, finiteEventTrajectoryEventProbability law initial step event n ≤
      potential initial / charge := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact finiteEventTrajectoryEventProbability_nonneg law initial step event n
  · intro horizon
    exact sum_range_finiteEventTrajectoryEventProbability_le_initialPotential_div_charge
      law initial step potential cost event charge hcharge hpotential_nonneg hstep hcost horizon

end

end AppliedModelingLib.Probability
