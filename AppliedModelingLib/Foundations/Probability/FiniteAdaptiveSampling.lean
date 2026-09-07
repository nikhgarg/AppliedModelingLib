import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite Adaptive Fresh Sampling

A finite PMF construction for one adaptive round: first sample a current state,
then draw an IID data batch from the PMF selected by that state.  The resulting
joint law preserves the state marginal and satisfies the expected conditional
sampling identity needed by finite-horizon adaptive algorithms.
-/

namespace AppliedModelingLib

/--
Joint law of a current state and a fresh IID batch whose data PMF is selected
by that state.  The data batch is conditionally IID, but generally not
independent of the state.
-/
noncomputable def adaptiveFreshProductLaw
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (stateLaw : PMF State) (dataLaw : State → PMF Data) :
    PMF (State × (BatchIndex → Data)) :=
  stateLaw.bind fun state =>
    (pmfProduct BatchIndex Data (dataLaw state)).map fun batch => (state, batch)

/-- The adaptive fresh-sampling law has the prescribed current-state marginal. -/
theorem adaptiveFreshProductLaw_fst_marginal
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (stateLaw : PMF State) (dataLaw : State → PMF Data) :
    (adaptiveFreshProductLaw stateLaw dataLaw (BatchIndex := BatchIndex)).map Prod.fst = stateLaw := by
  unfold adaptiveFreshProductLaw
  rw [PMF.map_bind]
  calc
    stateLaw.bind (fun state =>
        PMF.map Prod.fst (PMF.map (fun batch => (state, batch))
          (pmfProduct BatchIndex Data (dataLaw state)))) = stateLaw.bind PMF.pure := by
      congr 1
      funext state
      rw [PMF.map_comp]
      change PMF.map (fun _ : BatchIndex → Data => state) (pmfProduct BatchIndex Data (dataLaw state)) =
        PMF.pure state
      exact PMF.map_const _ state
    _ = stateLaw := PMF.bind_pure stateLaw

/--
Expectation under an adaptive fresh-sampling law is the expectation over the
current state of the IID-batch expectation selected at that state.
-/
theorem pmfExp_adaptiveFreshProductLaw
    {State Data BatchIndex : Type*}
    [Fintype State] [DecidableEq State] [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (stateLaw : PMF State) (dataLaw : State → PMF Data)
    (statistic : State × (BatchIndex → Data) → ℝ) :
    pmfExp (adaptiveFreshProductLaw stateLaw dataLaw) statistic =
      pmfExp stateLaw (fun state =>
        pmfExp (pmfProduct BatchIndex Data (dataLaw state))
          (fun batch => statistic (state, batch))) := by
  unfold adaptiveFreshProductLaw
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro state
  simpa [Function.comp_def] using
    (pmfExp_map (pmfProduct BatchIndex Data (dataLaw state))
      (fun batch => (state, batch)) statistic)

/--
Law of the next adaptive state after applying a deterministic update to the
current state and its fresh conditionally IID batch.
-/
noncomputable def adaptiveFreshStepLaw
    {State NextState Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (stateLaw : PMF State) (dataLaw : State → PMF Data)
    (update : State → (BatchIndex → Data) → NextState) : PMF NextState :=
  (adaptiveFreshProductLaw stateLaw dataLaw).map fun pair => update pair.1 pair.2

/--
Expectation after an adaptive fresh step first averages the deterministic
update over the fresh IID batch conditional on the current state.
-/
theorem pmfExp_adaptiveFreshStepLaw
    {State NextState Data BatchIndex : Type*}
    [Fintype State] [DecidableEq State] [Fintype NextState] [DecidableEq NextState]
    [Fintype Data] [DecidableEq Data] [Fintype BatchIndex] [DecidableEq BatchIndex]
    (stateLaw : PMF State) (dataLaw : State → PMF Data)
    (update : State → (BatchIndex → Data) → NextState) (statistic : NextState → ℝ) :
    pmfExp (adaptiveFreshStepLaw stateLaw dataLaw update) statistic =
      pmfExp stateLaw (fun state =>
        pmfExp (pmfProduct BatchIndex Data (dataLaw state))
          (fun batch => statistic (update state batch))) := by
  unfold adaptiveFreshStepLaw
  rw [pmfExp_map]
  exact pmfExp_adaptiveFreshProductLaw stateLaw dataLaw
    (fun pair => statistic (update pair.1 pair.2))

/--
Successive adaptive state laws: every transition draws a new conditionally IID
batch from the PMF selected by the random current state.
-/
noncomputable def adaptiveFreshIterateLaw
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (update : State → (BatchIndex → Data) → State) : ℕ → PMF State
  | 0 => initialLaw
  | iteration + 1 => adaptiveFreshStepLaw (adaptiveFreshIterateLaw initialLaw dataLaw update iteration)
      dataLaw update

/-- Unfolding equation for one fresh adaptive transition. -/
theorem adaptiveFreshIterateLaw_succ
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (update : State → (BatchIndex → Data) → State) (iteration : ℕ) :
    adaptiveFreshIterateLaw initialLaw dataLaw update (iteration + 1) =
    adaptiveFreshStepLaw (adaptiveFreshIterateLaw initialLaw dataLaw update iteration) dataLaw update := rfl

/--
Law of a complete finite adaptive batch trace. At round `n`, the fresh IID
batch is drawn from the data PMF selected by the state determined from the
preceding `n` batches.
-/
noncomputable def adaptiveFreshTraceLaw
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State) :
    (iteration : ℕ) → PMF (Fin iteration → BatchIndex → Data)
  | 0 => PMF.pure Fin.elim0
  | iteration + 1 =>
      (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration).bind fun history =>
        (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history))).map
          (fun batch => Fin.snoc history batch)

/--
One trace-extension equation: an adaptive trace is sampled by first drawing
its history and then an IID batch from the history-selected data law.
-/
theorem pmfExp_adaptiveFreshTraceLaw_succ
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (iteration : ℕ) (statistic : (Fin (iteration + 1) → BatchIndex → Data) → ℝ) :
    pmfExp (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1)) statistic =
      pmfExp (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration) (fun history =>
        pmfExp (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history)))
          (fun batch => statistic (Fin.snoc history batch))) := by
  change pmfExp
      ((adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration).bind fun history =>
        (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history))).map
          (fun batch => Fin.snoc history batch)) statistic = _
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro history
  simpa [Function.comp_def] using
    (pmfExp_map (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history)))
      (fun batch => Fin.snoc history batch) statistic)

/--
Dropping the newest batch from an adaptive trace recovers exactly the previous
trace law.  Thus later finite-horizon events can be compared on one common
batch-history probability space.
-/
theorem adaptiveFreshTraceLaw_init_marginal
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (iteration : ℕ) :
    (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1)).map Fin.init =
      adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration := by
  change PMF.map Fin.init
      ((adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration).bind fun history =>
        (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history))).map
          (fun batch : BatchIndex → Data =>
            @Fin.snoc iteration (fun _ => BatchIndex → Data) history batch)) = _
  rw [PMF.map_bind]
  calc
    (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration).bind (fun history =>
        PMF.map Fin.init
          (PMF.map (fun batch : BatchIndex → Data =>
            @Fin.snoc iteration (fun _ => BatchIndex → Data) history batch)
            (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history))))) =
      (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration).bind PMF.pure := by
        congr 1
        funext history
        have hcompose : Fin.init ∘
            (fun batch : BatchIndex → Data =>
              @Fin.snoc iteration (fun _ => BatchIndex → Data) history batch) =
            (fun _ : BatchIndex → Data => history) := by
          funext batch
          simp
        rw [PMF.map_comp]
        rw [hcompose]
        exact PMF.map_const _ history
    _ = adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration := PMF.bind_pure _

/--
Probability of a next-round trace event is the current-history expectation of
the event's conditional IID-batch probability.
-/
theorem pmfProb_adaptiveFreshTraceLaw_succ
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (iteration : ℕ) (event : (Fin (iteration + 1) → BatchIndex → Data) → Prop)
    [DecidablePred event] :
    pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1)) event =
      pmfExp (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration) (fun history =>
        pmfProb (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history)))
          (fun batch => event (Fin.snoc history batch))) := by
  classical
  unfold pmfProb
  simpa using pmfExp_adaptiveFreshTraceLaw_succ initialLaw dataLaw stateOfHistory iteration
    (fun trace => if event trace then (1 : ℝ) else 0)

/--
A uniform bound on the conditional IID failure probability controls the same
event after an adaptive fresh-sampling transition.
-/
theorem pmfProb_adaptiveFreshTraceLaw_succ_le_of_forall
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (iteration : ℕ) (event : (Fin (iteration + 1) → BatchIndex → Data) → Prop)
    [DecidablePred event]
    (failure : ℝ)
    (hfailure : ∀ history,
      pmfProb (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history)))
        (fun batch => event (Fin.snoc history batch)) ≤ failure) :
    pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1)) event ≤
      failure := by
  classical
  rw [pmfProb_adaptiveFreshTraceLaw_succ]
  calc
    pmfExp (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration) (fun history =>
        pmfProb (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history)))
          (fun batch => event (Fin.snoc history batch))) ≤
      pmfExp (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration) (fun _ => failure) :=
      pmfExp_le_pmfExp_of_forall_le _ _ _ hfailure
    _ = failure := pmfExp_const _ failure

/--
The event that one of the batches in an adaptive trace is bad, where the
current batch event may depend on its entire preceding history.
-/
def adaptiveFreshTraceAnyBadEvent
    {Data BatchIndex : Type*}
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop) :
    ∀ iteration, (Fin iteration → BatchIndex → Data) → Prop
  | 0 => fun _ => False
  | iteration + 1 => fun trace =>
      adaptiveFreshTraceAnyBadEvent bad iteration (Fin.init trace) ∨
      bad iteration (Fin.init trace) (trace (Fin.last iteration))

/-- The conditional fresh-batch probability of a history-dependent bad event. -/
noncomputable def adaptiveFreshConditionalBadProbability
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop)
    (iteration : ℕ) (history : Fin iteration → BatchIndex → Data) : ℝ := by
  classical
  letI : DecidablePred (bad iteration history) := Classical.decPred _
  exact pmfProb (pmfProduct BatchIndex Data (dataLaw (stateOfHistory iteration history)))
    (bad iteration history)

/-- The finite-PMF probability that an adaptive trace contains a bad batch. -/
noncomputable def adaptiveFreshTraceAnyBadProbability
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop)
    (iteration : ℕ) : ℝ := by
  classical
  letI : DecidablePred (adaptiveFreshTraceAnyBadEvent bad iteration) := Classical.decPred _
  exact pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration)
    (adaptiveFreshTraceAnyBadEvent bad iteration)

/-- Every finite adaptive-trace bad-event probability is nonnegative. -/
theorem adaptiveFreshTraceAnyBadProbability_nonneg
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop)
    (iteration : ℕ) :
    0 ≤ adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad iteration := by
  classical
  unfold adaptiveFreshTraceAnyBadProbability
  exact pmfProb_nonneg _ _

/--
One adaptive trace extension increases the probability of any bad batch by at
most a uniform bound on its history-conditional fresh-batch failure event.
-/
theorem adaptiveFreshTraceAnyBadProbability_succ_le
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop)
    (iteration : ℕ) (failure : ℝ)
    (hfailure : ∀ history,
      adaptiveFreshConditionalBadProbability dataLaw stateOfHistory bad iteration history ≤ failure) :
    adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad (iteration + 1) ≤
      adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad iteration + failure := by
  classical
  unfold adaptiveFreshTraceAnyBadProbability
  simp only [adaptiveFreshTraceAnyBadEvent]
  have hmarginal :
      (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1)).map
        (fun trace : Fin (iteration + 1) → BatchIndex → Data => Fin.init trace) =
      adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration :=
    adaptiveFreshTraceLaw_init_marginal initialLaw dataLaw stateOfHistory iteration
  have hprefix :
      pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
        (fun trace => adaptiveFreshTraceAnyBadEvent bad iteration (Fin.init trace)) =
      pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration)
        (adaptiveFreshTraceAnyBadEvent bad iteration) := by
    calc
      pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
          (fun trace => adaptiveFreshTraceAnyBadEvent bad iteration (Fin.init trace)) =
        pmfProb ((adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1)).map
          (fun trace : Fin (iteration + 1) → BatchIndex → Data => Fin.init trace))
          (adaptiveFreshTraceAnyBadEvent bad iteration) :=
        (pmfProb_map (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
          (fun trace : Fin (iteration + 1) → BatchIndex → Data => Fin.init trace)
          (adaptiveFreshTraceAnyBadEvent bad iteration)).symm
      _ = pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration)
          (adaptiveFreshTraceAnyBadEvent bad iteration) := by rw [hmarginal]
  have hcurrent :
      pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
        (fun trace => bad iteration (Fin.init trace) (trace (Fin.last iteration))) ≤ failure := by
    apply pmfProb_adaptiveFreshTraceLaw_succ_le_of_forall
      initialLaw dataLaw stateOfHistory iteration
      (fun trace => bad iteration (Fin.init trace) (trace (Fin.last iteration))) failure
    intro history
    simpa only [Fin.init_snoc, Fin.snoc_last, adaptiveFreshConditionalBadProbability] using
      hfailure history
  have hunion := pmfProb_or_le
    (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
    (fun trace : Fin (iteration + 1) → BatchIndex → Data =>
      adaptiveFreshTraceAnyBadEvent bad iteration (Fin.init trace))
    (fun trace : Fin (iteration + 1) → BatchIndex → Data =>
      bad iteration (Fin.init trace) (trace (Fin.last iteration)))
  refine (le_trans ?_ hunion).trans ?_
  · unfold pmfProb
    apply le_of_eq
    apply pmfExp_congr
    intro trace
    by_cases hbad : (adaptiveFreshTraceAnyBadEvent bad iteration (Fin.init trace) ∨
      bad iteration (Fin.init trace) (trace (Fin.last iteration))) <;> simp [hbad]
  · calc
      pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
          (fun trace => adaptiveFreshTraceAnyBadEvent bad iteration (Fin.init trace)) +
        pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
          (fun trace => bad iteration (Fin.init trace) (trace (Fin.last iteration))) =
        pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration)
          (adaptiveFreshTraceAnyBadEvent bad iteration) +
        pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory (iteration + 1))
          (fun trace => bad iteration (Fin.init trace) (trace (Fin.last iteration))) := by
          rw [hprefix]
      _ ≤ pmfProb (adaptiveFreshTraceLaw initialLaw dataLaw stateOfHistory iteration)
            (adaptiveFreshTraceAnyBadEvent bad iteration) + failure := by
          exact add_le_add_right hcurrent _

/--
The finite-horizon union bound for history-dependent adaptive batch events
with a separate conditional failure budget at each round.  This is the form
needed when a concentration argument allocates a summable confidence budget
over time rather than using one common per-round bound.
-/
theorem adaptiveFreshTraceAnyBadProbability_le_sum
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop)
    (iteration : ℕ) (failure : ℕ → ℝ)
    (hfailure : ∀ round history,
      adaptiveFreshConditionalBadProbability dataLaw stateOfHistory bad round history ≤
        failure round) :
    adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad iteration ≤
      ∑ round ∈ Finset.range iteration, failure round := by
  induction iteration with
  | zero =>
      classical
      unfold adaptiveFreshTraceAnyBadProbability
      simp [adaptiveFreshTraceAnyBadEvent, pmfProb, pmfExp]
  | succ iteration hiteration =>
      calc
        adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad (iteration + 1) ≤
            adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad iteration +
              failure iteration :=
          adaptiveFreshTraceAnyBadProbability_succ_le initialLaw dataLaw stateOfHistory bad iteration
            (failure iteration) (hfailure iteration)
        _ ≤ (∑ round ∈ Finset.range iteration, failure round) + failure iteration :=
          add_le_add_left hiteration _
        _ = ∑ round ∈ Finset.range (iteration + 1), failure round := by
          rw [Finset.sum_range_succ]

/-- The finite-horizon union bound for arbitrary history-dependent adaptive batch events. -/
theorem adaptiveFreshTraceAnyBadProbability_le_mul
    {State Data BatchIndex : Type*}
    [Fintype Data] [DecidableEq Data]
    [Fintype BatchIndex] [DecidableEq BatchIndex]
    (initialLaw : PMF State) (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, (Fin iteration → BatchIndex → Data) → State)
    (bad : ∀ iteration, (Fin iteration → BatchIndex → Data) → (BatchIndex → Data) → Prop)
    (iteration : ℕ) (failure : ℝ)
    (hfailure : ∀ round history,
      adaptiveFreshConditionalBadProbability dataLaw stateOfHistory bad round history ≤ failure) :
    adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad iteration ≤
      (iteration : ℝ) * failure := by
  induction iteration with
  | zero =>
      classical
      unfold adaptiveFreshTraceAnyBadProbability
      simp [adaptiveFreshTraceAnyBadEvent, pmfProb, pmfExp]
  | succ iteration hiteration =>
      calc
        adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad (iteration + 1) ≤
          adaptiveFreshTraceAnyBadProbability initialLaw dataLaw stateOfHistory bad iteration + failure :=
          adaptiveFreshTraceAnyBadProbability_succ_le initialLaw dataLaw stateOfHistory bad iteration
            failure (hfailure iteration)
        _ ≤ (iteration : ℝ) * failure + failure := add_le_add_left hiteration _
        _ = ((iteration + 1 : ℕ) : ℝ) * failure := by
          push_cast
          ring

/-- A finite batch trace whose batch index type may change with the round. -/
def HeterogeneousBatchTrace (BatchIndex : ℕ → Type*) (Data : Type*)
    (iteration : ℕ) : Type _ :=
  (round : Fin iteration) → BatchIndex round.1 → Data

instance heterogeneousBatchTraceFintype
    (BatchIndex : ℕ → Type*) (Data : Type*) (iteration : ℕ)
    [Fintype Data] [DecidableEq Data] [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)] :
    Fintype (HeterogeneousBatchTrace BatchIndex Data iteration) := by
  unfold HeterogeneousBatchTrace
  letI : ∀ round : Fin iteration, Fintype (BatchIndex round.1 → Data) :=
    fun _ => inferInstance
  exact Pi.instFintype

instance heterogeneousBatchTraceDecidableEq
    (BatchIndex : ℕ → Type*) (Data : Type*) (iteration : ℕ)
    [Fintype Data] [DecidableEq Data] [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)] :
    DecidableEq (HeterogeneousBatchTrace BatchIndex Data iteration) := by
  unfold HeterogeneousBatchTrace
  letI : ∀ round : Fin iteration, DecidableEq (BatchIndex round.1 → Data) :=
    fun _ => inferInstance
  infer_instance

/-- Drop the most recent batch from a heterogeneous trace. -/
def heterogeneousBatchTraceInit {BatchIndex : ℕ → Type*} {Data : Type*} {iteration : ℕ} :
    HeterogeneousBatchTrace BatchIndex Data (iteration + 1) →
      HeterogeneousBatchTrace BatchIndex Data iteration :=
  fun trace round => trace round.castSucc

/-- The batch observed at the newest round of a heterogeneous trace. -/
def heterogeneousBatchTraceLast {BatchIndex : ℕ → Type*} {Data : Type*} {iteration : ℕ} :
    HeterogeneousBatchTrace BatchIndex Data (iteration + 1) → BatchIndex iteration → Data :=
  fun trace => trace (Fin.last iteration)

/-- Append a round-dependent batch to a heterogeneous trace. -/
def heterogeneousBatchTraceSnoc {BatchIndex : ℕ → Type*} {Data : Type*} {iteration : ℕ}
    (history : HeterogeneousBatchTrace BatchIndex Data iteration)
    (batch : BatchIndex iteration → Data) :
    HeterogeneousBatchTrace BatchIndex Data (iteration + 1) :=
  fun round => Fin.lastCases batch (fun previous => history previous) round

@[simp] theorem heterogeneousBatchTraceInit_snoc
    {BatchIndex : ℕ → Type*} {Data : Type*} {iteration : ℕ}
    (history : HeterogeneousBatchTrace BatchIndex Data iteration)
    (batch : BatchIndex iteration → Data) :
    heterogeneousBatchTraceInit (heterogeneousBatchTraceSnoc history batch) = history := by
  funext round index
  simp [heterogeneousBatchTraceInit, heterogeneousBatchTraceSnoc]

@[simp] theorem heterogeneousBatchTraceLast_snoc
    {BatchIndex : ℕ → Type*} {Data : Type*} {iteration : ℕ}
    (history : HeterogeneousBatchTrace BatchIndex Data iteration)
    (batch : BatchIndex iteration → Data) :
    heterogeneousBatchTraceLast (heterogeneousBatchTraceSnoc history batch) = batch := by
  funext index
  simp [heterogeneousBatchTraceLast, heterogeneousBatchTraceSnoc]

/-- A nonempty heterogeneous trace is recovered by dropping and then reattaching its last batch. -/
@[simp] theorem heterogeneousBatchTraceSnoc_init_last
    {BatchIndex : ℕ → Type*} {Data : Type*} {iteration : ℕ}
    (trace : HeterogeneousBatchTrace BatchIndex Data (iteration + 1)) :
    heterogeneousBatchTraceSnoc (heterogeneousBatchTraceInit trace)
      (heterogeneousBatchTraceLast trace) = trace := by
  funext round
  refine Fin.lastCases ?_ ?_ round
  · funext index
    simp [heterogeneousBatchTraceSnoc, heterogeneousBatchTraceLast]
  · intro previous
    funext index
    simp [heterogeneousBatchTraceSnoc, heterogeneousBatchTraceInit]

/--
Law of a complete finite adaptive trace with a potentially different IID batch
carrier at every round.  The state selected for the next data law is a
deterministic function of the complete preceding trace, so random adaptive
deployment is represented without an inter-round independence assumption.
-/
noncomputable def adaptiveFreshHeterogeneousTraceLaw
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State) :
    (iteration : ℕ) → PMF (HeterogeneousBatchTrace BatchIndex Data iteration)
  | 0 => PMF.pure (fun round => Fin.elim0 round)
  | iteration + 1 =>
      (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration).bind fun history =>
        (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history))).map
          (heterogeneousBatchTraceSnoc history)

/-- One heterogeneous trace-extension expectation identity. -/
theorem pmfExp_adaptiveFreshHeterogeneousTraceLaw_succ
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) (statistic : HeterogeneousBatchTrace BatchIndex Data (iteration + 1) → ℝ) :
    pmfExp (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
      statistic =
      pmfExp (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
        (fun history => pmfExp
          (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history)))
          (fun batch => statistic (heterogeneousBatchTraceSnoc history batch))) := by
  change pmfExp
      ((adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration).bind fun history =>
        (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history))).map
          (heterogeneousBatchTraceSnoc history)) statistic = _
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro history
  simpa [Function.comp_def] using
    (pmfExp_map (pmfProduct (BatchIndex iteration) Data
      (dataLaw (stateOfHistory iteration history)))
      (heterogeneousBatchTraceSnoc history) statistic)

/-- Dropping the newest heterogeneous batch recovers exactly the previous trace law. -/
theorem adaptiveFreshHeterogeneousTraceLaw_init_marginal
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) :
    (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1)).map
        heterogeneousBatchTraceInit =
      adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration := by
  change PMF.map heterogeneousBatchTraceInit
      ((adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration).bind fun history =>
        (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history))).map
          (heterogeneousBatchTraceSnoc history)) = _
  rw [PMF.map_bind]
  calc
    (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration).bind (fun history =>
        PMF.map heterogeneousBatchTraceInit
          (PMF.map (heterogeneousBatchTraceSnoc history)
            (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history))))) =
      (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration).bind PMF.pure := by
        congr 1
        funext history
        rw [PMF.map_comp]
        have hcompose : heterogeneousBatchTraceInit ∘ heterogeneousBatchTraceSnoc history =
            (fun _ : BatchIndex iteration → Data => history) := by
          funext batch
          exact heterogeneousBatchTraceInit_snoc history batch
        rw [hcompose]
        exact PMF.map_const _ history
    _ = adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration := PMF.bind_pure _

/-- Next-round event probabilities factor through the preceding heterogeneous history. -/
theorem pmfProb_adaptiveFreshHeterogeneousTraceLaw_succ
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) (event : HeterogeneousBatchTrace BatchIndex Data (iteration + 1) → Prop)
    [DecidablePred event] :
    pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
      event =
      pmfExp (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
        (fun history => pmfProb
          (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history)))
          (fun batch => event (heterogeneousBatchTraceSnoc history batch))) := by
  classical
  unfold pmfProb
  simpa using pmfExp_adaptiveFreshHeterogeneousTraceLaw_succ BatchIndex dataLaw stateOfHistory
    iteration (fun trace => if event trace then (1 : ℝ) else 0)

/-- A uniform conditional bound controls the corresponding next heterogeneous trace event. -/
theorem pmfProb_adaptiveFreshHeterogeneousTraceLaw_succ_le_of_forall
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) (event : HeterogeneousBatchTrace BatchIndex Data (iteration + 1) → Prop)
    [DecidablePred event] (failure : ℝ)
    (hfailure : ∀ history,
      pmfProb (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history)))
        (fun batch => event (heterogeneousBatchTraceSnoc history batch)) ≤ failure) :
    pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
      event ≤ failure := by
  classical
  rw [pmfProb_adaptiveFreshHeterogeneousTraceLaw_succ]
  calc
    pmfExp (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
        (fun history => pmfProb
          (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history)))
          (fun batch => event (heterogeneousBatchTraceSnoc history batch))) ≤
      pmfExp (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
        (fun _ => failure) :=
      pmfExp_le_pmfExp_of_forall_le _ _ _ hfailure
    _ = failure := pmfExp_const _ failure

/-- The recursively defined event that one heterogeneous adaptive batch is bad. -/
def adaptiveFreshHeterogeneousTraceAnyBadEvent
    {Data : Type*} (BatchIndex : ℕ → Type*)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop) :
    ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → Prop
  | 0 => fun _ => False
  | iteration + 1 => fun trace =>
      adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
        (heterogeneousBatchTraceInit trace) ∨
      bad iteration (heterogeneousBatchTraceInit trace) (heterogeneousBatchTraceLast trace)

/-- Conditional IID bad-event probability for one heterogeneous batch. -/
noncomputable def adaptiveFreshHeterogeneousConditionalBadProbability
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (history : HeterogeneousBatchTrace BatchIndex Data iteration) : ℝ := by
  classical
  letI : DecidablePred (bad iteration history) := Classical.decPred _
  exact pmfProb (pmfProduct (BatchIndex iteration) Data (dataLaw (stateOfHistory iteration history)))
    (bad iteration history)

/-- The finite-PMF probability that a heterogeneous adaptive trace contains a bad batch. -/
noncomputable def adaptiveFreshHeterogeneousTraceAnyBadProbability
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) : ℝ := by
  classical
  letI : DecidablePred (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration) :=
    Classical.decPred _
  exact pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
    (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration)

/-- One heterogeneous extension increases bad-event probability by at most its round budget. -/
theorem adaptiveFreshHeterogeneousTraceAnyBadProbability_succ_le
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (failure : ℝ)
    (hfailure : ∀ history,
      adaptiveFreshHeterogeneousConditionalBadProbability BatchIndex dataLaw stateOfHistory bad
        iteration history ≤ failure) :
    adaptiveFreshHeterogeneousTraceAnyBadProbability BatchIndex dataLaw stateOfHistory bad
      (iteration + 1) ≤
      adaptiveFreshHeterogeneousTraceAnyBadProbability BatchIndex dataLaw stateOfHistory bad iteration +
        failure := by
  classical
  unfold adaptiveFreshHeterogeneousTraceAnyBadProbability
  simp only [adaptiveFreshHeterogeneousTraceAnyBadEvent]
  have hmarginal :
      (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1)).map
        heterogeneousBatchTraceInit =
      adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration :=
    adaptiveFreshHeterogeneousTraceLaw_init_marginal BatchIndex dataLaw stateOfHistory iteration
  have hprefix :
      pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
        (fun trace => adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
          (heterogeneousBatchTraceInit trace)) =
      pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
        (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration) := by
    calc
      pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
          (fun trace => adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
            (heterogeneousBatchTraceInit trace)) =
        pmfProb ((adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1)).map
          heterogeneousBatchTraceInit)
          (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration) :=
        (pmfProb_map (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
          heterogeneousBatchTraceInit (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration)).symm
      _ = pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
          (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration) := by rw [hmarginal]
  have hcurrent :
      pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
        (fun trace => bad iteration (heterogeneousBatchTraceInit trace)
          (heterogeneousBatchTraceLast trace)) ≤ failure := by
    apply pmfProb_adaptiveFreshHeterogeneousTraceLaw_succ_le_of_forall
      BatchIndex dataLaw stateOfHistory iteration
      (fun trace => bad iteration (heterogeneousBatchTraceInit trace)
        (heterogeneousBatchTraceLast trace)) failure
    intro history
    simpa only [heterogeneousBatchTraceInit_snoc, heterogeneousBatchTraceLast_snoc,
      adaptiveFreshHeterogeneousConditionalBadProbability] using hfailure history
  have hunion := pmfProb_or_le
    (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
    (fun trace => adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
      (heterogeneousBatchTraceInit trace))
    (fun trace => bad iteration (heterogeneousBatchTraceInit trace)
      (heterogeneousBatchTraceLast trace))
  refine (le_trans ?_ hunion).trans ?_
  · unfold pmfProb
    apply le_of_eq
    apply pmfExp_congr
    intro trace
    by_cases hbad : (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
      (heterogeneousBatchTraceInit trace) ∨
      bad iteration (heterogeneousBatchTraceInit trace) (heterogeneousBatchTraceLast trace)) <;>
      simp [hbad]
  · calc
      pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
          (fun trace => adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
            (heterogeneousBatchTraceInit trace)) +
        pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
          (fun trace => bad iteration (heterogeneousBatchTraceInit trace)
            (heterogeneousBatchTraceLast trace)) =
        pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
          (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration) +
        pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (iteration + 1))
          (fun trace => bad iteration (heterogeneousBatchTraceInit trace)
            (heterogeneousBatchTraceLast trace)) := by rw [hprefix]
      _ ≤ pmfProb (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory iteration)
            (adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration) + failure := by
          exact add_le_add_right hcurrent _

/--
The finite-horizon union bound for arbitrary history-dependent events with
heterogeneous batches and a separate conditional budget at each round.
-/
theorem adaptiveFreshHeterogeneousTraceAnyBadProbability_le_sum
    {State Data : Type*} [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (failure : ℕ → ℝ)
    (hfailure : ∀ round history,
      adaptiveFreshHeterogeneousConditionalBadProbability BatchIndex dataLaw stateOfHistory bad
        round history ≤ failure round) :
    adaptiveFreshHeterogeneousTraceAnyBadProbability BatchIndex dataLaw stateOfHistory bad iteration ≤
      ∑ round ∈ Finset.range iteration, failure round := by
  induction iteration with
  | zero =>
      classical
      unfold adaptiveFreshHeterogeneousTraceAnyBadProbability
      simp [adaptiveFreshHeterogeneousTraceAnyBadEvent, pmfProb, pmfExp]
  | succ iteration hiteration =>
      calc
        adaptiveFreshHeterogeneousTraceAnyBadProbability BatchIndex dataLaw stateOfHistory bad
            (iteration + 1) ≤
            adaptiveFreshHeterogeneousTraceAnyBadProbability BatchIndex dataLaw stateOfHistory bad
              iteration + failure iteration :=
          adaptiveFreshHeterogeneousTraceAnyBadProbability_succ_le BatchIndex dataLaw stateOfHistory
            bad iteration (failure iteration) (hfailure iteration)
        _ ≤ (∑ round ∈ Finset.range iteration, failure round) + failure iteration :=
          add_le_add_left hiteration _
        _ = ∑ round ∈ Finset.range (iteration + 1), failure round := by
          rw [Finset.sum_range_succ]

end AppliedModelingLib
