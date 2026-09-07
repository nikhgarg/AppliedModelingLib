import AppliedModelingLib.Foundations.Probability.FiniteEventDrift
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping

/-!
# Finite-event products as IID stream prefixes

This module identifies the finite PMF product used in a finite-horizon event
calculation with the literal prefix law of the canonical IID stream.  It is a
law bridge only: recurrence and renewal conclusions belong to the consumers
that supply an appropriate stopped trajectory.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {Event : Type*} [Fintype Event] [DecidableEq Event]
  [MeasurableSpace Event] [MeasurableSingletonClass Event]

/-- The PMF product over a finite index type induces exactly the corresponding
finite product measure of its one-event law. -/
theorem pmfProduct_toMeasure_eq_pi
    {ι : Type*} [Fintype ι] [DecidableEq ι] (law : PMF Event) :
    (pmfProduct ι Event law).toMeasure =
      Measure.pi (fun _ : ι => law.toMeasure) := by
  let productMeasure : Measure (ι → Event) :=
    Measure.pi (fun _ : ι => law.toMeasure)
  have hpmf : productMeasure.toPMF = pmfProduct ι Event law := by
    apply PMF.ext
    intro sample
    rw [Measure.toPMF_apply, Measure.pi_singleton, pmfProduct_apply]
    apply Finset.prod_congr rfl
    intro i _
    exact PMF.toMeasure_apply_singleton law (sample i) (measurableSet_singleton _)
  rw [← hpmf]
  exact Measure.toPMF_toMeasure productMeasure

/-- A deterministic finite IID block has the PMF-product law used by the
finite-event drift calculation. -/
theorem block_hasLaw_pmfProduct
    (law : PMF Event) (n : ℕ) :
    HasLaw (block (α := Event) 0 n)
      (pmfProduct (Fin n) Event law).toMeasure (measure law.toMeasure) := by
  refine ⟨(measurable_block 0 n).aemeasurable, ?_⟩
  calc
    Measure.map (block (α := Event) 0 n) (measure law.toMeasure) =
        Measure.pi (fun _ : Fin n => law.toMeasure) :=
      (block_hasLaw law.toMeasure 0 n).map_eq
    _ = (pmfProduct (Fin n) Event law).toMeasure :=
      (pmfProduct_toMeasure_eq_pi law).symm

/-- The literal IID-stream probability of a finite-horizon state event is the
finite-product probability used in `FiniteEventDrift`. -/
theorem measureReal_finiteEventTrajectoryEvent_eq
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (event : State → Prop) [DecidablePred event]
    (n : ℕ) :
    (measure law.toMeasure).real
      {omega | event (finiteEventTrajectory initial step n
        (block (α := Event) 0 n omega))} =
      finiteEventTrajectoryEventProbability law initial step event n := by
  let s : Set (Fin n → Event) :=
    {sample | event (finiteEventTrajectory initial step n sample)}
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  have hlaw := block_hasLaw_pmfProduct law n
  change (measure law.toMeasure
      ((block (α := Event) 0 n) ⁻¹' s)).toReal = _
  rw [← Measure.map_apply (measurable_block 0 n) hs, hlaw.map_eq]
  rw [PMF.toMeasure_apply_fintype]
  have hne : ∀ sample ∈ (Finset.univ : Finset (Fin n → Event)),
      s.indicator (pmfProduct (Fin n) Event law) sample ≠ ⊤ := by
    intro sample _
    by_cases hsample : sample ∈ s
    · rw [Set.indicator_of_mem hsample]
      exact (pmfProduct (Fin n) Event law).apply_ne_top sample
    · rw [Set.indicator_of_notMem hsample]
      exact ENNReal.zero_ne_top
  rw [ENNReal.toReal_sum hne]
  unfold finiteEventTrajectoryEventProbability
  apply Finset.sum_congr rfl
  intro sample _
  by_cases hevent : event (finiteEventTrajectory initial step n sample)
  · simp [s, hevent]
  · simp [s, hevent]

/-- The literal IID-stream event set at a finite trajectory horizon.  Its
measurability is inherited from the finite block of event coordinates, even
when the trajectory state space itself is infinite. -/
def finiteEventTrajectoryEventSet
    {State : Type*} (initial : State)
    (step : State → Event → State) (event : State → Prop) (n : ℕ) :
    Set (ℕ → Event) :=
  {omega | event (finiteEventTrajectory initial step n
    (block (α := Event) 0 n omega))}

/-- A finite-trajectory event is Borel on the literal IID event stream. -/
theorem measurableSet_finiteEventTrajectoryEventSet
    {State : Type*} (initial : State)
    (step : State → Event → State) (event : State → Prop) (n : ℕ) :
    MeasurableSet (finiteEventTrajectoryEventSet initial step event n) := by
  let s : Set (Fin n → Event) :=
    {sample | event (finiteEventTrajectory initial step n sample)}
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  change MeasurableSet ((block (α := Event) 0 n) ⁻¹' s)
  exact hs.preimage (measurable_block 0 n)

/-- A nonnegative reward evaluated at a fixed finite event horizon on the
literal IID stream.  The state space itself need not carry a useful Borel
structure: only the finite input prefix is observed. -/
noncomputable def finiteEventTrajectoryNonnegativeReward
    {State : Type*} (initial : State) (step : State → Event → State)
    (reward : State → ℝ) (n : ℕ) :
    (ℕ → Event) → ℝ≥0∞ :=
  fun omega => ENNReal.ofReal (reward (finiteEventTrajectory initial step n
    (block (α := Event) 0 n omega)))

/-- A fixed finite-horizon nonnegative trajectory reward is Borel on the
literal IID stream. -/
theorem measurable_finiteEventTrajectoryNonnegativeReward
    {State : Type*} (initial : State) (step : State → Event → State)
    (reward : State → ℝ) (n : ℕ) :
    Measurable (finiteEventTrajectoryNonnegativeReward initial step reward n) := by
  unfold finiteEventTrajectoryNonnegativeReward
  exact ((measurable_of_finite (fun sample : Fin n → Event =>
    reward (finiteEventTrajectory initial step n sample))).ennreal_ofReal).comp
      (measurable_block 0 n)

/-- The expected nonnegative reward at one finite event horizon agrees with
the finite PMF-product expectation used by the Lyapunov calculation. -/
theorem lintegral_finiteEventTrajectoryNonnegativeReward
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (reward : State → ℝ)
    (hreward : ∀ state, 0 ≤ reward state) (n : ℕ) :
    ∫⁻ omega, finiteEventTrajectoryNonnegativeReward initial step reward n omega ∂
      (measure law.toMeasure) =
      ENNReal.ofReal (pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => reward (finiteEventTrajectory initial step n sample))) := by
  let q := pmfProduct (Fin n) Event law
  let f : (Fin n → Event) → ℝ :=
    fun sample => reward (finiteEventTrajectory initial step n sample)
  have hf : Measurable f := measurable_of_finite f
  have hnonnegative : 0 ≤ᶠ[ae q.toMeasure] f :=
    Filter.Eventually.of_forall fun sample => hreward _
  have hintegrable : Integrable f q.toMeasure := Integrable.of_finite
  have hblock := block_hasLaw_pmfProduct law n
  calc
    ∫⁻ omega, finiteEventTrajectoryNonnegativeReward initial step reward n omega ∂
        (measure law.toMeasure) =
        ∫⁻ sample, ENNReal.ofReal (f sample) ∂q.toMeasure := by
          simpa [finiteEventTrajectoryNonnegativeReward, f, q] using
            hblock.lintegral_comp (hf.ennreal_ofReal.aemeasurable)
    _ = ENNReal.ofReal (∫ sample, f sample ∂q.toMeasure) := by
          symm
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            hintegrable hnonnegative
    _ = ENNReal.ofReal (pmfExp q f) := by
          rw [pmfExp_eq_integral_toMeasure]
    _ = ENNReal.ofReal (pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => reward (finiteEventTrajectory initial step n sample))) := by
          rfl

/-- A summable family of finite-horizon nonnegative PMF rewards has finite
total expectation on the literal IID event stream. -/
theorem tsum_lintegral_finiteEventTrajectoryNonnegativeReward_ne_top
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (reward : State → ℝ)
    (hreward : ∀ state, 0 ≤ reward state)
    (hsummable : Summable (fun n => pmfExp (pmfProduct (Fin n) Event law)
      (fun sample => reward (finiteEventTrajectory initial step n sample)))) :
    ∑' n, ∫⁻ omega,
      finiteEventTrajectoryNonnegativeReward initial step reward n omega ∂
        (measure law.toMeasure) ≠ ⊤ := by
  have heq : (fun n => ∫⁻ omega,
      finiteEventTrajectoryNonnegativeReward initial step reward n omega ∂
        (measure law.toMeasure)) =
      (fun n => ENNReal.ofReal (pmfExp (pmfProduct (Fin n) Event law)
        (fun sample => reward (finiteEventTrajectory initial step n sample)))) := by
    funext n
    exact lintegral_finiteEventTrajectoryNonnegativeReward
      law initial step reward hreward n
  rw [heq]
  exact hsummable.tsum_ofReal_ne_top

/-- Count the finite trajectory horizons at which an IID event path satisfies
a state predicate.  This extended count records the number of occupied event
slots before a regenerative state is reached. -/
noncomputable def finiteEventTrajectoryEventCount
    {State : Type*} (initial : State)
    (step : State → Event → State) (event : State → Prop) :
    (ℕ → Event) → ENNReal :=
  fun omega => ∑' n,
    (finiteEventTrajectoryEventSet initial step event n).indicator
      (fun _ => (1 : ENNReal)) omega

/-- If the initial state satisfies the counted predicate, every event path
contributes at least its initial occupied slot to the trajectory event count.
This elementary lower bound is useful when a regenerative excursion starts
from a nonempty state and its occupation measure must have positive mass. -/
theorem one_le_finiteEventTrajectoryEventCount_of_initial
    {State : Type*} (initial : State)
    (step : State → Event → State) (event : State → Prop)
    (hinitial : event initial) (omega : ℕ → Event) :
    1 ≤ finiteEventTrajectoryEventCount initial step event omega := by
  unfold finiteEventTrajectoryEventCount
  calc
    1 = (finiteEventTrajectoryEventSet initial step event 0).indicator
        (fun _ => (1 : ENNReal)) omega := by
          have hmem : omega ∈ finiteEventTrajectoryEventSet initial step event 0 := by
            change event (finiteEventTrajectory initial step 0
              (block (α := Event) 0 0 omega))
            simpa [finiteEventTrajectory] using hinitial
          rw [Set.indicator_of_mem hmem]
    _ ≤ ∑' n,
        (finiteEventTrajectoryEventSet initial step event n).indicator
          (fun _ => (1 : ENNReal)) omega := ENNReal.le_tsum 0

/-- The trajectory event count is Borel. -/
theorem measurable_finiteEventTrajectoryEventCount
    {State : Type*} (initial : State)
    (step : State → Event → State) (event : State → Prop) :
    Measurable (finiteEventTrajectoryEventCount initial step event) := by
  exact Measurable.ennreal_tsum fun n =>
    measurable_const.indicator
      (measurableSet_finiteEventTrajectoryEventSet initial step event n)

/-- Tonelli identifies the expected trajectory event count with the sum of
the literal IID-stream event probabilities. -/
theorem lintegral_finiteEventTrajectoryEventCount
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (event : State → Prop) :
    ∫⁻ omega, finiteEventTrajectoryEventCount initial step event omega ∂
      (measure law.toMeasure) =
      ∑' n, (measure law.toMeasure)
        (finiteEventTrajectoryEventSet initial step event n) := by
  unfold finiteEventTrajectoryEventCount
  rw [MeasureTheory.lintegral_tsum]
  · apply tsum_congr
    intro n
    exact MeasureTheory.lintegral_indicator_one
      (measurableSet_finiteEventTrajectoryEventSet initial step event n)
  · intro n
    exact (measurable_const.indicator
      (measurableSet_finiteEventTrajectoryEventSet initial step event n)).aemeasurable

/-- When the finite-product event probabilities are summable, the expected
literal IID event count is the extended-real embedding of their real sum. -/
theorem lintegral_finiteEventTrajectoryEventCount_eq_ofReal_tsum
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (event : State → Prop) [DecidablePred event]
    (hsummable : Summable
      (finiteEventTrajectoryEventProbability law initial step event)) :
    ∫⁻ omega, finiteEventTrajectoryEventCount initial step event omega ∂
      (measure law.toMeasure) =
      ENNReal.ofReal (∑' n,
        finiteEventTrajectoryEventProbability law initial step event n) := by
  letI : IsProbabilityMeasure (measure law.toMeasure) := by
    dsimp [measure]
    infer_instance
  rw [lintegral_finiteEventTrajectoryEventCount]
  have hterm : ∀ n,
      ENNReal.ofReal (finiteEventTrajectoryEventProbability law initial step event n) =
        (measure law.toMeasure)
          (finiteEventTrajectoryEventSet initial step event n) := by
    intro n
    rw [← measureReal_finiteEventTrajectoryEvent_eq law initial step event n]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [← tsum_congr hterm]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => finiteEventTrajectoryEventProbability_nonneg law initial step event n)
    hsummable).symm

/-- A real bound on a summable finite-product event tail transports to the
expected literal IID event count. -/
theorem lintegral_finiteEventTrajectoryEventCount_le_of_tsum_bound
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (event : State → Prop) [DecidablePred event]
    (hsummable : Summable
      (finiteEventTrajectoryEventProbability law initial step event))
    (bound : ℝ)
    (hbound : ∑' n, finiteEventTrajectoryEventProbability law initial step event n ≤ bound) :
    ∫⁻ omega, finiteEventTrajectoryEventCount initial step event omega ∂
      (measure law.toMeasure) ≤ ENNReal.ofReal bound := by
  rw [lintegral_finiteEventTrajectoryEventCount_eq_ofReal_tsum
    law initial step event hsummable]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Integrate the finite-event Lyapunov bound over an independent random
initial state.  The caller supplies measurability of the resulting count on
the product carrier; no stationarity or restart law is hidden in this
finite-start statement. -/
theorem lintegral_externalInitial_finiteEventTrajectoryEventCount_le
    {σ State : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (law : PMF Event) (initial : σ → State)
    (step : State → Event → State) (potential cost : State → ℝ)
    (event : State → Prop) [DecidablePred event]
    (charge : ℝ) (hcharge : 0 < charge)
    (hpotential_nonneg : ∀ state, 0 ≤ potential state)
    (hstep : ∀ state,
      pmfExp law (fun draw => potential (step state draw)) + cost state ≤ potential state)
    (hcost : ∀ state, cost state = charge * (if event state then 1 else 0))
    (hcount : Measurable (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryEventCount (initial z.1) step event z.2)) :
    ∫⁻ z : σ × (ℕ → Event),
        finiteEventTrajectoryEventCount (initial z.1) step event z.2 ∂
          (ρ.prod (measure law.toMeasure)) ≤
      ∫⁻ x, ENNReal.ofReal (potential (initial x) / charge) ∂ρ := by
  letI : IsProbabilityMeasure (measure law.toMeasure) := by
    dsimp [measure]
    infer_instance
  calc
    ∫⁻ z : σ × (ℕ → Event),
        finiteEventTrajectoryEventCount (initial z.1) step event z.2 ∂
          (ρ.prod (measure law.toMeasure)) =
        ∫⁻ x, ∫⁻ omega,
          finiteEventTrajectoryEventCount (initial x) step event omega ∂
            (measure law.toMeasure) ∂ρ := by
          exact MeasureTheory.lintegral_prod _ hcount.aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (potential (initial x) / charge) ∂ρ := by
      apply MeasureTheory.lintegral_mono
      intro x
      exact lintegral_finiteEventTrajectoryEventCount_le_of_tsum_bound
        law (initial x) step event
        (summable_finiteEventTrajectoryEventProbability_of_drift
          law (initial x) step potential cost event charge hcharge
          hpotential_nonneg hstep hcost)
        (potential (initial x) / charge)
        (tsum_finiteEventTrajectoryEventProbability_le_initialPotential_div_charge
          law (initial x) step potential cost event charge hcharge
          hpotential_nonneg hstep hcost)

/-- The event at a fixed finite trajectory horizon when the initial state is
an independent external coordinate. -/
def externalInitialFiniteEventTrajectoryEventSet
    {σ State : Type*} [MeasurableSpace σ]
    (initial : σ → State) (step : State → Event → State) (event : State → Prop)
    (n : ℕ) : Set (σ × (ℕ → Event)) :=
  {z | event (finiteEventTrajectory (initial z.1) step n (block 0 n z.2))}

/-- With a finite external initial-state type, every finite-horizon trajectory
event is Borel on the product of that state and the literal IID event stream.
This is the measurability bridge used when a finite initial distribution is
averaged over an otherwise infinite IID trajectory. -/
theorem measurableSet_externalInitialFiniteEventTrajectoryEventSet_of_finite
    {σ State : Type*} [MeasurableSpace σ] [Fintype σ]
    [MeasurableSingletonClass σ]
    (initial : σ → State) (step : State → Event → State) (event : State → Prop)
    (n : ℕ) :
    MeasurableSet (externalInitialFiniteEventTrajectoryEventSet initial step event n) := by
  let E : Set (σ × (ℕ → Event)) :=
    externalInitialFiniteEventTrajectoryEventSet initial step event n
  have hsplit : E = ⋃ i : σ,
      ({i} : Set σ) ×ˢ finiteEventTrajectoryEventSet (initial i) step event n := by
    ext z
    rcases z with ⟨x, omega⟩
    simp [E, externalInitialFiniteEventTrajectoryEventSet,
      finiteEventTrajectoryEventSet]
  change MeasurableSet E
  rw [hsplit]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_singleton i).prod
    (measurableSet_finiteEventTrajectoryEventSet (initial i) step event n)

/-- A countable external initial-state mixture also has Borel finite-horizon
trajectory events.  This is the natural form for a countable Markov state
space sampled from a regenerative law; no finiteness of its support is used. -/
theorem measurableSet_externalInitialFiniteEventTrajectoryEventSet_of_countable
    {σ State : Type*} [MeasurableSpace σ] [Countable σ]
    [MeasurableSingletonClass σ]
    (initial : σ → State) (step : State → Event → State) (event : State → Prop)
    (n : ℕ) :
    MeasurableSet (externalInitialFiniteEventTrajectoryEventSet initial step event n) := by
  let E : Set (σ × (ℕ → Event)) :=
    externalInitialFiniteEventTrajectoryEventSet initial step event n
  have hsplit : E = ⋃ i : σ,
      ({i} : Set σ) ×ˢ finiteEventTrajectoryEventSet (initial i) step event n := by
    ext z
    rcases z with ⟨x, omega⟩
    simp [E, externalInitialFiniteEventTrajectoryEventSet,
      finiteEventTrajectoryEventSet]
  change MeasurableSet E
  rw [hsplit]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_singleton i).prod
    (measurableSet_finiteEventTrajectoryEventSet (initial i) step event n)

/-- With finite external initial data, the full extended count of trajectory
event visits is Borel on the product carrier. -/
theorem measurable_externalInitial_finiteEventTrajectoryEventCount_of_finite
    {σ State : Type*} [MeasurableSpace σ] [Fintype σ]
    [MeasurableSingletonClass σ]
    (initial : σ → State) (step : State → Event → State) (event : State → Prop) :
    Measurable (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryEventCount (initial z.1) step event z.2) := by
  let term : σ → (σ × (ℕ → Event)) → ENNReal := fun i z =>
    (({i} : Set σ) ×ˢ Set.univ).indicator
      (fun z => finiteEventTrajectoryEventCount (initial i) step event z.2) z
  have hterm : ∀ i, Measurable (term i) := by
    intro i
    apply ((measurable_finiteEventTrajectoryEventCount (initial i) step event).comp
      measurable_snd).indicator
    exact (measurableSet_singleton i).prod MeasurableSet.univ
  have hsum : (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryEventCount (initial z.1) step event z.2) =
      fun z => ∑ i, term i z := by
    funext z
    rcases z with ⟨x, omega⟩
    rw [Finset.sum_eq_single x]
    · simp [term, Set.indicator]
    · intro i _ hix
      have hxi : x ≠ i := Ne.symm hix
      simp [term, Set.indicator, hxi]
    · simp
  rw [hsum]
  exact Finset.measurable_fun_sum Finset.univ fun i _ => hterm i

/-- The full extended count of trajectory visits is Borel for a countable
external initial-state carrier.  The count is a disjoint nonnegative sum over
the initial-state fibers, so countability is sufficient. -/
theorem measurable_externalInitial_finiteEventTrajectoryEventCount_of_countable
    {σ State : Type*} [MeasurableSpace σ] [Countable σ]
    [MeasurableSingletonClass σ]
    (initial : σ → State) (step : State → Event → State) (event : State → Prop) :
    Measurable (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryEventCount (initial z.1) step event z.2) := by
  classical
  let term : σ → (σ × (ℕ → Event)) → ENNReal := fun i z =>
    (({i} : Set σ) ×ˢ Set.univ).indicator
      (fun z => finiteEventTrajectoryEventCount (initial i) step event z.2) z
  have hterm : ∀ i, Measurable (term i) := by
    intro i
    apply ((measurable_finiteEventTrajectoryEventCount (initial i) step event).comp
      measurable_snd).indicator
    exact (measurableSet_singleton i).prod MeasurableSet.univ
  have hsum : (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryEventCount (initial z.1) step event z.2) =
      fun z => ∑' i, term i z := by
    funext z
    rcases z with ⟨x, omega⟩
    rw [tsum_eq_single x]
    · simp [term, Set.indicator]
    · intro i hix
      have hxi : x ≠ i := Ne.symm hix
      simp [term, Set.indicator, hxi]
  rw [hsum]
  exact Measurable.ennreal_tsum hterm

/-- With finite external initial data, a finite-horizon nonnegative trajectory
reward is Borel on the product of that data and the literal IID event stream. -/
theorem measurable_externalInitial_finiteEventTrajectoryNonnegativeReward_of_finite
    {σ State : Type*} [MeasurableSpace σ] [Fintype σ]
    [MeasurableSingletonClass σ]
    (initial : σ → State) (step : State → Event → State) (reward : State → ℝ)
    (n : ℕ) :
    Measurable (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2) := by
  let term : σ → (σ × (ℕ → Event)) → ENNReal := fun i z =>
    (({i} : Set σ) ×ˢ Set.univ).indicator
      (fun z => finiteEventTrajectoryNonnegativeReward (initial i) step reward n z.2) z
  have hterm : ∀ i, Measurable (term i) := by
    intro i
    apply ((measurable_finiteEventTrajectoryNonnegativeReward (initial i) step reward n).comp
      measurable_snd).indicator
    exact (measurableSet_singleton i).prod MeasurableSet.univ
  have hsum : (fun z : σ × (ℕ → Event) =>
      finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2) =
      fun z => ∑ i, term i z := by
    funext z
    rcases z with ⟨x, omega⟩
    rw [Finset.sum_eq_single x]
    · simp [term, Set.indicator]
    · intro i _ hix
      have hxi : x ≠ i := Ne.symm hix
      simp [term, Set.indicator, hxi]
    · simp
  rw [hsum]
  exact Finset.measurable_fun_sum Finset.univ fun i _ => hterm i

/-- A finite external initial-state mixture preserves the exact finite-event
reward identity: first condition on that initial state, then use the literal
IID event-stream prefix law. -/
theorem lintegral_externalInitial_finiteEventTrajectoryNonnegativeReward_eq_of_finite
    {σ State : Type*} [MeasurableSpace σ] [Fintype σ]
    [MeasurableSingletonClass σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (law : PMF Event) (initial : σ → State) (step : State → Event → State)
    (reward : State → ℝ) (hreward : ∀ state, 0 ≤ reward state) (n : ℕ) :
    ∫⁻ z : σ × (ℕ → Event),
      finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2 ∂
        (ρ.prod (measure law.toMeasure)) =
      ∫⁻ initialState, ENNReal.ofReal
        (pmfExp (pmfProduct (Fin n) Event law) (fun sample =>
          reward (finiteEventTrajectory (initial initialState) step n sample))) ∂ρ := by
  letI : IsProbabilityMeasure (measure law.toMeasure) := by
    dsimp [measure]
    infer_instance
  rw [MeasureTheory.lintegral_prod _
    (measurable_externalInitial_finiteEventTrajectoryNonnegativeReward_of_finite
      initial step reward n).aemeasurable]
  apply MeasureTheory.lintegral_congr
  intro initialState
  exact lintegral_finiteEventTrajectoryNonnegativeReward
    law (initial initialState) step reward hreward n

/-- A finite external mixture of finite-start nonnegative reward trajectories
has finite total expected reward whenever every component's expected reward
tail is summable. -/
theorem tsum_lintegral_externalInitial_finiteEventTrajectoryNonnegativeReward_ne_top_of_finite
    {σ State : Type*} [MeasurableSpace σ] [Fintype σ]
    [MeasurableSingletonClass σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (law : PMF Event) (initial : σ → State) (step : State → Event → State)
    (reward : State → ℝ) (hreward : ∀ state, 0 ≤ reward state)
    (hsummable : ∀ x, Summable (fun n =>
      pmfExp (pmfProduct (Fin n) Event law) (fun sample =>
        reward (finiteEventTrajectory (initial x) step n sample)))) :
    ∑' n, ∫⁻ z : σ × (ℕ → Event),
      finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2 ∂
        (ρ.prod (measure law.toMeasure)) ≠ ⊤ := by
  let M : Measure (ℕ → Event) := measure law.toMeasure
  let f : ℕ → σ → ENNReal := fun n x =>
    ∫⁻ omega, finiteEventTrajectoryNonnegativeReward (initial x) step reward n omega ∂M
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  have hcomponent : ∀ x, ∑' n, f n x ≠ ⊤ := by
    intro x
    simpa [f, M] using
      (tsum_lintegral_finiteEventTrajectoryNonnegativeReward_ne_top
        law (initial x) step reward hreward (hsummable x))
  have houter : ∀ n,
      ∫⁻ z : σ × (ℕ → Event),
        finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2 ∂
          (ρ.prod M) ≤ ∑ x, f n x := by
    intro n
    rw [MeasureTheory.lintegral_prod _
      (measurable_externalInitial_finiteEventTrajectoryNonnegativeReward_of_finite
        initial step reward n).aemeasurable]
    change (∫⁻ x, f n x ∂ρ) ≤ ∑ x, f n x
    calc
      ∫⁻ x, f n x ∂ρ =
          ∫⁻ x in (↑(Finset.univ : Finset σ) : Set σ), f n x ∂ρ := by simp
      _ = ∑ x ∈ (Finset.univ : Finset σ), f n x * ρ {x} :=
        MeasureTheory.lintegral_finset (Finset.univ : Finset σ) (f n)
      _ ≤ ∑ x ∈ (Finset.univ : Finset σ), f n x := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_of_le_one_right (zero_le _)
        calc
          ρ {x} ≤ ρ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := IsProbabilityMeasure.measure_univ
  have hbound :
      ∑' n, ∫⁻ z : σ × (ℕ → Event),
        finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2 ∂
          (ρ.prod M) ≤ ∑ x, ∑' n, f n x := by
    calc
      ∑' n, ∫⁻ z : σ × (ℕ → Event),
          finiteEventTrajectoryNonnegativeReward (initial z.1) step reward n z.2 ∂
            (ρ.prod M) ≤ ∑' n, ∑ x, f n x :=
        ENNReal.tsum_le_tsum houter
      _ = ∑' n, ∑' x, f n x := by
        congr with n
        exact (tsum_fintype _).symm
      _ = ∑' x, ∑' n, f n x := ENNReal.tsum_comm
      _ = ∑ x, ∑' n, f n x := by
        exact tsum_fintype _
  have hfinite : (∑ x, ∑' n, f n x) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro x _
    exact hcomponent x
  exact ne_top_of_le_ne_top hfinite (by simpa [M] using hbound)

/-- Tonelli identifies the expected finite-event count with the tail sum of
the literal external-initial-state events.  Measurability is explicit because
it belongs to the source-to-model bridge for a random initial state. -/
theorem lintegral_externalInitial_finiteEventTrajectoryEventCount
    {σ State : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (law : PMF Event) (initial : σ → State)
    (step : State → Event → State) (event : State → Prop)
    (hevent : ∀ n, MeasurableSet
      (externalInitialFiniteEventTrajectoryEventSet initial step event n)) :
    ∫⁻ z : σ × (ℕ → Event),
        finiteEventTrajectoryEventCount (initial z.1) step event z.2 ∂
          (ρ.prod (measure law.toMeasure)) =
      ∑' n, (ρ.prod (measure law.toMeasure))
        (externalInitialFiniteEventTrajectoryEventSet initial step event n) := by
  let E : ℕ → Set (σ × (ℕ → Event)) :=
    externalInitialFiniteEventTrajectoryEventSet initial step event
  have hsummand : ∀ n, AEMeasurable
      (fun z : σ × (ℕ → Event) =>
        (finiteEventTrajectoryEventSet (initial z.1) step event n).indicator
          (fun _ => (1 : ENNReal)) z.2)
      (ρ.prod (measure law.toMeasure)) := by
    intro n
    have heq :
        (fun z : σ × (ℕ → Event) =>
          (finiteEventTrajectoryEventSet (initial z.1) step event n).indicator
            (fun _ => (1 : ENNReal)) z.2) =
          (E n).indicator (fun _ => (1 : ENNReal)) := by
      funext z
      simp [E, externalInitialFiniteEventTrajectoryEventSet,
        finiteEventTrajectoryEventSet, Set.indicator]
    rw [heq]
    exact (measurable_const.indicator (hevent n)).aemeasurable
  unfold finiteEventTrajectoryEventCount
  rw [MeasureTheory.lintegral_tsum hsummand]
  apply tsum_congr
  intro n
  change ∫⁻ z : σ × (ℕ → Event),
      (finiteEventTrajectoryEventSet (initial z.1) step event n).indicator
        (fun _ => (1 : ENNReal)) z.2 ∂(ρ.prod (measure law.toMeasure)) = _
  have heq :
      (fun z : σ × (ℕ → Event) =>
        (finiteEventTrajectoryEventSet (initial z.1) step event n).indicator
          (fun _ => (1 : ENNReal)) z.2) =
        (E n).indicator (fun _ => (1 : ENNReal)) := by
    funext z
    simp [E, externalInitialFiniteEventTrajectoryEventSet,
      finiteEventTrajectoryEventSet, Set.indicator]
  rw [heq]
  change ∫⁻ z : σ × (ℕ → Event), (E n).indicator (fun _ => (1 : ENNReal)) z ∂
      (ρ.prod (measure law.toMeasure)) = (ρ.prod (measure law.toMeasure)) (E n)
  exact MeasureTheory.lintegral_indicator_one (hevent n)

/-- A summable finite-product tail gives finite expected trajectory event
count on the literal IID stream. -/
theorem lintegral_finiteEventTrajectoryEventCount_ne_top
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (event : State → Prop) [DecidablePred event]
    (hsummable : Summable
      (finiteEventTrajectoryEventProbability law initial step event)) :
    ∫⁻ omega, finiteEventTrajectoryEventCount initial step event omega ∂
      (measure law.toMeasure) ≠ ⊤ := by
  letI : IsProbabilityMeasure (measure law.toMeasure) := by
    dsimp [measure]
    infer_instance
  rw [lintegral_finiteEventTrajectoryEventCount]
  have hterm : ∀ n,
      ENNReal.ofReal (finiteEventTrajectoryEventProbability law initial step event n) =
        (measure law.toMeasure)
          (finiteEventTrajectoryEventSet initial step event n) := by
    intro n
    rw [← measureReal_finiteEventTrajectoryEvent_eq law initial step event n]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [← tsum_congr hterm]
  exact hsummable.tsum_ofReal_ne_top

/-- Under the same summability hypothesis, the literal IID path visits the
trajectory event only finitely often almost surely. -/
theorem ae_finiteEventTrajectoryEventCount_lt_top
    {State : Type*} (law : PMF Event) (initial : State)
    (step : State → Event → State) (event : State → Prop) [DecidablePred event]
    (hsummable : Summable
      (finiteEventTrajectoryEventProbability law initial step event)) :
    ∀ᵐ omega ∂(measure law.toMeasure),
      finiteEventTrajectoryEventCount initial step event omega < ⊤ := by
  letI : IsProbabilityMeasure (measure law.toMeasure) := by
    dsimp [measure]
    infer_instance
  apply MeasureTheory.ae_lt_top
  · exact measurable_finiteEventTrajectoryEventCount initial step event
  · exact lintegral_finiteEventTrajectoryEventCount_ne_top
      law initial step event hsummable

end

end AppliedModelingLib.Probability.IIDStream
