import AppliedModelingLib.Queueing.ManyServerMarkedUniformization
import AppliedModelingLib.Queueing.ManyServerServiceSemigroup
import AppliedModelingLib.Queueing.ManyServerTrajectory
import AppliedModelingLib.Queueing.ManyServerStationaryMoments
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic

/-!
# Mark-indexed many-server uniformization trajectories

This module augments a many-server uniformized queue by the independent
arrival-versus-potential-service mark that drives its current embedded event.
The queue-state transition still has state-dependent service success, but the
current event kind is a literal Bernoulli coordinate.  The augmented invariant
law factors into the queue-state law and this mark law.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Preorder Filtration
open scoped ENNReal NNReal

noncomputable section

/-- The product PMF of a queue state and its current potential-event mark. -/
def manyServerMarkedStatePMF
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) : PMF (ℕ × Bool) :=
  initial.bind fun state =>
    (manyServerUniformizationArrivalMark trafficIntensity).map
      (fun arrival => (state, arrival))

/-- With zero arrival intensity, the marked initial law retains the queue
state and sets its current potential-event mark to service. -/
theorem manyServerMarkedStatePMF_zero (initial : PMF ℕ) :
    manyServerMarkedStatePMF initial 0 = initial.map (fun state => (state, false)) := by
  unfold manyServerMarkedStatePMF
  rw [manyServerUniformizationArrivalMark_zero]
  simp only [PMF.pure_map]
  simpa [Function.comp_def] using
    (PMF.bind_pure_comp (p := initial) (f := fun state : ℕ => (state, false)))

/-- Under zero traffic, the retained event mark in the marked initial PMF is
almost surely a potential-service mark. -/
theorem manyServerMarkedStatePMF_zero_map_snd (initial : PMF ℕ) :
    (manyServerMarkedStatePMF initial 0).map Prod.snd = PMF.pure false := by
  rw [manyServerMarkedStatePMF_zero, PMF.map_comp]
  change initial.map (Function.const ℕ false) = PMF.pure false
  exact PMF.map_const _ false

/-- Forgetting the retained initial potential-event mark recovers exactly the
specified initial queue-state PMF. -/
theorem manyServerMarkedStatePMF_map_fst
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) :
    (manyServerMarkedStatePMF initial trafficIntensity).map Prod.fst = initial := by
  unfold manyServerMarkedStatePMF
  rw [PMF.map_bind]
  calc
    initial.bind (fun state =>
        ((manyServerUniformizationArrivalMark trafficIntensity).map
          (fun arrival => (state, arrival))).map Prod.fst) =
        initial.bind PMF.pure := by
          apply congrArg (fun transition : ℕ → PMF ℕ => initial.bind transition)
          funext state
          rw [PMF.map_comp]
          change (manyServerUniformizationArrivalMark trafficIntensity).map
              (Function.const Bool state) = PMF.pure state
          exact PMF.map_const _ state
    _ = initial := PMF.bind_pure _

/-- One augmented embedded step consumes the current arrival/potential-service
mark, then draws the independent mark for the next potential event. -/
def manyServerMarkedStateUniformizationKernel
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    CountableMarkovKernel (ℕ × Bool) :=
  fun stateAndArrival =>
    (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
      stateAndArrival.2).bind fun successor =>
        (manyServerUniformizationArrivalMark trafficIntensity).map
          (fun nextArrival => (successor, nextArrival))

/-- From a service mark at zero traffic intensity, an augmented step applies
the service update and retains a service mark for the next potential event. -/
theorem manyServerMarkedStateUniformizationKernel_zero_false
    (servers state : ℕ) (hservers : 0 < servers) :
    manyServerMarkedStateUniformizationKernel 0 servers hservers (state, false) =
      (manyServerUniformizedStateUpdate servers hservers state false).map
        (fun successor => (successor, false)) := by
  unfold manyServerMarkedStateUniformizationKernel
  rw [manyServerUniformizationArrivalMark_zero]
  simp only [PMF.pure_map]
  simpa [Function.comp_def] using
    (PMF.bind_pure_comp
      (p := manyServerUniformizedStateUpdate servers hservers state false)
      (f := fun successor : ℕ => (successor, false)))

/-- At zero traffic intensity, the marked row from a service mark is the
arrival-free row with the service mark retained. -/
theorem manyServerMarkedStateUniformizationKernel_zero_false_eq_serviceOnly
    (servers state : ℕ) (hservers : 0 < servers) :
    manyServerMarkedStateUniformizationKernel 0 servers hservers (state, false) =
      (manyServerServiceOnlyKernel servers hservers state).map
        (fun successor => (successor, false)) := by
  rw [manyServerMarkedStateUniformizationKernel_zero_false,
    ← manyServerServiceOnlyKernel_eq_stateUpdate_false]

/-- Finite zero-traffic marked-chain rows, begun at a service mark, are the
pushforward of the corresponding arrival-free rows. -/
theorem manyServerMarkedStateUniformizationKernel_iterate_zero_false_eq_serviceOnly
    (servers state steps : ℕ) (hservers : 0 < servers) :
    CountableMarkovKernel.iterate
      (manyServerMarkedStateUniformizationKernel 0 servers hservers) steps (state, false) =
      (CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).map
        (fun successor => (successor, false)) := by
  induction steps generalizing state with
  | zero => simp [CountableMarkovKernel.iterate, PMF.pure_map]
  | succ steps ih =>
      change
        (manyServerMarkedStateUniformizationKernel 0 servers hservers (state, false)).bind
            (CountableMarkovKernel.iterate
              (manyServerMarkedStateUniformizationKernel 0 servers hservers) steps) =
          ((manyServerServiceOnlyKernel servers hservers state).bind
            (CountableMarkovKernel.iterate
              (manyServerServiceOnlyKernel servers hservers) steps)).map
            (fun successor => (successor, false))
      rw [manyServerMarkedStateUniformizationKernel_zero_false_eq_serviceOnly]
      rw [PMF.bind_map]
      change
        (manyServerServiceOnlyKernel servers hservers state).bind
            (fun successor =>
              CountableMarkovKernel.iterate
                (manyServerMarkedStateUniformizationKernel 0 servers hservers)
                steps (successor, false)) =
          ((manyServerServiceOnlyKernel servers hservers state).bind
            (CountableMarkovKernel.iterate
              (manyServerServiceOnlyKernel servers hservers) steps)).map
            (fun successor => (successor, false))
      simp_rw [ih]
      rw [PMF.map_bind]

/-- Forgetting the freshly sampled next potential-event mark leaves exactly
the queue-state update driven by the retained current mark. -/
theorem manyServerMarkedStateUniformizationKernel_map_fst
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (stateAndArrival : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers stateAndArrival).map Prod.fst =
      manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
        stateAndArrival.2 := by
  unfold manyServerMarkedStateUniformizationKernel
  rw [PMF.map_bind]
  calc
    (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
        stateAndArrival.2).bind (fun successor =>
          ((manyServerUniformizationArrivalMark trafficIntensity).map
            (fun nextArrival => (successor, nextArrival))).map Prod.fst) =
        (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
          stateAndArrival.2).bind PMF.pure := by
            apply congrArg (fun transition : ℕ → PMF ℕ =>
              (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
                stateAndArrival.2).bind transition)
            funext successor
            rw [PMF.map_comp]
            change (manyServerUniformizationArrivalMark trafficIntensity).map
                (Function.const Bool successor) = PMF.pure successor
            exact PMF.map_const _ successor
    _ = manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
          stateAndArrival.2 := PMF.bind_pure _

/-- The queue-length component of one augmented potential-event step can only
move up by one, move down by one, or remain unchanged.  An arrival mark forces
the upward move; a potential-service mark permits only the latter two cases. -/
def ManyServerMarkedStateStepAllowed (current next : ℕ × Bool) : Prop :=
  if current.2 then next.1 = current.1 + 1 else
    next.1 = current.1 ∨ next.1 = current.1 - 1

/-- The unit arrival contribution of one retained potential-event mark. -/
def manyServerMarkedStateArrivalIncrement (current : ℕ × Bool) : ℕ :=
  if current.2 then 1 else 0

/-- The successful-service contribution of one marked embedded transition.
Potential-service marks that find no busy server contribute zero. -/
def manyServerMarkedStateDepartureIncrement
    (current next : ℕ × Bool) : ℕ :=
  if current.2 then 0 else current.1 - next.1

/-- The potential-service contribution of one retained potential-event mark.
It is one exactly on a potential-service event, whether or not a server is
busy enough to realize that potential service. -/
def manyServerMarkedStatePotentialServiceIncrement (current : ℕ × Bool) : ℕ :=
  if current.2 then 0 else 1

/-- The unused portion of one potential-service event.  On a transition
consistent with the queue dynamics it is an indicator: a potential-service
event that did not complete a job contributes one, and every other event
contributes zero. -/
def manyServerMarkedStateUnrealizedPotentialServiceIncrement
    (current next : ℕ × Bool) : ℕ :=
  manyServerMarkedStatePotentialServiceIncrement current -
    manyServerMarkedStateDepartureIncrement current next

/-- An unrealized potential-service contribution is always an indicator-sized
count, even before restricting to transitions that have positive kernel
probability. -/
theorem manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
    (current next : ℕ × Bool) :
    manyServerMarkedStateUnrealizedPotentialServiceIncrement current next ≤ 1 := by
  unfold manyServerMarkedStateUnrealizedPotentialServiceIncrement
  by_cases hmark : current.2
  · simp [manyServerMarkedStatePotentialServiceIncrement,
      manyServerMarkedStateDepartureIncrement, hmark]
  · simp [manyServerMarkedStatePotentialServiceIncrement,
      manyServerMarkedStateDepartureIncrement, hmark]

/-- The real embedding of an unrealized potential-service increment is
idempotent under squaring because the increment is indicator valued. -/
theorem sq_manyServerMarkedStateUnrealizedPotentialServiceIncrement_eq
    (current next : ℕ × Bool) :
    (manyServerMarkedStateUnrealizedPotentialServiceIncrement current next : ℝ) ^ 2 =
      manyServerMarkedStateUnrealizedPotentialServiceIncrement current next := by
  have hle := manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one current next
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- The real indicator of a measurable history event.  This presentation keeps
the classical decidability choice internal to a reusable finite-history
conditional-expectation API. -/
noncomputable def manyServerMarkedStateHistoryEventIndicator
    {State : Type*} [MeasurableSpace State]
    (historyEvent : Set State) : State → ℝ := by
  classical
  exact fun state => if state ∈ historyEvent then 1 else 0

/-- A marked embedded transition satisfies an exact one-step conservation
identity: the next queue length plus a successful departure equals the
current queue length plus the arrival contribution. -/
theorem ManyServerMarkedStateStepAllowed.queue_balance
    {current next : ℕ × Bool}
    (hstep : ManyServerMarkedStateStepAllowed current next) :
    next.1 + manyServerMarkedStateDepartureIncrement current next =
      current.1 + manyServerMarkedStateArrivalIncrement current := by
  by_cases harrival : current.2
  · simp [ManyServerMarkedStateStepAllowed,
      manyServerMarkedStateArrivalIncrement,
      manyServerMarkedStateDepartureIncrement, harrival] at hstep ⊢
    omega
  · simp [ManyServerMarkedStateStepAllowed,
      manyServerMarkedStateArrivalIncrement,
      manyServerMarkedStateDepartureIncrement, harrival] at hstep ⊢
    rcases hstep with hstay | hdown <;> omega

/-- At one retained potential event, the successful-service and arrival
contributions cannot together exceed one. -/
theorem ManyServerMarkedStateStepAllowed.departureIncrement_add_arrivalIncrement_le_one
    {current next : ℕ × Bool}
    (hstep : ManyServerMarkedStateStepAllowed current next) :
    manyServerMarkedStateDepartureIncrement current next +
        manyServerMarkedStateArrivalIncrement current ≤ 1 := by
  by_cases harrival : current.2
  · simp [ManyServerMarkedStateStepAllowed,
      manyServerMarkedStateArrivalIncrement,
      manyServerMarkedStateDepartureIncrement, harrival] at hstep ⊢
  · simp [ManyServerMarkedStateStepAllowed,
      manyServerMarkedStateArrivalIncrement,
      manyServerMarkedStateDepartureIncrement, harrival] at hstep ⊢
    rcases hstep with hstay | hdown <;> omega

/-- At a transition-consistent marked event, the queue's idle fraction moves
by at most one server's share. -/
theorem ManyServerMarkedStateStepAllowed.abs_idleFraction_sub_le_one_div
    {current next : ℕ × Bool} (servers : ℕ) (hservers : 0 < servers)
    (hstep : ManyServerMarkedStateStepAllowed current next) :
    |(1 - (manyServerBusyFraction servers next.1 : ℝ)) -
        (1 - (manyServerBusyFraction servers current.1 : ℝ))| ≤ 1 / (servers : ℝ) := by
  by_cases harrival : current.2
  · have hnext : next.1 = current.1 + 1 := by
      simpa [ManyServerMarkedStateStepAllowed, harrival] using hstep
    exact abs_one_sub_manyServerBusyFraction_sub_le_one_div
      servers current.1 next.1 hservers (Or.inl hnext)
  · have hnext : next.1 = current.1 ∨ next.1 = current.1 - 1 := by
      simpa [ManyServerMarkedStateStepAllowed, harrival] using hstep
    exact abs_one_sub_manyServerBusyFraction_sub_le_one_div
      servers current.1 next.1 hservers (Or.inr hnext)

/-- At a transition-consistent marked event, realized and unrealized
potential-service contributions partition the potential-service contribution. -/
theorem ManyServerMarkedStateStepAllowed.unrealizedPotentialServiceIncrement_add_departureIncrement_eq_potentialServiceIncrement
    {current next : ℕ × Bool}
    (hstep : ManyServerMarkedStateStepAllowed current next) :
    manyServerMarkedStateUnrealizedPotentialServiceIncrement current next +
        manyServerMarkedStateDepartureIncrement current next =
      manyServerMarkedStatePotentialServiceIncrement current := by
  by_cases harrival : current.2
  · simp [manyServerMarkedStateUnrealizedPotentialServiceIncrement,
      manyServerMarkedStatePotentialServiceIncrement,
      manyServerMarkedStateDepartureIncrement, harrival]
  · simp [manyServerMarkedStateUnrealizedPotentialServiceIncrement,
      manyServerMarkedStatePotentialServiceIncrement,
      manyServerMarkedStateDepartureIncrement, harrival,
      ManyServerMarkedStateStepAllowed] at hstep ⊢
    rcases hstep with hstay | hdown <;> omega

/-- The number of arrival-mark contributions in the first `steps` embedded
potential events of a marked trajectory. -/
def manyServerMarkedStateArrivalPrefix
    (path : ℕ → ℕ × Bool) (steps : ℕ) : ℕ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStateArrivalIncrement (path index)

/-- The number of successful-service contributions in the first `steps`
embedded potential events of a marked trajectory. -/
def manyServerMarkedStateDeparturePrefix
    (path : ℕ → ℕ × Bool) (steps : ℕ) : ℕ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStateDepartureIncrement (path index) (path (index + 1))

/-- The number of potential-service-mark contributions in a finite marked
embedded prefix. -/
def manyServerMarkedStatePotentialServicePrefix
    (path : ℕ → ℕ × Bool) (steps : ℕ) : ℕ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStatePotentialServiceIncrement (path index)

/-- A pathwise lower bound on the queue state obtained by replacing completed
service with all potential-service marks.  It is predictable from the marked
embedded history and is valid for every initial state, independently of any
stationarity assumption. -/
def manyServerMarkedStateArrivalPotentialLowerBound
    (path : ℕ → ℕ × Bool) (steps : ℕ) : ℕ :=
  (path 0).1 + manyServerMarkedStateArrivalPrefix path steps -
    manyServerMarkedStatePotentialServicePrefix path steps

/-- The number of unrealized potential-service contributions in a finite
marked embedded prefix. -/
def manyServerMarkedStateUnrealizedPotentialServicePrefix
    (path : ℕ → ℕ × Bool) (steps : ℕ) : ℕ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStateUnrealizedPotentialServiceIncrement
      (path index) (path (index + 1))

/-- The finite unused-service prefix count is measurable on the marked path
space. -/
theorem measurable_manyServerMarkedStateUnrealizedPotentialServicePrefix
    (steps : ℕ) :
    Measurable (fun path : ℕ → ℕ × Bool =>
      manyServerMarkedStateUnrealizedPotentialServicePrefix path steps) := by
  unfold manyServerMarkedStateUnrealizedPotentialServicePrefix
  apply Finset.measurable_sum
  intro index _
  have hpair : Measurable (fun path : ℕ → ℕ × Bool =>
      (path index, path (index + 1))) :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  exact (measurable_of_countable
    (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      manyServerMarkedStateUnrealizedPotentialServiceIncrement
        statePair.1 statePair.2)).comp
      hpair

/-- A finite unused-service prefix contains at most one unrealized service
per potential event. -/
theorem manyServerMarkedStateUnrealizedPotentialServicePrefix_le_steps
    (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStateUnrealizedPotentialServicePrefix path steps ≤ steps := by
  unfold manyServerMarkedStateUnrealizedPotentialServicePrefix
  calc
    ∑ index ∈ Finset.range steps,
        manyServerMarkedStateUnrealizedPotentialServiceIncrement
          (path index) (path (index + 1)) ≤
        ∑ _index ∈ Finset.range steps, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro index _
          exact manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
            (path index) (path (index + 1))
    _ = steps := by simp

/-- An arrival-mark prefix depends only on the embedded marked states through
the endpoint of that prefix. -/
theorem manyServerMarkedStateArrivalPrefix_congr_prefix
    (steps : ℕ) {first second : ℕ → ℕ × Bool}
    (hprefix : ∀ index ≤ steps, first index = second index) :
    manyServerMarkedStateArrivalPrefix first steps =
      manyServerMarkedStateArrivalPrefix second steps := by
  unfold manyServerMarkedStateArrivalPrefix
  apply Finset.sum_congr rfl
  intro index hindex
  have hindex_lt : index < steps := Finset.mem_range.mp hindex
  unfold manyServerMarkedStateArrivalIncrement
  rw [hprefix index (Nat.le_of_lt hindex_lt)]

/-- A potential-service-mark prefix depends only on the embedded marked
states through the endpoint of that prefix. -/
theorem manyServerMarkedStatePotentialServicePrefix_congr_prefix
    (steps : ℕ) {first second : ℕ → ℕ × Bool}
    (hprefix : ∀ index ≤ steps, first index = second index) :
    manyServerMarkedStatePotentialServicePrefix first steps =
      manyServerMarkedStatePotentialServicePrefix second steps := by
  unfold manyServerMarkedStatePotentialServicePrefix
  apply Finset.sum_congr rfl
  intro index hindex
  have hindex_lt : index < steps := Finset.mem_range.mp hindex
  unfold manyServerMarkedStatePotentialServiceIncrement
  rw [hprefix index (Nat.le_of_lt hindex_lt)]

/-- The arrival-minus-potential-service lower bound is measurable from the
marked history through its displayed embedded index. -/
theorem manyServerMarkedStateArrivalPotentialLowerBound_stronglyAdapted :
    StronglyAdapted piLE
      (fun steps path => manyServerMarkedStateArrivalPotentialLowerBound path steps) := by
  intro steps
  let history : (ℕ → ℕ × Bool) → ((index : Finset.Iic steps) → ℕ × Bool) :=
    Preorder.frestrictLe steps
  let extend : ((index : Finset.Iic steps) → ℕ × Bool) → ℕ → ℕ × Bool :=
    fun past index => if hindex : index ≤ steps then
      past ⟨index, Finset.mem_Iic.mpr hindex⟩ else (0, false)
  let term : ((index : Finset.Iic steps) → ℕ × Bool) → ℕ := fun past =>
    manyServerMarkedStateArrivalPotentialLowerBound (extend past) steps
  have hterm : Measurable term := measurable_of_countable _
  have heq : (fun path => manyServerMarkedStateArrivalPotentialLowerBound path steps) =
      term ∘ history := by
    funext path
    have hprefix : ∀ index ≤ steps, extend (history path) index = path index := by
      intro index hindex
      simp [extend, history, hindex]
    change manyServerMarkedStateArrivalPotentialLowerBound path steps =
      manyServerMarkedStateArrivalPotentialLowerBound (extend (history path)) steps
    symm
    unfold manyServerMarkedStateArrivalPotentialLowerBound
    rw [manyServerMarkedStateArrivalPrefix_congr_prefix steps hprefix,
      manyServerMarkedStatePotentialServicePrefix_congr_prefix steps hprefix,
      hprefix 0 (Nat.zero_le _)]
  change StronglyMeasurable[piLE steps] (fun path =>
    manyServerMarkedStateArrivalPotentialLowerBound path steps)
  rw [heq, piLE_eq_comap_frestrictLe]
  apply Measurable.stronglyMeasurable
  apply Measurable.of_comap_le
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hterm.comap_le

/-- The first embedded index at which the predictable arrival-minus-potential-
service lower bound enters a specified lower region. -/
noncomputable def manyServerMarkedStateArrivalPotentialLowerExitTime
    (lowerThreshold : ℕ) : (ℕ → ℕ × Bool) → ℕ∞ :=
  hittingAfter
    (fun steps path => manyServerMarkedStateArrivalPotentialLowerBound path steps)
    (Set.Iic lowerThreshold) 0

/-- The lower-exit index is a stopping time for the natural marked embedded
filtration. -/
theorem manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime
    (lowerThreshold : ℕ) :
    IsStoppingTime piLE
      (manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold) := by
  apply Adapted.isStoppingTime_hittingAfter
  · exact manyServerMarkedStateArrivalPotentialLowerBound_stronglyAdapted.adapted
  · exact measurableSet_Iic

/-- A finite lower-barrier exit is exactly a finite prefix at which the
arrival-versus-potential-service lower bound enters that barrier. -/
theorem manyServerMarkedStateArrivalPotentialLowerExitTime_le_iff
    (lowerThreshold n : ℕ) (path : ℕ → ℕ × Bool) :
    manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path ≤ (n : ℕ∞) ↔
      ∃ steps ≤ n,
        manyServerMarkedStateArrivalPotentialLowerBound path steps ≤ lowerThreshold := by
  simpa [manyServerMarkedStateArrivalPotentialLowerExitTime, Set.mem_Iic] using
    (hittingAfter_le_iff
      (u := fun steps path => manyServerMarkedStateArrivalPotentialLowerBound path steps)
      (s := Set.Iic lowerThreshold) (n := 0) (i := n) (ω := path))

/-- The paths that remain strictly before the lower-barrier exit at a given
embedded index. -/
def manyServerMarkedStateLowerExitActiveSet
    (lowerThreshold index : ℕ) : Set (ℕ → ℕ × Bool) :=
  {path | (index : ENat) <
    manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path}

/-- Whether the lower-barrier stopping rule remains active at an embedded
index is measurable from the history available at that index. -/
theorem manyServerMarkedStateLowerExitActiveSet_measurableSet
    (lowerThreshold index : ℕ) :
    MeasurableSet[piLE index]
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index) := by
  apply MeasurableSet.of_compl
  simpa only [manyServerMarkedStateLowerExitActiveSet, Set.compl_setOf, not_lt] using
    manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime
      lowerThreshold index

/-- Strictly before the lower-exit index, the predictable lower bound remains
strictly above its specified threshold. -/
theorem lowerThreshold_lt_manyServerMarkedStateArrivalPotentialLowerBound_of_lt_lowerExitTime
    (lowerThreshold steps : ℕ) (path : ℕ → ℕ × Bool)
    (hbefore : (steps : ℕ∞) <
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path) :
    lowerThreshold < manyServerMarkedStateArrivalPotentialLowerBound path steps := by
  have hnot : manyServerMarkedStateArrivalPotentialLowerBound path steps ∉
      Set.Iic lowerThreshold :=
    notMem_of_lt_hittingAfter
      (u := fun index path =>
        manyServerMarkedStateArrivalPotentialLowerBound path index)
      (s := Set.Iic lowerThreshold) (n := 0) (ω := path)
      hbefore (Nat.zero_le _)
  simpa only [Set.mem_Iic, not_le] using hnot

/-- The finite arrival-mark prefix cannot contain more contributions than its
number of embedded events. -/
theorem manyServerMarkedStateArrivalPrefix_le_steps
    (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStateArrivalPrefix path steps ≤ steps := by
  unfold manyServerMarkedStateArrivalPrefix
  calc
    (∑ index ∈ Finset.range steps,
        manyServerMarkedStateArrivalIncrement (path index)) ≤
        ∑ _index ∈ Finset.range steps, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro index _
          by_cases harrival : (path index).2 <;>
            simp [manyServerMarkedStateArrivalIncrement, harrival]
    _ = steps := by simp

/-- Arrival contributions are nonnegative, so the finite marked-arrival
prefix is monotone in the number of embedded potential events. -/
theorem monotone_manyServerMarkedStateArrivalPrefix
    (path : ℕ → ℕ × Bool) :
    Monotone (manyServerMarkedStateArrivalPrefix path) := by
  intro first second hfirstsecond
  induction second, hfirstsecond using Nat.le_induction with
  | base => exact le_rfl
  | succ second _ ih =>
      have hsucc :
          manyServerMarkedStateArrivalPrefix path (second + 1) =
            manyServerMarkedStateArrivalPrefix path second +
              manyServerMarkedStateArrivalIncrement (path second) := by
        unfold manyServerMarkedStateArrivalPrefix
        rw [Finset.sum_range_succ]
      rw [hsucc]
      exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- Potential-service contributions are nonnegative, so their finite marked
prefix is monotone in the number of embedded potential events. -/
theorem monotone_manyServerMarkedStatePotentialServicePrefix
    (path : ℕ → ℕ × Bool) :
    Monotone (manyServerMarkedStatePotentialServicePrefix path) := by
  intro first second hfirstsecond
  induction second, hfirstsecond using Nat.le_induction with
  | base => exact le_rfl
  | succ second _ ih =>
      have hsucc :
          manyServerMarkedStatePotentialServicePrefix path (second + 1) =
            manyServerMarkedStatePotentialServicePrefix path second +
              manyServerMarkedStatePotentialServiceIncrement (path second) := by
        unfold manyServerMarkedStatePotentialServicePrefix
        rw [Finset.sum_range_succ]
      rw [hsucc]
      exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- The finite arrival-prefix sum is exactly the retained-mark count of the
corresponding finite Boolean vector. -/
theorem manyServerMarkedStateArrivalPrefix_eq_keptInMarks
    (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStateArrivalPrefix path steps =
      FiniteHorizonMarkedPoisson.keptInMarks
        (fun index : Fin steps => (path index).2) := by
  unfold manyServerMarkedStateArrivalPrefix
  rw [FiniteHorizonMarkedPoisson.keptInMarks_eq_sum_indicator]
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun index : ℕ => if (path index).2 = true then 1 else 0) steps

/-- Potential-service marks complement arrival marks in each finite embedded
prefix. -/
theorem manyServerMarkedStatePotentialServicePrefix_eq_steps_sub_arrivalPrefix
    (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStatePotentialServicePrefix path steps =
      steps - manyServerMarkedStateArrivalPrefix path steps := by
  induction steps with
  | zero => simp [manyServerMarkedStatePotentialServicePrefix,
      manyServerMarkedStateArrivalPrefix]
  | succ steps ih =>
      have hpotential_succ :
          manyServerMarkedStatePotentialServicePrefix path (steps + 1) =
            manyServerMarkedStatePotentialServicePrefix path steps +
              manyServerMarkedStatePotentialServiceIncrement (path steps) := by
        unfold manyServerMarkedStatePotentialServicePrefix
        rw [Finset.sum_range_succ]
      have harrival_succ :
          manyServerMarkedStateArrivalPrefix path (steps + 1) =
            manyServerMarkedStateArrivalPrefix path steps +
              manyServerMarkedStateArrivalIncrement (path steps) := by
        unfold manyServerMarkedStateArrivalPrefix
        rw [Finset.sum_range_succ]
      rw [hpotential_succ, harrival_succ, ih]
      have harrival_le := manyServerMarkedStateArrivalPrefix_le_steps path steps
      by_cases harrival : (path steps).2
      · simp only [manyServerMarkedStatePotentialServiceIncrement,
          manyServerMarkedStateArrivalIncrement, harrival, ↓reduceIte] at ⊢
        omega
      · simp only [manyServerMarkedStatePotentialServiceIncrement,
          manyServerMarkedStateArrivalIncrement, harrival,
          Bool.false_eq_true, ↓reduceIte] at ⊢
        omega

/-- Replacing each completed service by a potential-service mark leaves a
real-valued lower bound whose net arrival component is at least twice the
arrival count minus the number of embedded events. -/
theorem two_mul_manyServerMarkedStateArrivalPrefix_sub_steps_le_arrivalPotentialLowerBound
    (path : ℕ → ℕ × Bool) (steps : ℕ) :
    ((path 0).1 : ℝ) + 2 * (manyServerMarkedStateArrivalPrefix path steps : ℝ) -
        (steps : ℝ) ≤
      (manyServerMarkedStateArrivalPotentialLowerBound path steps : ℝ) := by
  let arrivals := manyServerMarkedStateArrivalPrefix path steps
  let lowerBound := manyServerMarkedStateArrivalPotentialLowerBound path steps
  have harrivals : arrivals ≤ steps := by
    simpa [arrivals] using manyServerMarkedStateArrivalPrefix_le_steps path steps
  have hpotential : manyServerMarkedStatePotentialServicePrefix path steps =
      steps - arrivals := by
    simpa [arrivals] using
      manyServerMarkedStatePotentialServicePrefix_eq_steps_sub_arrivalPrefix path steps
  have hbase : (path 0).1 + arrivals ≤
      ((path 0).1 + arrivals - (steps - arrivals)) + (steps - arrivals) := by
    exact le_tsub_add
  have hnat : (path 0).1 + arrivals + arrivals ≤ steps + lowerBound := by
    dsimp [lowerBound, manyServerMarkedStateArrivalPotentialLowerBound]
    rw [hpotential]
    omega
  have hreal : ((path 0).1 : ℝ) + (arrivals : ℝ) + (arrivals : ℝ) ≤
      (steps : ℝ) + (lowerBound : ℝ) := by
    exact_mod_cast hnat
  dsimp [arrivals, lowerBound] at hreal ⊢
  linarith

/-- The potential-service prefix is exactly the finite count of `false`
retained marks. -/
theorem manyServerMarkedStatePotentialServicePrefix_eq_discardedInMarks
    (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStatePotentialServicePrefix path steps =
      FiniteHorizonMarkedPoisson.discardedInMarks
        (fun index : Fin steps => (path index).2) := by
  rw [manyServerMarkedStatePotentialServicePrefix_eq_steps_sub_arrivalPrefix,
    manyServerMarkedStateArrivalPrefix_eq_keptInMarks]
  rfl

/-- On a transition-consistent finite prefix, the unrealized potential-service
count is potential service minus completed service. -/
theorem manyServerMarkedStateUnrealizedPotentialServicePrefix_eq_potentialServicePrefix_sub_departurePrefix
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (steps : ℕ) :
    manyServerMarkedStateUnrealizedPotentialServicePrefix path steps =
      manyServerMarkedStatePotentialServicePrefix path steps -
        manyServerMarkedStateDeparturePrefix path steps := by
  have hpartition :
      manyServerMarkedStateUnrealizedPotentialServicePrefix path steps +
          manyServerMarkedStateDeparturePrefix path steps =
        manyServerMarkedStatePotentialServicePrefix path steps := by
    induction steps with
    | zero => simp [manyServerMarkedStateUnrealizedPotentialServicePrefix,
        manyServerMarkedStateDeparturePrefix, manyServerMarkedStatePotentialServicePrefix]
    | succ steps ih =>
        unfold manyServerMarkedStateUnrealizedPotentialServicePrefix
          manyServerMarkedStateDeparturePrefix
          manyServerMarkedStatePotentialServicePrefix at ih ⊢
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        have hlocal :=
          (hstep steps).unrealizedPotentialServiceIncrement_add_departureIncrement_eq_potentialServiceIncrement
        omega
  omega

/-- Successful services plus arrivals cannot exceed the number of embedded
potential events in any transition-consistent finite prefix. -/
theorem manyServerMarkedStateDeparturePrefix_add_arrivalPrefix_le_steps
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (steps : ℕ) :
    manyServerMarkedStateDeparturePrefix path steps +
        manyServerMarkedStateArrivalPrefix path steps ≤ steps := by
  induction steps with
  | zero => simp [manyServerMarkedStateArrivalPrefix,
      manyServerMarkedStateDeparturePrefix]
  | succ steps ih =>
      unfold manyServerMarkedStateArrivalPrefix
        manyServerMarkedStateDeparturePrefix at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hlocal := (hstep steps).departureIncrement_add_arrivalIncrement_le_one
      omega

/-- In a transition-consistent prefix, completed services are no more numerous
than potential-service marks. -/
theorem manyServerMarkedStateDeparturePrefix_le_discardedInMarks
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (steps : ℕ) :
    manyServerMarkedStateDeparturePrefix path steps ≤
      FiniteHorizonMarkedPoisson.discardedInMarks
        (fun index : Fin steps => (path index).2) := by
  rw [FiniteHorizonMarkedPoisson.discardedInMarks,
    ← manyServerMarkedStateArrivalPrefix_eq_keptInMarks]
  exact Nat.le_sub_of_add_le
    (manyServerMarkedStateDeparturePrefix_add_arrivalPrefix_le_steps path hstep steps)

/-- Telescoping the exact marked one-step balances gives the finite embedded
queue conservation law.  It is deterministic once the marked path satisfies
the transition rule. -/
theorem manyServerMarkedState_queue_balance_prefix
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (steps : ℕ) :
    (path steps).1 + manyServerMarkedStateDeparturePrefix path steps =
      (path 0).1 + manyServerMarkedStateArrivalPrefix path steps := by
  induction steps with
  | zero => simp [manyServerMarkedStateArrivalPrefix,
      manyServerMarkedStateDeparturePrefix]
  | succ steps ih =>
      unfold manyServerMarkedStateArrivalPrefix
        manyServerMarkedStateDeparturePrefix at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hlocal := (hstep steps).queue_balance
      omega

/-- On a transition-valid finite prefix with only potential-service marks,
the unused-service count is the potential-event count minus the queue loss. -/
theorem manyServerMarkedStateUnrealizedPotentialServicePrefix_eq_steps_sub_queueLoss_of_serviceMarks
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (steps : ℕ) (hmarks : ∀ index ≤ steps, (path index).2 = false) :
    manyServerMarkedStateUnrealizedPotentialServicePrefix path steps =
      steps - ((path 0).1 - (path steps).1) := by
  have harrivals : manyServerMarkedStateArrivalPrefix path steps = 0 := by
    unfold manyServerMarkedStateArrivalPrefix
    apply Finset.sum_eq_zero
    intro index hindex
    have hindex_le : index ≤ steps := Nat.le_of_lt (Finset.mem_range.mp hindex)
    simp [manyServerMarkedStateArrivalIncrement, hmarks index hindex_le]
  have hpotential : manyServerMarkedStatePotentialServicePrefix path steps = steps := by
    rw [manyServerMarkedStatePotentialServicePrefix_eq_steps_sub_arrivalPrefix,
      harrivals, Nat.sub_zero]
  have hbalance := manyServerMarkedState_queue_balance_prefix path hstep steps
  have hdepartures : manyServerMarkedStateDeparturePrefix path steps =
      (path 0).1 - (path steps).1 := by
    rw [harrivals] at hbalance
    omega
  rw [manyServerMarkedStateUnrealizedPotentialServicePrefix_eq_potentialServicePrefix_sub_departurePrefix
    path hstep steps, hpotential, hdepartures]

/-- Along a transition-consistent prefix, the actual queue length dominates
the predictable arrival-minus-potential-service lower bound. -/
theorem manyServerMarkedStateArrivalPotentialLowerBound_le_queueLength
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (steps : ℕ) :
    manyServerMarkedStateArrivalPotentialLowerBound path steps ≤ (path steps).1 := by
  have hdeparture_le_potential :
      manyServerMarkedStateDeparturePrefix path steps ≤
        manyServerMarkedStatePotentialServicePrefix path steps := by
    rw [manyServerMarkedStatePotentialServicePrefix_eq_discardedInMarks]
    exact manyServerMarkedStateDeparturePrefix_le_discardedInMarks path hstep steps
  have hbalance := manyServerMarkedState_queue_balance_prefix path hstep steps
  unfold manyServerMarkedStateArrivalPotentialLowerBound
  omega

/-- Before the lower-exit index, the actual marked queue length is strictly
above the specified threshold. -/
theorem lowerThreshold_lt_manyServerMarkedStateQueueLength_of_lt_lowerExitTime
    (lowerThreshold steps : ℕ) (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (hbefore : (steps : ℕ∞) <
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path) :
    lowerThreshold < (path steps).1 := by
  exact lt_of_lt_of_le
    (lowerThreshold_lt_manyServerMarkedStateArrivalPotentialLowerBound_of_lt_lowerExitTime
      lowerThreshold steps path hbefore)
    (manyServerMarkedStateArrivalPotentialLowerBound_le_queueLength path hstep steps)

/-- Before the lower-exit index, the idle fraction is bounded by its value at
the specified lower threshold. -/
theorem one_sub_manyServerBusyFraction_le_of_lt_lowerExitTime
    (servers lowerThreshold steps : ℕ) (path : ℕ → ℕ × Bool)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (hbefore : (steps : ℕ∞) <
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path) :
    1 - (manyServerBusyFraction servers (path steps).1 : ℝ) ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  apply antitone_one_sub_manyServerBusyFraction servers
  exact Nat.le_of_lt
    (lowerThreshold_lt_manyServerMarkedStateQueueLength_of_lt_lowerExitTime
      lowerThreshold steps path hstep hbefore)

/-- Every support point of the augmented state kernel has a queue update
consistent with its retained current potential-event mark. -/
theorem manyServerMarkedStateUniformizationKernel_support_stepAllowed
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current next : ℕ × Bool)
    (hnext : next ∈
      (manyServerMarkedStateUniformizationKernel
        trafficIntensity servers hservers current).support) :
    ManyServerMarkedStateStepAllowed current next := by
  rcases (PMF.mem_support_bind_iff _ _ next).mp hnext with
    ⟨successor, hsuccessor, hnextMark⟩
  rcases (PMF.mem_support_map_iff
    (fun nextArrival => (successor, nextArrival))
    (manyServerUniformizationArrivalMark trafficIntensity) next).mp hnextMark with
    ⟨nextArrival, _, hpair⟩
  cases current with
  | mk state arrival =>
    cases arrival with
    | false =>
        change successor ∈
          ((PMF.bernoulli (manyServerBusyFraction servers state)
            (manyServerBusyFraction_le_one servers state hservers)).map
            (fun service => if service then state - 1 else state)).support at hsuccessor
        rcases (PMF.mem_support_map_iff
          (fun service => if service then state - 1 else state)
          (PMF.bernoulli (manyServerBusyFraction servers state)
            (manyServerBusyFraction_le_one servers state hservers)) successor).mp hsuccessor with
          ⟨service, _, hservice⟩
        change next.1 = state ∨ next.1 = state - 1
        have hstate : next.1 = successor := (congrArg Prod.fst hpair).symm
        cases service <;> simp at hservice
        · exact Or.inl (hstate.trans hservice.symm)
        · exact Or.inr (hstate.trans hservice.symm)
    | true =>
        change successor ∈ (PMF.pure (state + 1)).support at hsuccessor
        have hsuccessor_eq : successor = state + 1 :=
          (PMF.mem_support_pure_iff (a := state + 1) (a' := successor)).mp hsuccessor
        change next.1 = state + 1
        exact (congrArg Prod.fst hpair).symm.trans hsuccessor_eq

/-- Conditional on the current marked state, the successful-service
contribution is the literal busy-fraction Bernoulli update; an arrival-marked
event has the degenerate zero contribution.  The subtraction form correctly
also treats a service-attempt mark selected on an empty queue. -/
theorem manyServerMarkedStateUniformizationKernel_map_departureIncrement
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers current).map
        (manyServerMarkedStateDepartureIncrement current) =
      if current.2 then PMF.pure 0 else
        (PMF.bernoulli (manyServerBusyFraction servers current.1)
          (manyServerBusyFraction_le_one servers current.1 hservers)).map
          (fun service => current.1 -
            (if service then current.1 - 1 else current.1)) := by
  unfold manyServerMarkedStateUniformizationKernel
  rw [PMF.map_bind]
  cases current with
  | mk state arrival =>
      cases arrival with
      | false =>
          simp only [manyServerUniformizedStateUpdate]
          calc
            ((PMF.bernoulli (manyServerBusyFraction servers state)
              (manyServerBusyFraction_le_one servers state hservers)).map
              (fun service => if service then state - 1 else state)).bind
                (fun successor =>
                  ((manyServerUniformizationArrivalMark trafficIntensity).map
                    (fun nextArrival => (successor, nextArrival))).map
                    (fun next => state - next.1)) =
                ((PMF.bernoulli (manyServerBusyFraction servers state)
                  (manyServerBusyFraction_le_one servers state hservers)).map
                  (fun service => if service then state - 1 else state)).bind
                    (fun successor => PMF.pure (state - successor)) := by
                      congr 1
                      funext successor
                      rw [PMF.map_comp]
                      change (manyServerUniformizationArrivalMark trafficIntensity).map
                        (Function.const Bool (state - successor)) = _
                      exact PMF.map_const _ _
            _ = ((PMF.bernoulli (manyServerBusyFraction servers state)
                  (manyServerBusyFraction_le_one servers state hservers)).map
                  (fun service => if service then state - 1 else state)).map
                    (fun successor => state - successor) := by
                      simpa [Function.comp_def] using
                        (PMF.bind_pure_comp (fun successor : ℕ => state - successor)
                          ((PMF.bernoulli (manyServerBusyFraction servers state)
                            (manyServerBusyFraction_le_one servers state hservers)).map
                            (fun service => if service then state - 1 else state)))
            _ = (PMF.bernoulli (manyServerBusyFraction servers state)
                  (manyServerBusyFraction_le_one servers state hservers)).map
                    (fun service => state -
                      (if service then state - 1 else state)) := by
                      rw [PMF.map_comp]
                      rfl
      | true =>
          simp only [manyServerUniformizedStateUpdate, ↓reduceIte]
          rw [PMF.pure_bind]
          rw [PMF.map_comp]
          change (manyServerUniformizationArrivalMark trafficIntensity).map
            (Function.const Bool 0) = PMF.pure 0
          exact PMF.map_const _ _

/-- The entire conditional law of the unrealized-potential-service increment.
On a potential-service mark, it is the complement of the busy-fraction
Bernoulli service-completion draw; on an arrival mark it is identically zero. -/
theorem manyServerMarkedStateUniformizationKernel_map_unrealizedPotentialServiceIncrement
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers current).map
        (manyServerMarkedStateUnrealizedPotentialServiceIncrement current) =
      if current.2 then PMF.pure 0 else
        (PMF.bernoulli (manyServerBusyFraction servers current.1)
          (manyServerBusyFraction_le_one servers current.1 hservers)).map
          (fun service => if service then 0 else 1) := by
  cases current with
  | mk state arrival =>
      cases arrival with
      | true =>
          unfold manyServerMarkedStateUniformizationKernel
          rw [PMF.map_bind]
          simp only [manyServerUniformizedStateUpdate, ↓reduceIte]
          rw [PMF.pure_bind]
          rw [PMF.map_comp]
          change (manyServerUniformizationArrivalMark trafficIntensity).map
            (Function.const Bool 0) = PMF.pure 0
          exact PMF.map_const _ _
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          calc
            ((manyServerMarkedStateUniformizationKernel
              trafficIntensity servers hservers (state, false)).map
                (manyServerMarkedStateUnrealizedPotentialServiceIncrement
                  (state, false))) =
                ((PMF.bernoulli (manyServerBusyFraction servers state)
                  (manyServerBusyFraction_le_one servers state hservers)).map
                    (fun service => if service then state - 1 else state)).bind
                  (fun successor => PMF.pure (1 - (state - successor))) := by
                    unfold manyServerMarkedStateUniformizationKernel
                    rw [PMF.map_bind]
                    simp only [manyServerUniformizedStateUpdate]
                    apply congrArg (fun transition : ℕ → PMF ℕ =>
                      ((PMF.bernoulli (manyServerBusyFraction servers state)
                        (manyServerBusyFraction_le_one servers state hservers)).map
                        (fun service => if service then state - 1 else state)).bind
                          transition)
                    funext successor
                    rw [PMF.map_comp]
                    change (manyServerUniformizationArrivalMark trafficIntensity).map
                      (Function.const Bool (1 - (state - successor))) = _
                    exact PMF.map_const _ _
            _ = ((PMF.bernoulli (manyServerBusyFraction servers state)
                  (manyServerBusyFraction_le_one servers state hservers)).map
                  (fun service => if service then state - 1 else state)).map
                  (fun successor => 1 - (state - successor)) := by
                    simpa [Function.comp_def] using
                      (PMF.bind_pure_comp
                        (fun successor : ℕ => 1 - (state - successor))
                        ((PMF.bernoulli (manyServerBusyFraction servers state)
                          (manyServerBusyFraction_le_one servers state hservers)).map
                          (fun service => if service then state - 1 else state)))
            _ = (PMF.bernoulli (manyServerBusyFraction servers state)
                  (manyServerBusyFraction_le_one servers state hservers)).map
                    (fun service => 1 -
                      (state - (if service then state - 1 else state))) := by
                    rw [PMF.map_comp]
                    rfl
          cases state with
          | zero =>
              apply PMF.ext
              intro value
              simp [PMF.map_apply, PMF.bernoulli_apply,
                manyServerBusyFraction]
          | succ state =>
              have hcorrection :
                  (fun service : Bool => 1 -
                    ((state + 1) -
                      (if service then state + 1 - 1 else state + 1))) =
                    (fun service => if service then 0 else 1) := by
                      funext service
                      cases service <;> simp
              rw [hcorrection]

/-- Conditional on the current marked state, the probability that the current
potential-service opportunity is unrealized is its idle fraction.  Arrival
marks have no potential service and hence give the degenerate zero law. -/
theorem manyServerMarkedStateUniformizationKernel_unrealizedPotentialServiceIncrement_one
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers current).map
        (manyServerMarkedStateUnrealizedPotentialServiceIncrement current) 1 =
      if current.2 then 0 else
        (1 : ℝ≥0∞) - ↑(manyServerBusyFraction servers current.1) := by
  rw [manyServerMarkedStateUniformizationKernel_map_unrealizedPotentialServiceIncrement]
  cases current with
  | mk state arrival =>
      cases arrival with
      | true => simp [PMF.pure_apply]
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [PMF.map_apply]
          simp [PMF.bernoulli_apply]

/-- The real conditional mean of the unrealized-potential-service increment is
the current idle fraction.  This converts the exact one-step PMF law into the
compensator quantity used by cumulative queueing arguments. -/
theorem manyServerMarkedStateUniformizationKernel_unrealizedPotentialServiceIncrement_integral
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) :
    (∫ next,
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement current next : ℝ) ∂
      (manyServerMarkedStateUniformizationKernel
        trafficIntensity servers hservers current).toMeasure) =
      if current.2 then 0 else
        1 - (manyServerBusyFraction servers current.1 : ℝ) := by
  have hle : ∀ next : ℕ × Bool,
      manyServerMarkedStateUnrealizedPotentialServiceIncrement current next ≤ 1 := by
    exact manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one current
  let E : Set (ℕ × Bool) :=
    {next | manyServerMarkedStateUnrealizedPotentialServiceIncrement current next = 1}
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurable_of_countable
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement current)
      (measurableSet_singleton 1)
  have hindicator :
      (fun next : ℕ × Bool =>
        (manyServerMarkedStateUnrealizedPotentialServiceIncrement current next : ℝ)) =
      E.indicator (fun _ : ℕ × Bool => (1 : ℝ)) := by
    funext next
    by_cases hvalue :
      manyServerMarkedStateUnrealizedPotentialServiceIncrement current next = 1
    · simp [E, hvalue]
    · have hzero :
        manyServerMarkedStateUnrealizedPotentialServiceIncrement current next = 0 := by
        have hbound := hle next
        omega
      simp [E, hzero]
  calc
    (∫ next,
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement current next : ℝ) ∂
      (manyServerMarkedStateUniformizationKernel
        trafficIntensity servers hservers current).toMeasure) =
        ((manyServerMarkedStateUniformizationKernel
          trafficIntensity servers hservers current).toMeasure).real E := by
            rw [hindicator]
            exact MeasureTheory.integral_indicator_one hE
    _ = (Measure.map (manyServerMarkedStateUnrealizedPotentialServiceIncrement current)
        (manyServerMarkedStateUniformizationKernel
          trafficIntensity servers hservers current).toMeasure).real {1} := by
            rw [MeasureTheory.map_measureReal_apply
              (measurable_of_countable _) (measurableSet_singleton 1)]
            rfl
    _ = (((manyServerMarkedStateUniformizationKernel
          trafficIntensity servers hservers current).map
            (manyServerMarkedStateUnrealizedPotentialServiceIncrement current)).toMeasure).real
            {1} := by
            rw [PMF.toMeasure_map
              (manyServerMarkedStateUnrealizedPotentialServiceIncrement current)
              (manyServerMarkedStateUniformizationKernel
                trafficIntensity servers hservers current)
              (measurable_of_countable _)]
    _ = ((manyServerMarkedStateUniformizationKernel
          trafficIntensity servers hservers current).map
            (manyServerMarkedStateUnrealizedPotentialServiceIncrement current) 1).toReal := by
            change (((manyServerMarkedStateUniformizationKernel
              trafficIntensity servers hservers current).map
                (manyServerMarkedStateUnrealizedPotentialServiceIncrement current)).toMeasure
                  {1}).toReal = _
            rw [PMF.toMeasure_apply_singleton _ 1 (measurableSet_singleton 1)]
    _ = if current.2 then 0 else
        1 - (manyServerBusyFraction servers current.1 : ℝ) := by
          rw [manyServerMarkedStateUniformizationKernel_unrealizedPotentialServiceIncrement_one]
          split_ifs with hmark
          · norm_num
          · rw [ENNReal.toReal_sub_of_le]
            · simp
            · exact_mod_cast
                manyServerBusyFraction_le_one servers current.1 hservers
            · norm_num

/-- At a positive queue length, the conditional probability of one completed
service at the current potential event is precisely the busy fraction, after
excluding arrival-marked events. -/
theorem manyServerMarkedStateUniformizationKernel_departureIncrement_one
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) (hcurrent : 0 < current.1) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers current).map
        (manyServerMarkedStateDepartureIncrement current) 1 =
      if current.2 then 0 else ↑(manyServerBusyFraction servers current.1) := by
  rw [manyServerMarkedStateUniformizationKernel_map_departureIncrement]
  cases hcurrentMark : current.2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hindicator :
        (fun service : Bool => current.1 -
          (if service then current.1 - 1 else current.1)) =
          (fun service => if service then 1 else 0) := by
      funext service
      cases service
      · simp
      · simp
        omega
    rw [hindicator, PMF.map_apply, tsum_bool]
    rw [PMF.bernoulli_apply, PMF.bernoulli_apply]
    simp
  | true =>
    simp [PMF.pure_apply]

/-- The one-completed-service conditional probability is the busy fraction
for every queue length (including the zero state, where both sides vanish),
after excluding arrival-marked events. -/
theorem manyServerMarkedStateUniformizationKernel_departureIncrement_one_eq_busyFraction
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers current).map
        (manyServerMarkedStateDepartureIncrement current) 1 =
      if current.2 then 0 else ↑(manyServerBusyFraction servers current.1) := by
  rcases current with ⟨state, currentMark⟩
  cases state with
  | zero =>
      rw [manyServerMarkedStateUniformizationKernel_map_departureIncrement]
      cases currentMark <;>
        simp [manyServerBusyFraction, PMF.pure_apply]
  | succ state =>
      exact manyServerMarkedStateUniformizationKernel_departureIncrement_one
        trafficIntensity servers hservers (state + 1, currentMark) (by omega)

/-- Conditional on any current augmented state, the next potential-event mark
has the same state-independent Bernoulli law. -/
theorem manyServerMarkedStateUniformizationKernel_map_snd
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (stateAndArrival : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers stateAndArrival).map Prod.snd =
      manyServerUniformizationArrivalMark trafficIntensity := by
  unfold manyServerMarkedStateUniformizationKernel
  rw [PMF.map_bind]
  calc
    (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
      stateAndArrival.2).bind (fun successor =>
        ((manyServerUniformizationArrivalMark trafficIntensity).map
          (fun nextArrival => (successor, nextArrival))).map Prod.snd) =
      (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
        stateAndArrival.2).bind (fun _ =>
          manyServerUniformizationArrivalMark trafficIntensity) := by
            apply congrArg (fun transition : ℕ → PMF Bool =>
              (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
                stateAndArrival.2).bind transition)
            funext successor
            rw [PMF.map_comp]
            simpa [Function.comp_def] using
              PMF.map_id (manyServerUniformizationArrivalMark trafficIntensity)
    _ = manyServerUniformizationArrivalMark trafficIntensity := PMF.bind_const _ _

/-- Conditional on a current augmented state, retaining its current mark and
the next mark gives the current-mark singleton paired with a fresh Bernoulli
draw. -/
theorem manyServerMarkedStateUniformizationKernel_map_currentNextArrivalMark
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (stateAndArrival : ℕ × Bool) :
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers stateAndArrival).map
        (fun nextStateAndArrival =>
          (stateAndArrival.2, nextStateAndArrival.2)) =
      (manyServerUniformizationArrivalMark trafficIntensity).map
        (fun nextArrival => (stateAndArrival.2, nextArrival)) := by
  unfold manyServerMarkedStateUniformizationKernel
  rw [PMF.map_bind]
  calc
    (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
      stateAndArrival.2).bind (fun successor =>
        ((manyServerUniformizationArrivalMark trafficIntensity).map
          (fun nextArrival => (successor, nextArrival))).map
            (fun nextStateAndArrival =>
              (stateAndArrival.2, nextStateAndArrival.2))) =
      (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
        stateAndArrival.2).bind (fun _ =>
          (manyServerUniformizationArrivalMark trafficIntensity).map
            (fun nextArrival => (stateAndArrival.2, nextArrival))) := by
            apply congrArg (fun transition : ℕ → PMF (Bool × Bool) =>
              (manyServerUniformizedStateUpdate servers hservers stateAndArrival.1
                stateAndArrival.2).bind transition)
            funext successor
            rw [PMF.map_comp]
            rfl
    _ = (manyServerUniformizationArrivalMark trafficIntensity).map
          (fun nextArrival => (stateAndArrival.2, nextArrival)) := PMF.bind_const _ _

/-- The finite PMF of two independent Boolean draws is the corresponding
monadic two-draw law. -/
private theorem manyServer_arrivalPair_bind_eq_pmfProd (mark : PMF Bool) :
    mark.bind (fun arrival => mark.map fun nextArrival => (arrival, nextArrival)) =
      AppliedModelingLib.pmfProd mark mark := by
  apply PMF.ext
  rintro ⟨arrival, nextArrival⟩
  cases arrival <;> cases nextArrival <;>
    simp [PMF.bind_apply, PMF.map_apply, AppliedModelingLib.pmfProd_apply]

/-- The joint PMF of the current and next potential-event marks when starting
from an arbitrary queue-state law and an independent current mark. -/
def manyServerCurrentNextArrivalMarkPMF
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) : PMF (Bool × Bool) :=
  (manyServerMarkedStatePMF initial trafficIntensity).bind
    (fun stateAndArrival =>
      (manyServerMarkedStateUniformizationKernel
        trafficIntensity servers hservers stateAndArrival).map
        (fun nextStateAndArrival =>
          (stateAndArrival.2, nextStateAndArrival.2)))

/-- The current and next event marks are independent Bernoulli draws, for
every initial queue-state PMF. -/
theorem manyServerCurrentNextArrivalMarkPMF_eq_pmfProd
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    manyServerCurrentNextArrivalMarkPMF initial trafficIntensity servers hservers =
      AppliedModelingLib.pmfProd (manyServerUniformizationArrivalMark trafficIntensity)
        (manyServerUniformizationArrivalMark trafficIntensity) := by
  let mark := manyServerUniformizationArrivalMark trafficIntensity
  calc
    manyServerCurrentNextArrivalMarkPMF initial trafficIntensity servers hservers =
        initial.bind fun _state => mark.bind fun arrival =>
          mark.map fun nextArrival => (arrival, nextArrival) := by
            unfold manyServerCurrentNextArrivalMarkPMF manyServerMarkedStatePMF
            rw [PMF.bind_bind]
            congr 1
            funext state
            rw [PMF.bind_map]
            apply congrArg (fun transition : Bool → PMF (Bool × Bool) => mark.bind transition)
            funext arrival
            dsimp [mark]
            exact manyServerMarkedStateUniformizationKernel_map_currentNextArrivalMark
              trafficIntensity servers hservers (state, arrival)
    _ = mark.bind fun arrival => mark.map fun nextArrival => (arrival, nextArrival) := by
          rw [PMF.bind_const]
    _ = AppliedModelingLib.pmfProd mark mark := manyServer_arrivalPair_bind_eq_pmfProd mark

/-- The current/next mark PMF is the mark projection of the ordinary
initial/transition-pair PMF of the augmented chain. -/
theorem manyServerCurrentNextArrivalMarkPMF_eq_initialTransitionPair_map
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    manyServerCurrentNextArrivalMarkPMF initial trafficIntensity servers hservers =
      (CountableMarkovKernel.initialTransitionPairPMF
        (manyServerMarkedStatePMF initial trafficIntensity)
        (manyServerMarkedStateUniformizationKernel
          trafficIntensity servers hservers)).map
        (fun statePair => (statePair.1.2, statePair.2.2)) := by
  unfold manyServerCurrentNextArrivalMarkPMF
    CountableMarkovKernel.initialTransitionPairPMF
  rw [PMF.map_bind]
  apply congrArg (fun transition : (ℕ × Bool) → PMF (Bool × Bool) =>
    (manyServerMarkedStatePMF initial trafficIntensity).bind transition)
  funext stateAndArrival
  rw [PMF.map_comp]
  rfl

/-- Running the augmented chain from a state/mark product law is the same as
running the unmarked many-server kernel and then drawing a fresh independent
event mark. -/
theorem manyServerMarkedStatePMF_bind_kernel
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    (manyServerMarkedStatePMF initial trafficIntensity).bind
      (manyServerMarkedStateUniformizationKernel trafficIntensity servers hservers) =
      manyServerMarkedStatePMF
        (initial.bind (manyServerUniformizedKernel trafficIntensity servers hservers))
        trafficIntensity := by
  let mark := manyServerUniformizationArrivalMark trafficIntensity
  calc
    (manyServerMarkedStatePMF initial trafficIntensity).bind
        (manyServerMarkedStateUniformizationKernel trafficIntensity servers hservers) =
        initial.bind fun state => mark.bind fun arrival =>
          (manyServerUniformizedStateUpdate servers hservers state arrival).bind
            fun successor => mark.map fun nextArrival => (successor, nextArrival) := by
              unfold manyServerMarkedStatePMF manyServerMarkedStateUniformizationKernel
              rw [PMF.bind_bind]
              congr 1
              funext state
              rw [PMF.bind_map]
              rfl
    _ = initial.bind fun state =>
          (mark.bind (manyServerUniformizedStateUpdate servers hservers state)).bind
            fun successor => mark.map fun nextArrival => (successor, nextArrival) := by
              congr 1
              funext state
              rw [PMF.bind_bind]
    _ = manyServerMarkedStatePMF
        (initial.bind (manyServerUniformizedKernel trafficIntensity servers hservers))
        trafficIntensity := by
          unfold manyServerMarkedStatePMF
          rw [PMF.bind_bind]
          apply congrArg (fun transition : ℕ → PMF (ℕ × Bool) => initial.bind transition)
          funext state
          dsimp [mark]
          rw [← manyServerUniformizedKernel_eq_arrivalMark_bind]

/-- After one marked embedded transition, forgetting the newly retained mark
has exactly the ordinary many-server one-step queue-state law. -/
theorem manyServerMarkedStatePMF_bind_kernel_map_fst
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    ((manyServerMarkedStatePMF initial trafficIntensity).bind
      (manyServerMarkedStateUniformizationKernel trafficIntensity servers hservers)).map
        Prod.fst =
      initial.bind (manyServerUniformizedKernel trafficIntensity servers hservers) := by
  rw [manyServerMarkedStatePMF_bind_kernel]
  exact manyServerMarkedStatePMF_map_fst _ _

/-- Iterating the marked embedded chain is the same as iterating the ordinary
many-server chain and then adjoining one fresh current potential-event mark.
This is an exact PMF identity, with no stationarity hypothesis. -/
theorem manyServerMarkedStatePMF_bind_iterate
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (steps : ℕ) :
    (manyServerMarkedStatePMF initial trafficIntensity).bind
        (CountableMarkovKernel.iterate
          (manyServerMarkedStateUniformizationKernel
            trafficIntensity servers hservers) steps) =
      manyServerMarkedStatePMF
        (initial.bind (CountableMarkovKernel.iterate
          (manyServerUniformizedKernel trafficIntensity servers hservers) steps))
        trafficIntensity := by
  induction steps generalizing initial with
  | zero =>
      simp [CountableMarkovKernel.iterate]
  | succ steps ih =>
      rw [CountableMarkovKernel.iterate_succ, ← PMF.bind_bind,
        manyServerMarkedStatePMF_bind_kernel]
      simpa [CountableMarkovKernel.iterate_succ, ← PMF.bind_bind] using
        ih (initial.bind (manyServerUniformizedKernel
          trafficIntensity servers hservers))

/-- An invariant unmarked many-server PMF induces an invariant augmented PMF
with an independent current arrival/potential-service mark. -/
theorem manyServerMarkedStatePMF_stationary
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial) :
    PMFStationary
      (manyServerMarkedStateUniformizationKernel trafficIntensity servers hservers)
      (manyServerMarkedStatePMF initial trafficIntensity) := by
  unfold PMFStationary
  rw [manyServerMarkedStatePMF_bind_kernel, hstationary]

/-- Measure-valued realization of the marked many-server embedded kernel. -/
noncomputable def manyServerMarkedStateUniformizationMeasureKernel
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    Kernel (ℕ × Bool) (ℕ × Bool) :=
  countablePMFKernel
    (manyServerMarkedStateUniformizationKernel trafficIntensity servers hservers)

instance (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
  unfold manyServerMarkedStateUniformizationMeasureKernel
  infer_instance

/-- At every deterministic embedded index, the marked trajectory has the
iterated marked-state PMF.  This is the arbitrary-initial-law marginal
semantics of the retained-mark construction. -/
theorem manyServerMarkedStateTrajectory_stateAt_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool => path index)
      ((manyServerMarkedStatePMF initial trafficIntensity).bind
        (CountableMarkovKernel.iterate
          (manyServerMarkedStateUniformizationKernel
            trafficIntensity servers hservers) index)).toMeasure
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  have hpair := stationaryTrajMeasure_zero_n_pair_hasLaw
    (π := (manyServerMarkedStatePMF initial trafficIntensity).toMeasure)
    (K := manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers) index
  have hterminal : HasLaw Prod.snd
      ((manyServerMarkedStatePMF initial trafficIntensity).bind
        (CountableMarkovKernel.iterate
          (manyServerMarkedStateUniformizationKernel
            trafficIntensity servers hservers) index)).toMeasure
      ((manyServerMarkedStatePMF initial trafficIntensity).toMeasure ⊗ₘ
        ((manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers) ^ index)) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    letI : IsSFiniteKernel
        ((countablePMFKernel
          (manyServerMarkedStateUniformizationKernel
            trafficIntensity servers hservers)) ^ index) :=
      isSFiniteKernel_pow _ index
    change
      ((manyServerMarkedStatePMF initial trafficIntensity).toMeasure ⊗ₘ
        ((countablePMFKernel
          (manyServerMarkedStateUniformizationKernel
            trafficIntensity servers hservers)) ^ index)).snd = _
    rw [Measure.snd_compProd,
      ← CountableMarkovKernel.countablePMFKernel_iterate_eq_pow,
      bind_countablePMFKernel_eq_pmf_bind_toMeasure]
  simpa [Function.comp_def] using hterminal.comp hpair

/-- At zero traffic intensity, every fixed finite prefix of a marked
many-server trajectory has only potential-service marks. -/
theorem ae_manyServerMarkedStateTrajectory_serviceMarks_false_of_zero
    (initial : PMF ℕ) (servers : ℕ) (hservers : 0 < servers) (steps : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial 0).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel 0 servers hservers),
      ∀ index ≤ steps, (path index).2 = false := by
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial 0).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel 0 servers hservers)
  have hmark : ∀ index : ℕ,
      HasLaw (fun path : ℕ → ℕ × Bool => (path index).2) (PMF.pure false).toMeasure
        trajectory := by
    intro index
    have hstate := manyServerMarkedStateTrajectory_stateAt_hasLaw
      initial 0 servers hservers index
    rw [manyServerMarkedStatePMF_bind_iterate] at hstate
    have hprojection : HasLaw Prod.snd (PMF.pure false).toMeasure
        (manyServerMarkedStatePMF
          (initial.bind (CountableMarkovKernel.iterate
            (manyServerUniformizedKernel 0 servers hservers) index)) 0).toMeasure := by
      refine ⟨measurable_snd.aemeasurable, ?_⟩
      rw [PMF.toMeasure_map Prod.snd
        (manyServerMarkedStatePMF
          (initial.bind (CountableMarkovKernel.iterate
            (manyServerUniformizedKernel 0 servers hservers) index)) 0)
        (measurable_of_countable _), manyServerMarkedStatePMF_zero_map_snd]
    simpa [trajectory, Function.comp_def] using hprojection.comp hstate
  have hmarkFalse : ∀ index : ℕ, ∀ᵐ path ∂trajectory, (path index).2 = false := by
    intro index
    refine ((hmark index).ae_iff (p := fun mark : Bool => mark = false)
      (measurable_of_countable _)).2 ?_
    simp only [PMF.toMeasure_pure, ae_dirac_eq, Filter.eventually_pure]
  induction steps with
  | zero =>
      filter_upwards [hmarkFalse 0] with path hzero index hindex
      have hindex_zero : index = 0 := Nat.eq_zero_of_le_zero hindex
      subst index
      exact hzero
  | succ steps ih =>
      filter_upwards [ih, hmarkFalse (steps + 1)] with path hprefix hlast index hindex
      rcases Nat.lt_or_eq_of_le hindex with hlt | heq
      · exact hprefix index (Nat.le_of_lt_succ hlt)
      · subst index
        exact hlast

/-- Forgetting the retained mark at every deterministic embedded index gives
the same one-time state law as the ordinary many-server uniformized chain.
This is the coordinate-level corollary of the finite-prefix and complete-path
bridge developed in `ManyServerMarkedStatePrefix`. -/
theorem manyServerMarkedStateTrajectory_queueStateAt_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool => (path index).1)
      (initial.bind (CountableMarkovKernel.iterate
        (manyServerUniformizedKernel trafficIntensity servers hservers) index)).toMeasure
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  have hstate := manyServerMarkedStateTrajectory_stateAt_hasLaw
    initial trafficIntensity servers hservers index
  rw [manyServerMarkedStatePMF_bind_iterate] at hstate
  have hprojection : HasLaw Prod.fst
      (initial.bind (CountableMarkovKernel.iterate
        (manyServerUniformizedKernel trafficIntensity servers hservers) index)).toMeasure
      (manyServerMarkedStatePMF
        (initial.bind (CountableMarkovKernel.iterate
          (manyServerUniformizedKernel trafficIntensity servers hservers) index))
        trafficIntensity).toMeasure := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [PMF.toMeasure_map Prod.fst _ (measurable_of_countable _),
      manyServerMarkedStatePMF_map_fst]
  simpa [Function.comp_def] using hprojection.comp hstate

/-- At each deterministic embedded index, forgetting marks from the marked
trajectory and the ordinary uniformized trajectory gives the same queue-state
law.  The complete embedded path-law equality is established in
`ManyServerMarkedStatePrefix`; this remains a lightweight coordinate form. -/
theorem manyServerMarkedStateTrajectory_queueStateAt_map_eq_unmarked
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    Measure.map (fun path : ℕ → ℕ × Bool => (path index).1)
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) =
      Measure.map (fun path : ℕ → ℕ => path index)
        (manyServerUniformizedEmbeddedTrajectoryMeasure
          initial.toMeasure trafficIntensity servers hservers) := by
  have hmarked := manyServerMarkedStateTrajectory_queueStateAt_hasLaw
    initial trafficIntensity servers hservers index
  have hunmarked := manyServerUniformizedEmbeddedTrajectory_stateAt_hasLaw
    initial trafficIntensity servers hservers index
  rw [hmarked.map_eq, hunmarked.map_eq]

/-- Forgetting the next queue state from the augmented transition leaves the
constant Bernoulli potential-event-mark kernel. -/
theorem manyServerMarkedStateUniformizationMeasureKernel_map_snd
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers).map Prod.snd =
      Kernel.const (ℕ × Bool)
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
  ext stateAndArrival event hEvent
  rw [Kernel.map_apply _ (measurable_of_countable _)]
  change Measure.map Prod.snd
    ((manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers stateAndArrival).toMeasure) event = _
  rw [PMF.toMeasure_map Prod.snd
    (manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers stateAndArrival)
    (measurable_of_countable _),
    manyServerMarkedStateUniformizationKernel_map_snd]
  rfl

/-- The next retained arrival mark has its state-independent Bernoulli mean
under every current augmented queue state. -/
theorem manyServerMarkedStateUniformizationMeasureKernel_nextArrivalMark_integral
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (current : ℕ × Bool) :
    (∫ next : ℕ × Bool,
      if next.2 then (1 : ℝ) else 0 ∂
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers) current) =
      (uniformizedBirthProbability trafficIntensity : ℝ) := by
  let kernel := manyServerMarkedStateUniformizationMeasureKernel
    trafficIntensity servers hservers
  let arrivalIndicator : Bool → ℝ := fun arrival => if arrival then 1 else 0
  have hmap :
      (∫ arrival : Bool, arrivalIndicator arrival ∂(kernel current).map Prod.snd) =
        ∫ next : ℕ × Bool, arrivalIndicator next.2 ∂kernel current :=
    MeasureTheory.integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable
  rw [← hmap]
  rw [← Kernel.map_apply _ (measurable_of_countable _)]
  rw [show kernel.map Prod.snd = Kernel.const (ℕ × Bool)
      (manyServerUniformizationArrivalMark trafficIntensity).toMeasure by
    exact manyServerMarkedStateUniformizationMeasureKernel_map_snd
      trafficIntensity servers hservers]
  simpa [arrivalIndicator] using
    integral_manyServerUniformizationArrivalMark_arrival trafficIntensity

/-- The next arrival-mark indicator retains its state-independent mean after
weighting by any event determined by the marked history through the current
embedded index. -/
theorem manyServerMarkedStateTrajectory_nextArrivalMark_history_indicator_integral_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ)
    (historyEvent : Set ((i : Finset.Iic index) → ℕ × Bool))
    (hhistoryEvent : MeasurableSet historyEvent) :
    (∫ path,
      manyServerMarkedStateHistoryEventIndicator historyEvent
        (Preorder.frestrictLe index path) *
        (if (path (index + 1)).2 then (1 : ℝ) else 0) ∂
      stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) =
      ∫ path,
        manyServerMarkedStateHistoryEventIndicator historyEvent
          (Preorder.frestrictLe index path) *
          (uniformizedBirthProbability trafficIntensity : ℝ) ∂
        stationaryTrajMeasure
          (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
          (manyServerMarkedStateUniformizationMeasureKernel
            trafficIntensity servers hservers) := by
  classical
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let history : (ℕ → ℕ × Bool) → ((i : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let last : ((i : Finset.Iic index) → ℕ × Bool) → ℕ × Bool :=
    fun past => past ⟨index, Finset.mem_Iic.mpr le_rfl⟩
  let historyKernel : Kernel ((i : Finset.Iic index) → ℕ × Bool) (ℕ × Bool) :=
    measureKernel ∘ₖ Kernel.deterministic last (measurable_pi_apply _)
  let historyMeasure : Measure ((i : Finset.Iic index) → ℕ × Bool) :=
    trajectory.map history
  let historyNext : (ℕ → ℕ × Bool) →
      ((i : Finset.Iic index) → ℕ × Bool) × (ℕ × Bool) :=
    fun path => (history path, path (index + 1))
  let weight : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    manyServerMarkedStateHistoryEventIndicator historyEvent
  let increment : (ℕ × Bool) × (ℕ × Bool) → ℝ :=
    fun statePair => if statePair.2.2 then 1 else 0
  let mean : ℝ := uniformizedBirthProbability trafficIntensity
  let integrand : ((i : Finset.Iic index) → ℕ × Bool) × (ℕ × Bool) → ℝ :=
    fun historyPair => weight historyPair.1 * increment (last historyPair.1, historyPair.2)
  let right : (ℕ → ℕ × Bool) → ℝ :=
    fun path => weight (history path) * mean
  let pastRight : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    fun past => weight past * mean
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  letI : IsFiniteMeasure historyMeasure := by
    dsimp [historyMeasure]
    infer_instance
  letI : IsFiniteMeasure (historyMeasure ⊗ₘ historyKernel) := by infer_instance
  have hhistory : Measurable history := Preorder.measurable_frestrictLe index
  have hhistoryNext : Measurable historyNext :=
    hhistory.prodMk (measurable_pi_apply (index + 1))
  have hintegrand : Measurable integrand := measurable_of_countable _
  have hintegrand_int : Integrable integrand (historyMeasure ⊗ₘ historyKernel) := by
    apply Integrable.of_bound hintegrand.aestronglyMeasurable 1
    filter_upwards [] with historyPair
    by_cases hmem : historyPair.1 ∈ historyEvent
    · simp [integrand, weight, increment,
        manyServerMarkedStateHistoryEventIndicator, hmem]
      split <;> norm_num
    · simp [integrand, weight, increment,
        manyServerMarkedStateHistoryEventIndicator, hmem]
  have hhistoryLaw : Measure.map historyNext trajectory = historyMeasure ⊗ₘ historyKernel := by
    exact stationaryTrajMeasure_prefix_succ
      (π := markedInitial.toMeasure) (K := measureKernel) index
  have hpastRight : Measurable pastRight := measurable_of_countable _
  have hright_eq : right = pastRight ∘ history := by
    funext path
    rfl
  change (∫ path, integrand (historyNext path) ∂trajectory) = ∫ path, right path ∂trajectory
  calc
    (∫ path, integrand (historyNext path) ∂trajectory) =
        ∫ historyPair, integrand historyPair ∂Measure.map historyNext trajectory := by
          symm
          exact integral_map hhistoryNext.aemeasurable hintegrand.aestronglyMeasurable
    _ = ∫ historyPair, integrand historyPair ∂(historyMeasure ⊗ₘ historyKernel) := by
          rw [hhistoryLaw]
    _ = ∫ past, ∫ next, integrand (past, next) ∂historyKernel past ∂historyMeasure := by
          rw [Measure.integral_compProd hintegrand_int]
    _ = ∫ past, weight past * mean ∂historyMeasure := by
          apply integral_congr_ae
          filter_upwards [] with past
          by_cases hmem : past ∈ historyEvent
          · simp [integrand, weight, increment,
              manyServerMarkedStateHistoryEventIndicator, hmem]
            rw [show historyKernel past = measureKernel (last past) by
              dsimp [historyKernel]
              rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]]
            dsimp [mean, measureKernel]
            exact manyServerMarkedStateUniformizationMeasureKernel_nextArrivalMark_integral
              trafficIntensity servers hservers (last past)
          · simp [integrand, weight, increment,
              manyServerMarkedStateHistoryEventIndicator, hmem]
    _ = ∫ path, pastRight (history path) ∂trajectory := by
          exact integral_map hhistory.aemeasurable hpastRight.aestronglyMeasurable
    _ = ∫ path, right path ∂trajectory := by
          rw [hright_eq]
          rfl

/-- Conditional on the marked embedded history through an index, the next
arrival-mark indicator has the state-independent Bernoulli mean. -/
theorem manyServerMarkedStateTrajectory_nextArrivalMark_condExp_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[(fun path => if (path (index + 1)).2 then (1 : ℝ) else 0) |
      piLE index] =ᵐ[trajectory]
      fun _ => (uniformizedBirthProbability trafficIntensity : ℝ) := by
  classical
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let f : (ℕ → ℕ × Bool) → ℝ :=
    fun path => if (path (index + 1)).2 then 1 else 0
  let g : (ℕ → ℕ × Bool) → ℝ :=
    fun _ => (uniformizedBirthProbability trafficIntensity : ℝ)
  let history : (ℕ → ℕ × Bool) → ((i : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let pastMean : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    fun _ => (uniformizedBirthProbability trafficIntensity : ℝ)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hfmeas : Measurable f :=
    (measurable_of_countable (fun state : ℕ × Bool =>
      if state.2 then (1 : ℝ) else 0)).comp
      (measurable_pi_apply (index + 1))
  have hf : Integrable f trajectory := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [f]
    split <;> norm_num
  have hg : Integrable g trajectory := integrable_const _
  have hg_eq : g = pastMean ∘ history := by
    funext path
    rfl
  have hgm : AEStronglyMeasurable[piLE index] g trajectory := by
    rw [hg_eq, piLE_eq_comap_frestrictLe]
    apply StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (show Measurable pastMean by exact measurable_of_countable _).comap_le
  change trajectory[f | piLE index] =ᵐ[trajectory] g
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le index) hf
    (fun s _ _ => hg.integrableOn) ?_ hgm
  rintro s hs _
  rw [piLE_eq_comap_frestrictLe] at hs
  rcases hs with ⟨historyEvent, hhistoryEvent, rfl⟩
  have hcomp :=
    manyServerMarkedStateTrajectory_nextArrivalMark_history_indicator_integral_from_initial
      initial trafficIntensity servers hservers index historyEvent hhistoryEvent
  have hEvent : MeasurableSet (history ⁻¹' historyEvent) :=
    hhistoryEvent.preimage (Preorder.measurable_frestrictLe index)
  rw [← integral_indicator hEvent, ← integral_indicator hEvent]
  calc
    ∫ x, (history ⁻¹' historyEvent).indicator g x ∂trajectory =
        ∫ path,
          manyServerMarkedStateHistoryEventIndicator historyEvent (history path) *
            (uniformizedBirthProbability trafficIntensity : ℝ) ∂trajectory := by
              apply integral_congr_ae
              filter_upwards [] with path
              by_cases hmem : history path ∈ historyEvent <;>
                simp [Set.indicator, manyServerMarkedStateHistoryEventIndicator,
                  hmem, g]
    _ = ∫ path,
          manyServerMarkedStateHistoryEventIndicator historyEvent (history path) *
            f path ∂trajectory := by
              simpa [trajectory, markedInitial, measureKernel, history, f] using hcomp.symm
    _ = ∫ x, (history ⁻¹' historyEvent).indicator f x ∂trajectory := by
              symm
              apply integral_congr_ae
              filter_upwards [] with path
              by_cases hmem : history path ∈ historyEvent <;>
                simp [Set.indicator, manyServerMarkedStateHistoryEventIndicator,
                  hmem, f]

/-- The centered fresh arrival mark at an embedded step.  Using the mark at
`index + 1` makes it a fresh draw relative to the history through `index`. -/
def manyServerMarkedStateCenteredNextArrivalMarkIncrement
    (trafficIntensity : ℝ≥0) (index : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  (if (path (index + 1)).2 then 1 else 0) -
    (uniformizedBirthProbability trafficIntensity : ℝ)

/-- The centered partial sum of the fresh uniformization arrival marks. -/
def manyServerMarkedStateCenteredNextArrivalMarkPartialSum
    (trafficIntensity : ℝ≥0) (steps : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index path

/-- The idle fraction just before an embedded potential event.  Unlike the
retained current mark, this state coordinate is available before the next
fresh arrival-versus-potential-service mark is sampled. -/
noncomputable def manyServerMarkedStateIdleFractionAt
    (servers : ℕ) (index : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  1 - (manyServerBusyFraction servers (path index).1 : ℝ)

/-- The centered contribution of the next fresh potential-service mark,
weighted by the idle fraction at the current embedded state. -/
noncomputable def manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
    (trafficIntensity : ℝ≥0) (servers : ℕ) (index : ℕ)
    (path : ℕ → ℕ × Bool) : ℝ :=
  ((uniformizedBirthProbability trafficIntensity : ℝ) -
      (if (path (index + 1)).2 then 1 else 0)) *
    manyServerMarkedStateIdleFractionAt servers index path

/-- The embedded partial sum of fresh-mark centered idle contributions. -/
noncomputable def manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
    (trafficIntensity : ℝ≥0) (servers steps : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
      trafficIntensity servers index path

/-- The next-mark potential-service idle reward accumulated over an embedded
prefix. -/
noncomputable def manyServerMarkedStateNextPotentialServiceIdlePrefix
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) : ℝ :=
  ∑ index ∈ Finset.range steps,
    (if (path (index + 1)).2 then 0 else
      manyServerMarkedStateIdleFractionAt servers index path)

/-- The unmarked idle-fraction sum over an embedded prefix. -/
noncomputable def manyServerMarkedStateIdleFractionPrefix
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) : ℝ :=
  ∑ index ∈ Finset.range steps,
    manyServerMarkedStateIdleFractionAt servers index path

/-- The centered fresh-mark idle sum is exactly its literal next-mark reward
minus the uniformized potential-service mean times the state idle sum. -/
theorem manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_eq
    (trafficIntensity : ℝ≥0) (servers steps : ℕ) (path : ℕ → ℕ × Bool) :
    manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers steps path =
      manyServerMarkedStateNextPotentialServiceIdlePrefix servers path steps -
        (1 - (uniformizedBirthProbability trafficIntensity : ℝ)) *
          manyServerMarkedStateIdleFractionPrefix servers path steps := by
  unfold manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
    manyServerMarkedStateNextPotentialServiceIdlePrefix
    manyServerMarkedStateIdleFractionPrefix
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  unfold manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
  cases hmark : (path (index + 1)).2 <;>
    simp [hmark] <;> ring

/-- An idle fraction lies in the unit interval. -/
theorem manyServerMarkedStateIdleFractionAt_nonneg_le_one
    (servers index : ℕ) (path : ℕ → ℕ × Bool) (hservers : 0 < servers) :
    0 ≤ manyServerMarkedStateIdleFractionAt servers index path ∧
      manyServerMarkedStateIdleFractionAt servers index path ≤ 1 := by
  unfold manyServerMarkedStateIdleFractionAt
  have hbusy_nonneg :
      0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
  have hbusy_le :
      (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
    exact_mod_cast manyServerBusyFraction_le_one servers (path index).1 hservers
  constructor <;> linarith

/-- The current idle fraction is measurable with respect to the retained
marked history through its embedded index. -/
theorem stronglyMeasurable_manyServerMarkedStateIdleFractionAt
    (servers index : ℕ) :
    StronglyMeasurable[piLE index]
      (manyServerMarkedStateIdleFractionAt servers index) := by
  let history : (ℕ → ℕ × Bool) → ((j : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let term : ((j : Finset.Iic index) → ℕ × Bool) → ℝ := fun past =>
    1 - (manyServerBusyFraction servers
      (past ⟨index, Finset.mem_Iic.mpr le_rfl⟩).1 : ℝ)
  have hterm : Measurable term := measurable_of_countable _
  have heq : manyServerMarkedStateIdleFractionAt servers index = term ∘ history := by
    funext path
    rfl
  rw [heq, piLE_eq_comap_frestrictLe]
  apply Measurable.stronglyMeasurable
  apply Measurable.of_comap_le
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hterm.comap_le

/-- A fresh-mark centered idle contribution has absolute value at most one. -/
theorem abs_manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_le_one
    (trafficIntensity : ℝ≥0) (servers index : ℕ)
    (path : ℕ → ℕ × Bool) (hservers : 0 < servers) :
    |manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
      trafficIntensity servers index path| ≤ 1 := by
  have hprob_nonneg : 0 ≤ (uniformizedBirthProbability trafficIntensity : ℝ) := by
    positivity
  have hprob_le_one : (uniformizedBirthProbability trafficIntensity : ℝ) ≤ 1 := by
    exact_mod_cast uniformizedBirthProbability_le_one trafficIntensity
  have hidle := manyServerMarkedStateIdleFractionAt_nonneg_le_one
    servers index path hservers
  have hmark : |(uniformizedBirthProbability trafficIntensity : ℝ) -
      (if (path (index + 1)).2 then 1 else 0)| ≤ 1 := by
    cases hnext : (path (index + 1)).2 with
    | false =>
        simpa [hnext, abs_of_nonneg hprob_nonneg] using hprob_le_one
    | true =>
        have hsub_nonpos : (uniformizedBirthProbability trafficIntensity : ℝ) - 1 ≤ 0 :=
          sub_nonpos.mpr hprob_le_one
        change |(uniformizedBirthProbability trafficIntensity : ℝ) - 1| ≤ 1
        rw [abs_of_nonpos hsub_nonpos]
        linarith
  unfold manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
  rw [abs_mul, abs_of_nonneg hidle.1]
  calc
    |(uniformizedBirthProbability trafficIntensity : ℝ) -
        (if (path (index + 1)).2 then 1 else 0)| *
        manyServerMarkedStateIdleFractionAt servers index path ≤ 1 * 1 :=
      mul_le_mul hmark hidle.2 hidle.1 zero_le_one
    _ = 1 := one_mul _

/-- Every fresh-mark centered idle contribution is integrable under the
arbitrary-initial marked trajectory law. -/
theorem integrable_manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Integrable
      (manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
        trafficIntensity servers index)
      trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hmark : Measurable (fun path : ℕ → ℕ × Bool =>
      if (path (index + 1)).2 then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun state : ℕ × Bool =>
      if state.2 then (1 : ℝ) else 0)).comp
      (measurable_pi_apply (index + 1))
  have hidle : Measurable (manyServerMarkedStateIdleFractionAt servers index) := by
    unfold manyServerMarkedStateIdleFractionAt
    exact measurable_const.sub
      ((measurable_of_countable fun state : ℕ × Bool =>
        (manyServerBusyFraction servers state.1 : ℝ)).comp
        (measurable_pi_apply index))
  have hincrement : Measurable
      (manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
        trafficIntensity servers index) := by
    unfold manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
    exact (measurable_const.sub hmark).mul hidle
  apply Integrable.of_bound hincrement.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun path =>
    abs_manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_le_one
      trafficIntensity servers index path hservers

/-- The arrival count in an embedded prefix is its fresh-mark martingale
plus the deterministic Bernoulli mean and the two endpoint marks.  The shift
by one is the cost of making each martingale increment fresh relative to the
preceding queue history. -/
theorem manyServerMarkedStateArrivalPrefix_cast_eq_centeredNextArrivalMarkPartialSum
    (trafficIntensity : ℝ≥0) (steps : ℕ) (path : ℕ → ℕ × Bool) :
    (manyServerMarkedStateArrivalPrefix path steps : ℝ) =
      manyServerMarkedStateCenteredNextArrivalMarkPartialSum trafficIntensity steps path +
        (steps : ℝ) * (uniformizedBirthProbability trafficIntensity : ℝ) +
        (if (path 0).2 then (1 : ℝ) else 0) -
        (if (path steps).2 then (1 : ℝ) else 0) := by
  induction steps with
  | zero =>
      simp [manyServerMarkedStateArrivalPrefix,
        manyServerMarkedStateCenteredNextArrivalMarkPartialSum]
  | succ steps ih =>
      have harrival :
          (manyServerMarkedStateArrivalPrefix path steps.succ : ℝ) =
            (manyServerMarkedStateArrivalPrefix path steps : ℝ) +
              (if (path steps).2 then (1 : ℝ) else 0) := by
        simp only [manyServerMarkedStateArrivalPrefix,
          manyServerMarkedStateArrivalIncrement, Finset.sum_range_succ,
          Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have hcentered :
          manyServerMarkedStateCenteredNextArrivalMarkPartialSum
              trafficIntensity steps.succ path =
            manyServerMarkedStateCenteredNextArrivalMarkPartialSum
              trafficIntensity steps path +
              ((if (path (steps + 1)).2 then (1 : ℝ) else 0) -
                (uniformizedBirthProbability trafficIntensity : ℝ)) := by
        unfold manyServerMarkedStateCenteredNextArrivalMarkPartialSum
        rw [Finset.sum_range_succ]
        rfl
      rw [harrival, ih, hcentered]
      norm_num [Nat.cast_succ]
      ring

/-- The predictable arrival-versus-potential-service lower bound dominates
the fresh arrival-mark martingale plus its deterministic uniformization drift.
The two endpoint marks are the exact cost of shifting to fresh increments. -/
theorem manyServerMarkedStateCenteredNextArrivalMark_lowerBound
    (trafficIntensity : ℝ≥0) (steps : ℕ) (path : ℕ → ℕ × Bool) :
    ((path 0).1 : ℝ) +
        2 * manyServerMarkedStateCenteredNextArrivalMarkPartialSum
          trafficIntensity steps path +
        (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) * (steps : ℝ) +
        2 * (if (path 0).2 then (1 : ℝ) else 0) -
        2 * (if (path steps).2 then (1 : ℝ) else 0) ≤
      (manyServerMarkedStateArrivalPotentialLowerBound path steps : ℝ) := by
  have hlower :=
    two_mul_manyServerMarkedStateArrivalPrefix_sub_steps_le_arrivalPotentialLowerBound
      path steps
  rw [manyServerMarkedStateArrivalPrefix_cast_eq_centeredNextArrivalMarkPartialSum
    trafficIntensity steps path] at hlower
  nlinarith [hlower]

/-- Each fresh centered mark is bounded in absolute value by one. -/
theorem abs_manyServerMarkedStateCenteredNextArrivalMarkIncrement_le_one
    (trafficIntensity : ℝ≥0) (index : ℕ) (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateCenteredNextArrivalMarkIncrement
      trafficIntensity index path| ≤ 1 := by
  have hprob_nonneg : 0 ≤ (uniformizedBirthProbability trafficIntensity : ℝ) := by
    positivity
  have hprob_le_one : (uniformizedBirthProbability trafficIntensity : ℝ) ≤ 1 := by
    exact_mod_cast uniformizedBirthProbability_le_one trafficIntensity
  cases hmark : (path (index + 1)).2 with
  | false =>
      simpa [manyServerMarkedStateCenteredNextArrivalMarkIncrement, hmark,
        abs_of_nonneg hprob_nonneg] using hprob_le_one
  | true =>
      have hnonneg : 0 ≤ 1 - (uniformizedBirthProbability trafficIntensity : ℝ) := by
        linarith
      have hle : 1 - (uniformizedBirthProbability trafficIntensity : ℝ) ≤ 1 := by
        linarith
      simpa [manyServerMarkedStateCenteredNextArrivalMarkIncrement, hmark,
        abs_of_nonneg hnonneg] using hle

/-- The fresh centered mark is integrable under every marked many-server
trajectory law. -/
theorem integrable_manyServerMarkedStateCenteredNextArrivalMarkIncrement_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Integrable
      (manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index)
      trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hmeas : Measurable
      (manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index) := by
    unfold manyServerMarkedStateCenteredNextArrivalMarkIncrement
    exact ((measurable_of_countable (fun state : ℕ × Bool =>
      if state.2 then (1 : ℝ) else 0)).comp
      (measurable_pi_apply (index + 1))).sub measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun path =>
    abs_manyServerMarkedStateCenteredNextArrivalMarkIncrement_le_one
      trafficIntensity index path

/-- The centered fresh arrival mark has conditional mean zero given the
marked queue history before it is sampled. -/
theorem manyServerMarkedStateCenteredNextArrivalMarkIncrement_condExp_eq_zero_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index |
      piLE index] =ᵐ[trajectory] 0 := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let f : (ℕ → ℕ × Bool) → ℝ :=
    fun path => if (path (index + 1)).2 then 1 else 0
  let g : (ℕ → ℕ × Bool) → ℝ :=
    fun _ => (uniformizedBirthProbability trafficIntensity : ℝ)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hfmeas : Measurable f :=
    (measurable_of_countable (fun state : ℕ × Bool =>
      if state.2 then (1 : ℝ) else 0)).comp
      (measurable_pi_apply (index + 1))
  have hf : Integrable f trajectory := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [f]
    split <;> norm_num
  have hg : Integrable g trajectory := integrable_const _
  have hgstrong : StronglyMeasurable[piLE index] g := stronglyMeasurable_const
  have hmean :=
    manyServerMarkedStateTrajectory_nextArrivalMark_condExp_from_initial
      initial trafficIntensity servers hservers index
  change trajectory[
    manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index |
    piLE index] =ᵐ[trajectory] 0
  change trajectory[f - g | piLE index] =ᵐ[trajectory] 0
  calc
    trajectory[f - g | piLE index] =ᵐ[trajectory]
        trajectory[f | piLE index] - trajectory[g | piLE index] :=
      condExp_sub hf hg _
    _ =ᵐ[trajectory] g - trajectory[g | piLE index] := by
      exact hmean.sub (Filter.Eventually.of_forall fun _ => rfl)
    _ =ᵐ[trajectory] 0 := by
      rw [condExp_of_stronglyMeasurable (piLE.le index) hgstrong hg]
      exact Filter.Eventually.of_forall fun _ => sub_self _

/-- The cumulative fresh centered arrival marks are adapted to the natural
marked-history filtration. -/
theorem manyServerMarkedStateCenteredNextArrivalMarkPartialSum_stronglyAdapted
    (trafficIntensity : ℝ≥0) :
    StronglyAdapted piLE
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum trafficIntensity) := by
  intro steps
  unfold manyServerMarkedStateCenteredNextArrivalMarkPartialSum
  have hsum : StronglyMeasurable[piLE steps]
      (∑ index ∈ Finset.range steps,
        manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index) := by
    apply Finset.stronglyMeasurable_sum
    intro index hindex
    have hindex_lt : index < steps := Finset.mem_range.mp hindex
    let history : (ℕ → ℕ × Bool) → ((j : Finset.Iic steps) → ℕ × Bool) :=
      Preorder.frestrictLe steps
    let term : ((j : Finset.Iic steps) → ℕ × Bool) → ℝ := fun past =>
      (if (past ⟨index + 1,
        Finset.mem_Iic.mpr (Nat.succ_le_of_lt hindex_lt)⟩).2 then 1 else 0) -
        (uniformizedBirthProbability trafficIntensity : ℝ)
    have hterm : Measurable term := measurable_of_countable _
    have heq : manyServerMarkedStateCenteredNextArrivalMarkIncrement
        trafficIntensity index = term ∘ history := by
      funext path
      rfl
    rw [heq, piLE_eq_comap_frestrictLe]
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hterm.comap_le
  convert hsum using 1
  ext path
  simp

/-- Fresh centered arrival-mark partial sums form a martingale under every
initial many-server marked trajectory law. -/
theorem manyServerMarkedStateCenteredNextArrivalMarkPartialSum_martingale_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Martingale
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum trafficIntensity)
      piLE trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  apply AppliedModelingLib.martingale_partial_sum_of_condExp_eq_zero
  · exact manyServerMarkedStateCenteredNextArrivalMarkPartialSum_stronglyAdapted
      trafficIntensity
  · intro n
    apply integrable_finset_sum
    intro i _
    simpa [trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredNextArrivalMarkIncrement_from_initial
        initial trafficIntensity servers hservers i
  · intro n
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextArrivalMarkIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers n

/-- A fresh potential-service mark, weighted by the current idle fraction,
has conditional mean zero after subtracting its state-independent mark mean. -/
theorem manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_condExp_eq_zero_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
        trafficIntensity servers index | piLE index] =ᵐ[trajectory] 0 := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let weight : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateIdleFractionAt servers index
  let noise : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity index
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hweight : StronglyMeasurable[piLE index] weight := by
    simpa [weight] using
      stronglyMeasurable_manyServerMarkedStateIdleFractionAt servers index
  have hnoise : Integrable noise trajectory := by
    simpa [noise, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredNextArrivalMarkIncrement_from_initial
        initial trafficIntensity servers hservers index
  have hnoise_meas : Measurable noise := by
    unfold noise manyServerMarkedStateCenteredNextArrivalMarkIncrement
    exact ((measurable_of_countable (fun state : ℕ × Bool =>
      if state.2 then (1 : ℝ) else 0)).comp
      (measurable_pi_apply (index + 1))).sub measurable_const
  have hproduct : Integrable (fun path => weight path * noise path) trajectory := by
    apply Integrable.of_bound
      ((hweight.mono (piLE.le index)).aestronglyMeasurable.mul
        hnoise_meas.aestronglyMeasurable) 1
    filter_upwards [] with path
    have hidle := manyServerMarkedStateIdleFractionAt_nonneg_le_one
      servers index path hservers
    have hnoise_bound := abs_manyServerMarkedStateCenteredNextArrivalMarkIncrement_le_one
      trafficIntensity index path
    change |weight path * noise path| ≤ 1
    rw [abs_mul, abs_of_nonneg hidle.1]
    exact mul_le_one₀ hidle.2 (abs_nonneg _) hnoise_bound
  have hnoise_zero : trajectory[noise | piLE index] =ᵐ[trajectory] 0 := by
    simpa [noise, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextArrivalMarkIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers index
  have hincrement_eq :
      manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
          trafficIntensity servers index =
        fun path => -(weight path * noise path) := by
    funext path
    unfold manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
    dsimp [weight, noise, manyServerMarkedStateCenteredNextArrivalMarkIncrement]
    ring
  calc
    trajectory[manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
        trafficIntensity servers index | piLE index] =ᵐ[trajectory]
        trajectory[(fun path => -(weight path * noise path)) | piLE index] := by
          apply condExp_congr_ae
          exact Filter.Eventually.of_forall fun path => congrFun hincrement_eq path
    _ =ᵐ[trajectory] -trajectory[(fun path => weight path * noise path) | piLE index] :=
      condExp_neg _ _
    _ =ᵐ[trajectory] -(weight * trajectory[noise | piLE index]) := by
      exact (condExp_mul_of_stronglyMeasurable_left hweight hproduct hnoise).neg
    _ =ᵐ[trajectory] 0 := by
      filter_upwards [hnoise_zero] with path hzero
      simp [hzero]

/-- Fresh-mark centered idle partial sums are adapted to the retained marked
history filtration. -/
theorem manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_stronglyAdapted
    (trafficIntensity : ℝ≥0) (servers : ℕ) :
    StronglyAdapted piLE
      (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers) := by
  intro steps
  unfold manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
  have hsum : StronglyMeasurable[piLE steps]
      (∑ index ∈ Finset.range steps,
        manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
          trafficIntensity servers index) := by
    apply Finset.stronglyMeasurable_sum
    intro index hindex
    have hindex_lt : index < steps := Finset.mem_range.mp hindex
    let history : (ℕ → ℕ × Bool) → ((j : Finset.Iic steps) → ℕ × Bool) :=
      Preorder.frestrictLe steps
    let term : ((j : Finset.Iic steps) → ℕ × Bool) → ℝ := fun past =>
      ((uniformizedBirthProbability trafficIntensity : ℝ) -
          (if (past ⟨index + 1,
            Finset.mem_Iic.mpr (Nat.succ_le_of_lt hindex_lt)⟩).2 then 1 else 0)) *
        (1 - (manyServerBusyFraction servers
          (past ⟨index, Finset.mem_Iic.mpr (Nat.le_of_lt hindex_lt)⟩).1 : ℝ))
    have hterm : Measurable term := measurable_of_countable _
    have heq : manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
        trafficIntensity servers index = term ∘ history := by
      funext path
      rfl
    rw [heq, piLE_eq_comap_frestrictLe]
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hterm.comap_le
  convert hsum using 1
  ext path
  simp

/-- Fresh-mark centered idle partial sums form a martingale under every
initial marked many-server trajectory law. -/
theorem manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_martingale_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Martingale
      (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers)
      piLE trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  apply AppliedModelingLib.martingale_partial_sum_of_condExp_eq_zero
  · exact manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_stronglyAdapted
      trafficIntensity servers
  · intro n
    apply integrable_finset_sum
    intro i _
    simpa [trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_from_initial
        initial trafficIntensity servers hservers i
  · intro n
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers n

/-- The fresh-mark centered idle martingale, stopped before the predictable
arrival-minus-potential-service lower barrier reaches a specified level. -/
noncomputable def manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
    (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ) :
    ℕ → (ℕ → ℕ × Bool) → ℝ :=
  stoppedProcess
    (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
      trafficIntensity servers)
    (manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold)

/-- Lower-barrier stopping preserves adaptation of the fresh-mark idle
martingale. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_stronglyAdapted
    (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ) :
    StronglyAdapted piLE
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold) := by
  simpa [manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum] using
    StronglyAdapted.stoppedProcess_of_discrete
      (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_stronglyAdapted
        trafficIntensity servers)
      (manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime
        lowerThreshold)

/-- Lower-barrier stopping preserves the fresh-mark centered idle martingale
under every initial queue law. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_martingale_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Martingale
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold)
      piLE trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_martingale_from_initial
        initial trafficIntensity servers hservers
  rw [manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum,
    martingale_iff]
  constructor
  · have hneg : Submartingale
        (-stoppedProcess
          (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
            trafficIntensity servers)
          (manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold))
        piLE trajectory := by
      simpa only [Pi.neg_apply] using
        Submartingale.stoppedProcess hmartingale.neg.submartingale
          (manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime lowerThreshold)
    simpa only [neg_neg] using hneg.neg
  · exact Submartingale.stoppedProcess hmartingale.submartingale
      (manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime lowerThreshold)

/-- The individual fresh-mark idle increment retained while the predictable
lower barrier remains unhit. -/
noncomputable def manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
    (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (path : ℕ → ℕ × Bool) : ℝ :=
  if (index : ENat) <
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path then
    manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
      trafficIntensity servers index path
  else 0

/-- The stopped fresh-mark increment is the lower-exit active-set indicator
times the original fresh-mark centered idle increment. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_eq_indicator
    (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ) :
    manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index =
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
        (manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
          trafficIntensity servers index) := by
  funext path
  by_cases hactive : path ∈
      manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · have hcondition : (index : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    unfold manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
    rw [if_pos hcondition, Set.indicator_of_mem hactive]
  · have hcondition : ¬ (index : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    unfold manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
    rw [if_neg hcondition, Set.indicator_of_notMem hactive]

/-- Before the predictable lower exit, a fresh-mark centered idle increment
is bounded by the idle fraction at the lower threshold. -/
theorem abs_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_le_idleFraction_at_lowerThreshold
    (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (hservers : 0 < servers) (path : ℕ → ℕ × Bool)
    (hstep : ∀ step : ℕ,
      ManyServerMarkedStateStepAllowed (path step) (path (step + 1))) :
    |manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index path| ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  have hthreshold_nonneg : 0 ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  rw [manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_eq_indicator]
  by_cases hactive : path ∈
      manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · rw [Set.indicator_of_mem hactive]
    have hbefore : (index : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    have hidle_le : manyServerMarkedStateIdleFractionAt servers index path ≤
        1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
      simpa [manyServerMarkedStateIdleFractionAt] using
        one_sub_manyServerBusyFraction_le_of_lt_lowerExitTime
          servers lowerThreshold index path hstep hbefore
    have hidle_nonneg :=
      (manyServerMarkedStateIdleFractionAt_nonneg_le_one servers index path hservers).1
    have hmark : |(uniformizedBirthProbability trafficIntensity : ℝ) -
        (if (path (index + 1)).2 then 1 else 0)| ≤ 1 := by
      simpa [abs_sub_comm] using
        abs_manyServerMarkedStateCenteredNextArrivalMarkIncrement_le_one
          trafficIntensity index path
    unfold manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
    rw [abs_mul, abs_of_nonneg hidle_nonneg]
    calc
      |(uniformizedBirthProbability trafficIntensity : ℝ) -
          (if (path (index + 1)).2 then 1 else 0)| *
          manyServerMarkedStateIdleFractionAt servers index path ≤
          1 * manyServerMarkedStateIdleFractionAt servers index path :=
        mul_le_mul_of_nonneg_right hmark hidle_nonneg
      _ ≤ 1 * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) :=
        mul_le_mul_of_nonneg_left hidle_le zero_le_one
      _ = 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := one_mul _
  · rw [Set.indicator_of_notMem hactive]
    simpa using hthreshold_nonneg

/-- The lower-barrier-stopped fresh-mark idle martingale is the finite sum of
exactly the increments retained before the predictable exit. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_sum_before_lowerExit
    (trafficIntensity : ℝ≥0) (servers lowerThreshold steps : ℕ)
    (path : ℕ → ℕ × Bool) :
    manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
      trafficIntensity servers lowerThreshold steps path =
      ∑ index ∈ Finset.range steps,
        manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
          trafficIntensity servers lowerThreshold index path := by
  unfold manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
    stoppedProcess manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
  cases hexit : manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path with
  | top =>
      have hmin : ((steps : WithTop ℕ) ⊓ (⊤ : WithTop ℕ)).untopA = steps := by
        rw [inf_eq_left.mpr le_top]
        exact WithTop.untopA_eq_untop
          (WithTop.coe_ne_top : (steps : WithTop ℕ) ≠ (⊤ : WithTop ℕ)) |>.trans
          (WithTop.untop_coe steps _)
      change (∑ index ∈ Finset.range
        ((steps : WithTop ℕ) ⊓ (⊤ : WithTop ℕ)).untopA,
        manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
          trafficIntensity servers index path) = _
      rw [hmin]
      apply Finset.sum_congr rfl
      intro index _
      unfold manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      rw [hexit]
      rw [if_pos (ENat.coe_lt_top index)]
  | coe exit =>
      by_cases hsteps : steps ≤ exit
      · have hmin : (steps : WithTop ℕ) ⊓ (exit : WithTop ℕ) = steps := by
          exact inf_eq_left.mpr (by exact_mod_cast hsteps)
        have hmin_untop : ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA = steps := by
          calc
            ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA =
                (steps : WithTop ℕ).untopA := congrArg WithTop.untopA hmin
            _ = steps := by
              exact WithTop.untopA_eq_untop
                (WithTop.coe_ne_top : (steps : WithTop ℕ) ≠ (⊤ : WithTop ℕ)) |>.trans
                (WithTop.untop_coe steps _)
        change (∑ index ∈ Finset.range
          ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA,
          manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
            trafficIntensity servers index path) = _
        rw [hmin_untop]
        apply Finset.sum_congr rfl
        intro index hindex
        unfold manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
        rw [hexit]
        have hindex_lt : index < exit :=
          lt_of_lt_of_le (Finset.mem_range.mp hindex) hsteps
        have hindex_lt' : (index : ENat) < (exit : ENat) :=
          ENat.coe_lt_coe.mpr hindex_lt
        rw [if_pos hindex_lt']
      · have hexit_lt_steps : exit < steps := Nat.lt_of_not_ge hsteps
        have hmin : (steps : WithTop ℕ) ⊓ (exit : WithTop ℕ) = exit := by
          exact inf_eq_right.mpr (by exact_mod_cast (Nat.le_of_lt hexit_lt_steps))
        have hmin_untop : ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA = exit := by
          calc
            ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA =
                (exit : WithTop ℕ).untopA := congrArg WithTop.untopA hmin
            _ = exit := by
              exact WithTop.untopA_eq_untop
                (WithTop.coe_ne_top : (exit : WithTop ℕ) ≠ (⊤ : WithTop ℕ)) |>.trans
                (WithTop.untop_coe exit _)
        change (∑ index ∈ Finset.range
          ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA,
          manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement
            trafficIntensity servers index path) = _
        rw [hmin_untop]
        have hfilter : (Finset.range steps).filter
            (fun index : ℕ => (index : ENat) < (exit : ENat)) = Finset.range exit := by
          ext index
          simp only [Finset.mem_filter, Finset.mem_range]
          rw [ENat.coe_lt_coe]
          omega
        simp only [manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement, hexit]
        rw [← Finset.sum_filter]
        rw [hfilter]

/-- Before the predictable lower-barrier exit, stopping leaves the fresh-mark
idle martingale unchanged. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_centered_of_le_lowerExit
    (trafficIntensity : ℝ≥0) (servers lowerThreshold steps : ℕ)
    (path : ℕ → ℕ × Bool)
    (hbefore : (steps : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path) :
    manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
      trafficIntensity servers lowerThreshold steps path =
      manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers steps path := by
  unfold manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
  exact stoppedProcess_eq_of_le hbefore

/-- Each retained fresh-mark idle increment is the corresponding one-step
difference of the lower-barrier-stopped martingale. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_eq_partialSum_succ_sub
    (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (path : ℕ → ℕ × Bool) :
    manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index path =
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold (index + 1) path -
        manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold index path := by
  rw [manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_sum_before_lowerExit,
    manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_sum_before_lowerExit,
    Finset.sum_range_succ]
  ring

/-- Lower-barrier stopping never enlarges a fresh-mark centered idle
increment beyond its unit bound. -/
theorem abs_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_le_one
    (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (hservers : 0 < servers) (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index path| ≤ 1 := by
  rw [manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_eq_indicator]
  by_cases hactive : path ∈
      manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · rw [Set.indicator_of_mem hactive]
    exact abs_manyServerMarkedStateCenteredNextPotentialServiceIdleIncrement_le_one
      trafficIntensity servers index path hservers
  · rw [Set.indicator_of_notMem hactive]
    norm_num

/-- The lower-barrier-stopped fresh-mark idle martingale cannot exceed its
number of retained embedded increments in absolute value. -/
theorem abs_manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_le
    (trafficIntensity : ℝ≥0) (servers lowerThreshold n : ℕ)
    (hservers : 0 < servers) (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
      trafficIntensity servers lowerThreshold n path| ≤ n := by
  rw [manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_sum_before_lowerExit]
  calc
    |∑ index ∈ Finset.range n,
        manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
          trafficIntensity servers lowerThreshold index path| ≤
        ∑ index ∈ Finset.range n,
          |manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
            trafficIntensity servers lowerThreshold index path| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro index _
          exact abs_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_le_one
            trafficIntensity servers lowerThreshold index hservers path
    _ = n := by simp

/-- Every lower-barrier-retained fresh-mark idle increment is integrable
under the arbitrary-initial marked trajectory law. -/
theorem integrable_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold index : ℕ) (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Integrable
      (manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
        trafficIntensity servers lowerThreshold index)
      trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have heq : manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index =
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold (index + 1) -
        manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold index := by
    funext path
    exact manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_eq_partialSum_succ_sub
      trafficIntensity servers lowerThreshold index path
  rw [heq]
  exact (hmartingale.integrable (index + 1)).sub (hmartingale.integrable index)

/-- A lower-barrier-retained fresh-mark idle increment has conditional mean
zero with respect to the current marked embedded history. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_condExp_eq_zero_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold index : ℕ) (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
        trafficIntensity servers lowerThreshold index | piLE index] =ᵐ[trajectory] 0 := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have heq : manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index =
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold (index + 1) -
        manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold index := by
    funext path
    exact manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_eq_partialSum_succ_sub
      trafficIntensity servers lowerThreshold index path
  rw [heq]
  calc
    trajectory[
        manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold (index + 1) -
          manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold index | piLE index] =ᵐ[trajectory]
        trajectory[
          manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold (index + 1) | piLE index] -
          trajectory[
            manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
              trafficIntensity servers lowerThreshold index | piLE index] :=
      condExp_sub (hmartingale.integrable (index + 1))
        (hmartingale.integrable index) _
    _ =ᵐ[trajectory]
        manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold index -
          manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold index := by
          exact (hmartingale.condExp_ae_eq (Nat.le_succ index)).sub
            (hmartingale.condExp_ae_eq le_rfl)
    _ =ᵐ[trajectory] 0 := by
      exact Filter.Eventually.of_forall fun _ => sub_self _

/-- The second moment of one lower-barrier-retained fresh-mark idle increment
is bounded by the deterministic idle fraction at the lower threshold. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_secondMoment_le_idleFraction_at_lowerThreshold_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold index : ℕ) (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∀ᵐ path ∂trajectory, ∀ step : ℕ,
      ManyServerMarkedStateStepAllowed (path step) (path (step + 1))) →
    (∫ path,
      (manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
        trafficIntensity servers lowerThreshold index path) ^ 2 ∂trajectory) ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Z : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold index
  let b : ℝ := 1 - (manyServerBusyFraction servers lowerThreshold : ℝ)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  dsimp only
  intro hallSteps
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    dsimp [b]
    have hbusy_nonneg :
        0 ≤ (manyServerBusyFraction servers lowerThreshold : ℝ) := by positivity
    have hbusy_le :
        (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    constructor <;> linarith
  have hZintegrable : Integrable Z trajectory := by
    simpa [Z, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hbound : ∀ᵐ path ∂trajectory, |Z path| ≤ b := by
    filter_upwards [hallSteps] with path hstep
    simpa [Z, b] using
      abs_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_le_idleFraction_at_lowerThreshold
        trafficIntensity servers lowerThreshold index hservers path hstep
  have hZsq : Integrable (fun path => (Z path) ^ 2) trajectory := by
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le hZintegrable.aestronglyMeasurable zero_le_one
    filter_upwards [hbound] with path hpath
    exact hpath.trans hb.2
  have hsq_bound : ∀ᵐ path ∂trajectory, (Z path) ^ 2 ≤ b := by
    filter_upwards [hbound] with path hpath
    have habs_nonneg : 0 ≤ |Z path| := abs_nonneg _
    have hsquare : |Z path| ^ 2 ≤ b ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self habs_nonneg hpath
    have hb_square : b ^ 2 ≤ b := by
      calc
        b ^ 2 = b * b := pow_two _
        _ ≤ 1 * b := mul_le_mul_of_nonneg_right hb.2 hb.1
        _ = b := one_mul _
    calc
      (Z path) ^ 2 = |Z path| ^ 2 := by rw [sq_abs]
      _ ≤ b ^ 2 := hsquare
      _ ≤ b := hb_square
  calc
    (∫ path, (Z path) ^ 2 ∂trajectory) ≤ ∫ _path : ℕ → ℕ × Bool, b ∂trajectory := by
      exact integral_mono_ae hZsq (integrable_const _) hsq_bound
    _ = b := by simp

/-- Before the predictable lower exit, the fresh-mark idle martingale has
second moment at most its horizon times the idle fraction at the barrier. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_secondMoment_le_lowerThreshold_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∀ᵐ path ∂trajectory, ∀ step : ℕ,
      ManyServerMarkedStateStepAllowed (path step) (path (step + 1))) →
    (∫ path,
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold n path) ^ 2 ∂trajectory) ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Y : ℕ → (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
      trafficIntensity servers lowerThreshold
  let b : ℝ := 1 - (manyServerBusyFraction servers lowerThreshold : ℝ)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  dsimp only
  intro hallSteps
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    dsimp [b]
    have hbusy_nonneg :
        0 ≤ (manyServerBusyFraction servers lowerThreshold : ℝ) := by positivity
    have hbusy_le :
        (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    constructor <;> linarith
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have hsum_eq :
      (fun steps path => ∑ index ∈ Finset.range steps, Y index path) =
        manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold := by
    funext steps path
    symm
    exact manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_sum_before_lowerExit
      trafficIntensity servers lowerThreshold steps path
  have hadapted : StronglyAdapted piLE
      (fun steps path => ∑ index ∈ Finset.range steps, Y index path) := by
    rw [hsum_eq]
    exact hmartingale.stronglyAdapted
  have hY_integrable : ∀ index, Integrable (Y index) trajectory := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hY_bound : ∀ index, ∀ᵐ path ∂trajectory, |Y index path| ≤ 1 := by
    intro index
    filter_upwards [hallSteps] with path hstep
    exact (abs_manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_le_idleFraction_at_lowerThreshold
      trafficIntensity servers lowerThreshold index hservers path hstep).trans hb.2
  have hsum_bound : ∀ steps, ∀ᵐ path ∂trajectory,
      |∑ index ∈ Finset.range steps, Y index path| ≤ steps := by
    intro steps
    filter_upwards [(Finset.eventually_all (Finset.range steps)).2
      (fun index hindex => hY_bound index)] with path hbound
    calc
      |∑ index ∈ Finset.range steps, Y index path| ≤
          ∑ index ∈ Finset.range steps, |Y index path| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index ∈ Finset.range steps, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro index hindex
          exact hbound index hindex
      _ = steps := by simp
  have hsum_sq_int : ∀ steps,
      Integrable (fun path =>
        (∑ index ∈ Finset.range steps, Y index path) ^ 2) trajectory := by
    intro steps
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (((hadapted steps).mono (piLE.le steps)).aestronglyMeasurable)
      (Nat.cast_nonneg steps)
    exact hsum_bound steps
  have hcross_int : ∀ index,
      Integrable (fun path =>
        (∑ previous ∈ Finset.range index, Y previous path) * Y index path)
        trajectory := by
    intro index
    apply Integrable.of_bound
      ((((hadapted index).mono (piLE.le index)).aestronglyMeasurable).mul
        (hY_integrable index).aestronglyMeasurable) index
    filter_upwards [hsum_bound index, hY_bound index] with path hsum hY
    change |(∑ previous ∈ Finset.range index, Y previous path) * Y index path| ≤ index
    rw [abs_mul]
    calc
      |∑ previous ∈ Finset.range index, Y previous path| * |Y index path| ≤
          (index : ℝ) * |Y index path| :=
        mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
      _ ≤ (index : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg index)
      _ = index := by ring
  have hY_sq_int : ∀ index,
      Integrable (fun path => (Y index path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (hY_integrable index).aestronglyMeasurable zero_le_one
    exact hY_bound index
  have hY_second : ∀ index,
      (∫ path, (Y index path) ^ 2 ∂trajectory) ≤ b := by
    intro index
    simpa [Y, b, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_secondMoment_le_idleFraction_at_lowerThreshold_from_initial
        initial trafficIntensity servers lowerThreshold index hservers hallSteps
  have hcond : ∀ index, trajectory[Y index | piLE index] =ᵐ[trajectory] 0 := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hcross_nonpos : ∀ index,
      (∫ path,
        (∑ previous ∈ Finset.range index, Y previous path) * Y index path ∂trajectory) ≤ 0 :=
    AppliedModelingLib.partial_sum_cross_integral_nonpos_of_condExp_eq_zero
      hadapted hcross_int hY_integrable hcond
  have hsecond := AppliedModelingLib.partial_sum_secondMoment_le_sum_of_cross_nonpos
    (Y := Y) (b := fun _ => b)
    hsum_sq_int hcross_int hY_sq_int hY_second hcross_nonpos n
  rw [← hsum_eq]
  simpa using hsecond

/-- The fresh centered arrival-mark partial sum is bounded pathwise by its
number of embedded increments. -/
theorem abs_manyServerMarkedStateCenteredNextArrivalMarkPartialSum_le
    (trafficIntensity : ℝ≥0) (n : ℕ) (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateCenteredNextArrivalMarkPartialSum
      trafficIntensity n path| ≤ n := by
  unfold manyServerMarkedStateCenteredNextArrivalMarkPartialSum
  calc
    |∑ i ∈ Finset.range n,
        manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity i path| ≤
        ∑ i ∈ Finset.range n,
          |manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity i path| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact abs_manyServerMarkedStateCenteredNextArrivalMarkIncrement_le_one
            trafficIntensity i path
    _ = n := by simp

/-- Every fresh centered arrival-mark partial sum is square-integrable under
an arbitrary initial marked trajectory law. -/
theorem memLp_two_manyServerMarkedStateCenteredNextArrivalMarkPartialSum_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    MemLp (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
      trafficIntensity n) 2 trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmeas : AEStronglyMeasurable
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum trafficIntensity n)
      trajectory :=
    ((manyServerMarkedStateCenteredNextArrivalMarkPartialSum_stronglyAdapted
      trafficIntensity n).mono (piLE.le n)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  apply AppliedModelingLib.integrable_sq_of_ae_abs_le hmeas (Nat.cast_nonneg n)
  exact Filter.Eventually.of_forall fun path =>
    abs_manyServerMarkedStateCenteredNextArrivalMarkPartialSum_le
      trafficIntensity n path

/-- The fresh arrival-mark martingale has a finite-horizon second moment at
most its number of embedded increments. -/
theorem manyServerMarkedStateCenteredNextArrivalMarkPartialSum_secondMoment_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
        trafficIntensity n path) ^ 2 ∂trajectory) ≤ n := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Y : ℕ → (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateCenteredNextArrivalMarkIncrement trafficIntensity
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hadapted : StronglyAdapted piLE
      (fun index path => ∑ i ∈ Finset.range index, Y i path) := by
    simpa [Y] using
      manyServerMarkedStateCenteredNextArrivalMarkPartialSum_stronglyAdapted
        trafficIntensity
  have hY_integrable : ∀ index, Integrable (Y index) trajectory := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredNextArrivalMarkIncrement_from_initial
        initial trafficIntensity servers hservers index
  have hY_bound : ∀ index, ∀ᵐ path ∂trajectory, |Y index path| ≤ 1 := by
    intro index
    exact Filter.Eventually.of_forall fun path =>
      abs_manyServerMarkedStateCenteredNextArrivalMarkIncrement_le_one
        trafficIntensity index path
  have hsum_bound : ∀ index, ∀ᵐ path ∂trajectory,
      |∑ i ∈ Finset.range index, Y i path| ≤ index := by
    intro index
    exact Filter.Eventually.of_forall fun path => by
      simpa [Y, manyServerMarkedStateCenteredNextArrivalMarkPartialSum] using
        abs_manyServerMarkedStateCenteredNextArrivalMarkPartialSum_le
          trafficIntensity index path
  have hsum_sq_int : ∀ index,
      Integrable (fun path => (∑ i ∈ Finset.range index, Y i path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (((hadapted index).mono (piLE.le index)).aestronglyMeasurable)
      (Nat.cast_nonneg index)
    exact hsum_bound index
  have hcross_int : ∀ index,
      Integrable (fun path =>
        (∑ i ∈ Finset.range index, Y i path) * Y index path) trajectory := by
    intro index
    apply Integrable.of_bound
      ((((hadapted index).mono (piLE.le index)).aestronglyMeasurable).mul
        (hY_integrable index).aestronglyMeasurable) index
    filter_upwards [hsum_bound index, hY_bound index] with path hsum hY
    change |(∑ i ∈ Finset.range index, Y i path) * Y index path| ≤ index
    rw [abs_mul]
    calc
      |∑ i ∈ Finset.range index, Y i path| * |Y index path| ≤
          (index : ℝ) * |Y index path| :=
        mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
      _ ≤ (index : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg index)
      _ = index := by ring
  have hY_sq_int : ∀ index,
      Integrable (fun path => (Y index path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (hY_integrable index).aestronglyMeasurable zero_le_one
    exact hY_bound index
  have hY_second : ∀ index,
      (∫ path, (Y index path) ^ 2 ∂trajectory) ≤ 1 := by
    intro index
    simpa using AppliedModelingLib.integral_sq_le_sq_of_ae_abs_le
      (hY_sq_int index) zero_le_one (hY_bound index)
  have hcond : ∀ index, trajectory[Y index | piLE index] =ᵐ[trajectory] 0 := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextArrivalMarkIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers index
  have hcross_nonpos : ∀ index,
      (∫ path,
        (∑ i ∈ Finset.range index, Y i path) * Y index path ∂trajectory) ≤ 0 :=
    AppliedModelingLib.partial_sum_cross_integral_nonpos_of_condExp_eq_zero
      hadapted hcross_int hY_integrable hcond
  have hsecond := AppliedModelingLib.partial_sum_secondMoment_le_sum_of_cross_nonpos
    (Y := Y) (b := fun _ => (1 : ℝ)) hsum_sq_int hcross_int hY_sq_int hY_second
      hcross_nonpos n
  simpa [Y, manyServerMarkedStateCenteredNextArrivalMarkPartialSum] using
    hsecond

/-- A finite-horizon Doob estimate for the fresh arrival-mark martingale. -/
theorem ennreal_mul_measure_maximalCenteredNextArrivalMarkPartialSum_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (threshold : ℝ≥0) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
            trafficIntensity index path) ^ 2)} ≤ ENNReal.ofReal n := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum trafficIntensity)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextArrivalMarkPartialSum_martingale_from_initial
        initial trafficIntensity servers hservers
  have hL2 : ∀ index : ℕ, MemLp
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum trafficIntensity index)
      2 trajectory := by
    intro index
    simpa [trajectory, markedInitial, measureKernel] using
      memLp_two_manyServerMarkedStateCenteredNextArrivalMarkPartialSum_from_initial
        initial trafficIntensity servers hservers index
  have hmax := AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
    hmartingale hL2 threshold n
  have hsecond : (∫ path,
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
        trafficIntensity n path) ^ 2 ∂trajectory) ≤ n := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredNextArrivalMarkPartialSum_secondMoment_le_from_initial
        initial trafficIntensity servers hservers n
  calc
    threshold * trajectory {path | (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
              trafficIntensity index path) ^ 2)} ≤
        ENNReal.ofReal (∫ path,
          (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
            trafficIntensity n path) ^ 2 ∂trajectory) := hmax
    _ ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal hsecond

/-- A terminal separation bound supplies the lower-barrier margin required by
the arrival-mark localization argument.  In the stable regime, the adverse
uniformized drift is monotone in the number of embedded steps. -/
theorem uniformizedArrivalLowerBarrier_margin_condition_of_terminal
    (trafficIntensity : ℝ≥0) (initialLower lowerThreshold cutoff : ℕ) (margin : ℝ)
    (htraffic_le_one : trafficIntensity ≤ 1)
    (hterminal : 2 * margin + 2 +
      (1 - 2 * (uniformizedBirthProbability trafficIntensity : ℝ)) * (cutoff : ℝ) ≤
        (initialLower : ℝ) - (lowerThreshold : ℝ)) :
    ∀ steps ≤ cutoff,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin := by
  obtain ⟨hdrift_nonneg, _⟩ :=
    one_sub_two_mul_uniformizedBirthProbability_nonneg_le_gap
      trafficIntensity htraffic_le_one
  intro steps hsteps
  have hsteps_real : (steps : ℝ) ≤ (cutoff : ℝ) := by exact_mod_cast hsteps
  have hdrift :
      (1 - 2 * (uniformizedBirthProbability trafficIntensity : ℝ)) * (steps : ℝ) ≤
        (1 - 2 * (uniformizedBirthProbability trafficIntensity : ℝ)) * (cutoff : ℝ) :=
    mul_le_mul_of_nonneg_left hsteps_real hdrift_nonneg
  calc
    (lowerThreshold : ℝ) - (initialLower : ℝ) -
        (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
          (steps : ℝ) + 2 =
        -((initialLower : ℝ) - (lowerThreshold : ℝ)) +
          (1 - 2 * (uniformizedBirthProbability trafficIntensity : ℝ)) * (steps : ℝ) + 2 := by
            ring
    _ ≤ -((initialLower : ℝ) - (lowerThreshold : ℝ)) +
          (1 - 2 * (uniformizedBirthProbability trafficIntensity : ℝ)) * (cutoff : ℝ) + 2 := by
            gcongr
    _ ≤ -2 * margin := by linarith

/-- If the arrival-versus-potential-service lower barrier exits through a
finite horizon while the initial queue is above a prescribed level, then the
fresh arrival-mark martingale has a correspondingly large negative excursion.
This is a deterministic localization implication. -/
theorem manyServerMarkedStateArrivalPotentialLowerExit_implies_maximalCenteredNextArrivalMark
    (trafficIntensity : ℝ≥0) (initialLower lowerThreshold n : ℕ)
    (margin : ℝ) (path : ℕ → ℕ × Bool)
    (hmargin_nonneg : 0 ≤ margin)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hinitial : initialLower ≤ (path 0).1)
    (hexit : manyServerMarkedStateArrivalPotentialLowerExitTime
      lowerThreshold path ≤ (n : ℕ∞)) :
    margin ^ 2 ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
            trafficIntensity index path) ^ 2) := by
  rcases (manyServerMarkedStateArrivalPotentialLowerExitTime_le_iff
    lowerThreshold n path).mp hexit with ⟨steps, hsteps, hbarrier⟩
  have hlower := manyServerMarkedStateCenteredNextArrivalMark_lowerBound
    trafficIntensity steps path
  have hendpoint : -2 ≤
      2 * (if (path 0).2 then (1 : ℝ) else 0) -
        2 * (if (path steps).2 then (1 : ℝ) else 0) := by
    cases (path 0).2 <;> cases (path steps).2 <;> norm_num
  have hsum : manyServerMarkedStateCenteredNextArrivalMarkPartialSum
      trafficIntensity steps path ≤ -margin := by
    have hmargin' := hmargin steps hsteps
    have hinitial' : (initialLower : ℝ) ≤ ((path 0).1 : ℝ) := by
      exact_mod_cast hinitial
    have hbarrier' : (manyServerMarkedStateArrivalPotentialLowerBound
        path steps : ℝ) ≤ lowerThreshold := by
      exact_mod_cast hbarrier
    nlinarith
  have hsquare : margin ^ 2 ≤
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
        trafficIntensity steps path) ^ 2 := by
    nlinarith [sq_nonneg
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
        trafficIntensity steps path + margin)]
  exact hsquare.trans (Finset.le_sup'
    (s := Finset.range (n + 1))
    (f := fun index =>
      (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
        trafficIntensity index path) ^ 2)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hsteps)))

/-- The fresh-mark Doob estimate controls a finite lower-barrier exit on the
event that the initial queue is above the localization level. -/
theorem ennreal_mul_measure_manyServerMarkedStateArrivalPotentialLowerExit_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers initialLower lowerThreshold n : ℕ)
    (hservers : 0 < servers) (margin : ℝ) (threshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin) (hthreshold : (threshold : ℝ) ≤ margin ^ 2)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path |
      initialLower ≤ (path 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime
        lowerThreshold path ≤ (n : ℕ∞)} ≤ ENNReal.ofReal n := by
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
  have hsubset : {path : ℕ → ℕ × Bool |
      initialLower ≤ (path 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime
        lowerThreshold path ≤ (n : ℕ∞)} ⊆
      {path | (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
              trafficIntensity index path) ^ 2)} := by
    intro path hpath
    exact hthreshold.trans
      (manyServerMarkedStateArrivalPotentialLowerExit_implies_maximalCenteredNextArrivalMark
        trafficIntensity initialLower lowerThreshold n margin path hmargin_nonneg hmargin
        hpath.1 hpath.2)
  calc
    threshold * trajectory {path |
        initialLower ≤ (path 0).1 ∧
        manyServerMarkedStateArrivalPotentialLowerExitTime
          lowerThreshold path ≤ (n : ℕ∞)} ≤
        threshold * trajectory {path | (threshold : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun index =>
              (manyServerMarkedStateCenteredNextArrivalMarkPartialSum
                trafficIntensity index path) ^ 2)} :=
      mul_le_mul_right (measure_mono hsubset) threshold
    _ ≤ ENNReal.ofReal n := by
      simpa [trajectory] using
        ennreal_mul_measure_maximalCenteredNextArrivalMarkPartialSum_le_from_initial
          initial trafficIntensity servers hservers threshold n

/-- The invariant augmented PMF lifts to the measure-valued kernel used by
the stationary trajectory construction. -/
theorem manyServerMarkedStatePMF_kernelInvariant
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial) :
    Kernel.Invariant
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
  simpa only [manyServerMarkedStateUniformizationMeasureKernel] using
    (manyServerMarkedStatePMF_stationary trafficIntensity servers hservers hstationary).kernelInvariant

/-- At each deterministic embedded index, the stationary marked trajectory
obeys the queue update dictated by its retained potential-event mark. -/
theorem ae_stationaryManyServerMarkedStateTrajectory_stepAllowed
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial)
    (index : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers),
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let markedKernel : CountableMarkovKernel (ℕ × Bool) :=
    manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hkernel : ∀ current : ℕ × Bool,
      ∀ᵐ next ∂measureKernel current,
        ManyServerMarkedStateStepAllowed current next := by
    intro current
    refine MeasureTheory.ae_iff.2 ?_
    rw [show measureKernel current = (markedKernel current).toMeasure by rfl,
      (markedKernel current).toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete,
      Set.disjoint_left]
    intro next hnext hbad
    exact hbad (manyServerMarkedStateUniformizationKernel_support_stepAllowed
      trafficIntensity servers hservers current next hnext)
  have hpair : ∀ᵐ statePair ∂markedInitial.toMeasure ⊗ₘ measureKernel,
      ManyServerMarkedStateStepAllowed statePair.1 statePair.2 := by
    refine Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete ?_
    exact Filter.Eventually.of_forall hkernel
  have hpairMap :
      Measure.map (fun path : ℕ → ℕ × Bool => (path index, path (index + 1)))
        trajectory = markedInitial.toMeasure ⊗ₘ measureKernel := by
    exact stationaryTrajMeasure_consecutivePair
      (manyServerMarkedStatePMF_kernelInvariant
        trafficIntensity servers hservers hstationary) index
  refine ae_of_ae_map
    (μ := trajectory)
    (f := fun path : ℕ → ℕ × Bool => (path index, path (index + 1)))
    (p := fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      ManyServerMarkedStateStepAllowed statePair.1 statePair.2)
    ((measurable_pi_apply index).prodMk
      (measurable_pi_apply (index + 1))).aemeasurable ?_
  rw [hpairMap]
  exact hpair

/-- The retained-mark recursion holds simultaneously at every embedded
potential-event index, outside one null set of marked trajectories. -/
theorem ae_all_stationaryManyServerMarkedStateTrajectory_stepAllowed
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers),
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (path index) (path (index + 1)) := by
  exact ae_all_iff.2 fun index =>
    ae_stationaryManyServerMarkedStateTrajectory_stepAllowed
      trafficIntensity servers hservers hstationary index

/-- For an arbitrary initial marked-state PMF, every deterministic embedded
transition follows the retained-mark queue update outside a null set.  This
uses the one-step Ionescu--Tulcea recurrence rather than stationarity. -/
theorem ae_manyServerMarkedStateTrajectory_stepAllowed_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers),
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let markedKernel : CountableMarkovKernel (ℕ × Bool) :=
    manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hkernel : ∀ current : ℕ × Bool,
      ∀ᵐ next ∂measureKernel current,
        ManyServerMarkedStateStepAllowed current next := by
    intro current
    refine MeasureTheory.ae_iff.2 ?_
    rw [show measureKernel current = (markedKernel current).toMeasure by rfl,
      (markedKernel current).toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete,
      Set.disjoint_left]
    intro next hnext hbad
    exact hbad (manyServerMarkedStateUniformizationKernel_support_stepAllowed
      trafficIntensity servers hservers current next hnext)
  have hpair : ∀ᵐ statePair ∂((trajectory.map (fun path => path index)) ⊗ₘ measureKernel),
      ManyServerMarkedStateStepAllowed statePair.1 statePair.2 := by
    refine Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete ?_
    exact Filter.Eventually.of_forall hkernel
  have hpairMap :
      Measure.map (fun path : ℕ → ℕ × Bool => (path index, path (index + 1)))
        trajectory = (trajectory.map (fun path => path index)) ⊗ₘ measureKernel := by
    exact stationaryTrajMeasure_consecutivePair_recurrence
      (π := markedInitial.toMeasure) (K := measureKernel) index
  refine ae_of_ae_map
    (μ := trajectory)
    (f := fun path : ℕ → ℕ × Bool => (path index, path (index + 1)))
    (p := fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      ManyServerMarkedStateStepAllowed statePair.1 statePair.2)
    ((measurable_pi_apply index).prodMk
      (measurable_pi_apply (index + 1))).aemeasurable ?_
  rw [hpairMap]
  exact hpair

/-- The retained-mark recursion holds at every embedded index for an arbitrary
initial marked-state PMF, on one common full-measure event. -/
theorem ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers),
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (path index) (path (index + 1)) := by
  exact ae_all_iff.2 fun index =>
    ae_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers index

/-- At zero traffic intensity, the marked finite-prefix unused-service reward
is almost surely the service-only endpoint reward. -/
theorem ae_manyServerMarkedStateTrajectory_unrealizedPotentialServicePrefix_eq_steps_sub_queueLoss_of_zero
    (initial : PMF ℕ) (servers : ℕ) (hservers : 0 < servers) (steps : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial 0).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel 0 servers hservers),
      manyServerMarkedStateUnrealizedPotentialServicePrefix path steps =
        steps - ((path 0).1 - (path steps).1) := by
  filter_upwards [ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
    initial 0 servers hservers,
    ae_manyServerMarkedStateTrajectory_serviceMarks_false_of_zero
      initial servers hservers steps] with path hstep hmarks
  exact manyServerMarkedStateUnrealizedPotentialServicePrefix_eq_steps_sub_queueLoss_of_serviceMarks
    path hstep steps hmarks

/-- The expected unused-service reward of a finite zero-traffic marked prefix
equals the endpoint-accounting reward under the arrival-free kernel. -/
theorem integral_manyServerMarkedStateTrajectory_unrealizedPotentialServicePrefix_eq_serviceOnly
    (servers state steps : ℕ) (hservers : 0 < servers) :
    (∫ path : ℕ → ℕ × Bool,
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) ∂
        stationaryTrajMeasure
          (manyServerMarkedStatePMF (PMF.pure state) 0).toMeasure
          (manyServerMarkedStateUniformizationMeasureKernel 0 servers hservers)) =
      ∫ next,
        (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ∂
          (CountableMarkovKernel.iterate
            (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure := by
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF (PMF.pure state) 0).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel 0 servers hservers)
  let reward : ℕ → ℝ := fun next =>
    (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ)
  have hinitialLaw : HasLaw (fun path : ℕ → ℕ × Bool => (path 0).1)
      (PMF.pure state).toMeasure trajectory := by
    simpa [trajectory, CountableMarkovKernel.iterate] using
      (manyServerMarkedStateTrajectory_queueStateAt_hasLaw
        (PMF.pure state) 0 servers hservers 0)
  have hinitial : ∀ᵐ path ∂trajectory, (path 0).1 = state := by
    refine (hinitialLaw.ae_iff (p := fun initialState : ℕ => initialState = state)
      (measurable_of_countable _)).2 ?_
    simp only [PMF.toMeasure_pure, ae_dirac_eq, Filter.eventually_pure]
  have hprefix :=
    ae_manyServerMarkedStateTrajectory_unrealizedPotentialServicePrefix_eq_steps_sub_queueLoss_of_zero
      (PMF.pure state) servers hservers steps
  have hidentity : ∀ᵐ path ∂trajectory,
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) =
        reward ((path steps).1) := by
    filter_upwards [hprefix, hinitial] with path hpath hinitialPath
    rw [hpath]
    simp [reward, manyServerServiceOnlyUnrealizedPotentialService,
      manyServerServiceOnlyCompletedServiceCount, hinitialPath]
  have hterminal : HasLaw (fun path : ℕ → ℕ × Bool => (path steps).1)
      (CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure
      trajectory := by
    simpa [trajectory, manyServerServiceOnlyKernel] using
      (manyServerMarkedStateTrajectory_queueStateAt_hasLaw
        (PMF.pure state) 0 servers hservers steps)
  calc
    (∫ path : ℕ → ℕ × Bool,
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) ∂trajectory) =
        ∫ path : ℕ → ℕ × Bool, reward ((path steps).1) ∂trajectory :=
      integral_congr_ae hidentity
    _ = ∫ next, reward next ∂Measure.map (fun path : ℕ → ℕ × Bool => (path steps).1)
        trajectory := by
          symm
          simpa [Function.comp_def] using
            (integral_map
              ((measurable_fst.comp (measurable_pi_apply steps)).aemeasurable)
              (measurable_of_countable reward).aestronglyMeasurable)
    _ = ∫ next, reward next ∂
        (CountableMarkovKernel.iterate
          (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure := by
      rw [hterminal.map_eq]

/-- Under the marked many-server trajectory law, one lower-barrier-retained
fresh-mark idle increment has second moment at most the barrier idle fraction. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_secondMoment_le_idleFraction_at_lowerThreshold_from_initial_auto
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold index : ℕ) (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement
        trafficIntensity servers lowerThreshold index path) ^ 2 ∂trajectory) ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  dsimp only
  exact
    manyServerMarkedStateStoppedNextPotentialServiceIdleIncrement_secondMoment_le_idleFraction_at_lowerThreshold_from_initial
      initial trafficIntensity servers lowerThreshold index hservers
      (ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
        initial trafficIntensity servers hservers)

/-- Under the marked many-server trajectory law, the lower-barrier-stopped
fresh-mark idle martingale has second moment at most its horizon times the
barrier idle fraction. -/
theorem manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_secondMoment_le_lowerThreshold_idleFraction_from_initial_auto
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold n path) ^ 2 ∂trajectory) ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
  dsimp only
  exact
    manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_secondMoment_le_lowerThreshold_idleFraction_from_initial
      initial trafficIntensity servers lowerThreshold hservers n
      (ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
        initial trafficIntensity servers hservers)

/-- Every lower-barrier-stopped fresh-mark idle martingale value is square
integrable under an arbitrary initial marked trajectory law. -/
theorem memLp_two_manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    MemLp (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
      trafficIntensity servers lowerThreshold n) 2 trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have hmeas : AEStronglyMeasurable
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold n)
      trajectory :=
    ((hmartingale.stronglyMeasurable n).mono (piLE.le n)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  apply AppliedModelingLib.integrable_sq_of_ae_abs_le hmeas (Nat.cast_nonneg n)
  exact Filter.Eventually.of_forall fun path =>
    abs_manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_le
      trafficIntensity servers lowerThreshold n hservers path

/-- Doob's finite-prefix estimate for the fresh-mark idle martingale stopped
at the predictable lower barrier. -/
theorem ennreal_mul_measure_maximalStoppedNextPotentialServiceIdlePartialSum_le_lowerThreshold_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) (threshold : ℝ≥0) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold index path) ^ 2)} ≤
      ENNReal.ofReal ((n : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have hL2 : ∀ index : ℕ, MemLp
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold index)
      2 trajectory := by
    intro index
    simpa [trajectory, markedInitial, measureKernel] using
      memLp_two_manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_from_initial
        initial trafficIntensity servers lowerThreshold hservers index
  have hmax := AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
    hmartingale hL2 threshold n
  have hsecond : (∫ path,
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold n path) ^ 2 ∂trajectory) ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_secondMoment_le_lowerThreshold_idleFraction_from_initial_auto
        initial trafficIntensity servers lowerThreshold hservers n
  calc
    threshold * trajectory {path | (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
              trafficIntensity servers lowerThreshold index path) ^ 2)} ≤
        ENNReal.ofReal (∫ path,
          (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold n path) ^ 2 ∂trajectory) := hmax
    _ ≤ ENNReal.ofReal ((n : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) :=
      ENNReal.ofReal_le_ofReal hsecond

/-- At every deterministic embedded index, the expected unrealized
potential-service increment equals the expected current idle fraction, for an
arbitrary initial queue-state PMF.  This is the integrated one-step
compensator identity for the marked Ionescu--Tulcea trajectory. -/
theorem manyServerMarkedStateTrajectory_unrealizedPotentialServiceIncrement_integral_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    (∫ path,
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement
        (path index) (path (index + 1)) : ℝ) ∂
      stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) =
      ∫ current,
        if current.2 then 0 else
          1 - (manyServerBusyFraction servers current.1 : ℝ) ∂
        (stationaryTrajMeasure
          (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
          (manyServerMarkedStateUniformizationMeasureKernel
            trafficIntensity servers hservers)).map (fun path => path index) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let marginal : Measure (ℕ × Bool) := trajectory.map (fun path => path index)
  let pair : (ℕ → ℕ × Bool) → (ℕ × Bool) × (ℕ × Bool) :=
    fun path => (path index, path (index + 1))
  let increment : (ℕ × Bool) × (ℕ × Bool) → ℝ :=
    fun statePair =>
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement
        statePair.1 statePair.2 : ℝ)
  let idle : (ℕ × Bool) → ℝ :=
    fun current => if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  letI : IsFiniteMeasure marginal := by
    dsimp [marginal]
    infer_instance
  letI : IsFiniteMeasure (marginal ⊗ₘ measureKernel) := by infer_instance
  have hpair : Measurable pair :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  have hincrement : Measurable increment := measurable_of_countable _
  have hincrement_int : Integrable increment (marginal ⊗ₘ measureKernel) := by
    apply Integrable.of_bound hincrement.aestronglyMeasurable 1
    filter_upwards [] with statePair
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast
      manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
        statePair.1 statePair.2
  have hpairLaw : Measure.map pair trajectory = marginal ⊗ₘ measureKernel := by
    exact stationaryTrajMeasure_consecutivePair_recurrence
      (π := markedInitial.toMeasure) (K := measureKernel) index
  change (∫ path, increment (pair path) ∂trajectory) = ∫ current, idle current ∂marginal
  calc
    (∫ path, increment (pair path) ∂trajectory) =
        ∫ statePair, increment statePair ∂Measure.map pair trajectory := by
          symm
          exact integral_map hpair.aemeasurable hincrement.aestronglyMeasurable
    _ = ∫ statePair, increment statePair ∂(marginal ⊗ₘ measureKernel) := by
          rw [hpairLaw]
    _ = ∫ current, ∫ next, increment (current, next) ∂measureKernel current ∂marginal := by
          rw [Measure.integral_compProd hincrement_int]
    _ = ∫ current, idle current ∂marginal := by
          apply integral_congr_ae
          filter_upwards [] with current
          dsimp [increment, idle, measureKernel]
          exact manyServerMarkedStateUniformizationKernel_unrealizedPotentialServiceIncrement_integral
            trafficIntensity servers hservers current

/-- The embedded one-step compensator identity remains valid after weighting
by any measurable event of the complete retained-mark history through the
current index.  Thus the next unrealized potential-service increment has the
idle fraction as its conditional mean relative to every finite-history event;
this is the finite-history Markov input needed to construct its compensated
partial-sum martingale. -/
theorem manyServerMarkedStateTrajectory_unrealizedPotentialServiceIncrement_history_indicator_integral_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ)
    (historyEvent : Set ((i : Finset.Iic index) → ℕ × Bool))
    (hhistoryEvent : MeasurableSet historyEvent) :
    (∫ path,
      manyServerMarkedStateHistoryEventIndicator historyEvent
        (Preorder.frestrictLe index path) *
        (manyServerMarkedStateUnrealizedPotentialServiceIncrement
          (path index) (path (index + 1)) : ℝ) ∂
      stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) =
      ∫ path,
        manyServerMarkedStateHistoryEventIndicator historyEvent
          (Preorder.frestrictLe index path) *
          (if (path index).2 then 0 else
            1 - (manyServerBusyFraction servers (path index).1 : ℝ)) ∂
        stationaryTrajMeasure
          (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
          (manyServerMarkedStateUniformizationMeasureKernel
            trafficIntensity servers hservers) := by
  classical
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let history : (ℕ → ℕ × Bool) → ((i : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let last : ((i : Finset.Iic index) → ℕ × Bool) → ℕ × Bool :=
    fun past => past ⟨index, Finset.mem_Iic.mpr le_rfl⟩
  let historyKernel : Kernel ((i : Finset.Iic index) → ℕ × Bool) (ℕ × Bool) :=
    measureKernel ∘ₖ Kernel.deterministic last (measurable_pi_apply _)
  let historyMeasure : Measure ((i : Finset.Iic index) → ℕ × Bool) :=
    trajectory.map history
  let historyNext : (ℕ → ℕ × Bool) →
      ((i : Finset.Iic index) → ℕ × Bool) × (ℕ × Bool) :=
    fun path => (history path, path (index + 1))
  let weight : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    manyServerMarkedStateHistoryEventIndicator historyEvent
  let increment : (ℕ × Bool) × (ℕ × Bool) → ℝ :=
    fun statePair =>
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement
        statePair.1 statePair.2 : ℝ)
  let idle : (ℕ × Bool) → ℝ :=
    fun current => if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ)
  let integrand : ((i : Finset.Iic index) → ℕ × Bool) × (ℕ × Bool) → ℝ :=
    fun historyPair => weight historyPair.1 * increment (last historyPair.1, historyPair.2)
  let right : (ℕ → ℕ × Bool) → ℝ :=
    fun path => weight (history path) * idle (path index)
  let pastRight : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    fun past => weight past * idle (last past)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  letI : IsFiniteMeasure historyMeasure := by
    dsimp [historyMeasure]
    infer_instance
  letI : IsFiniteMeasure (historyMeasure ⊗ₘ historyKernel) := by infer_instance
  have hhistory : Measurable history := Preorder.measurable_frestrictLe index
  have hhistoryNext : Measurable historyNext :=
    hhistory.prodMk (measurable_pi_apply (index + 1))
  have hintegrand : Measurable integrand := measurable_of_countable _
  have hweight : Measurable weight := by
    dsimp [weight]
    unfold manyServerMarkedStateHistoryEventIndicator
    exact Measurable.ite hhistoryEvent measurable_const measurable_const
  have hintegrand_int : Integrable integrand (historyMeasure ⊗ₘ historyKernel) := by
    apply Integrable.of_bound hintegrand.aestronglyMeasurable 1
    filter_upwards [] with historyPair
    by_cases hmem : historyPair.1 ∈ historyEvent
    · simp [integrand, weight, manyServerMarkedStateHistoryEventIndicator, hmem]
      dsimp [increment]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast
        manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
          (last historyPair.1) historyPair.2
    · simp [integrand, weight, manyServerMarkedStateHistoryEventIndicator, hmem]
  have hhistoryLaw : Measure.map historyNext trajectory = historyMeasure ⊗ₘ historyKernel := by
    exact stationaryTrajMeasure_prefix_succ
      (π := markedInitial.toMeasure) (K := measureKernel) index
  have hpastRight : Measurable pastRight := by
    exact hweight.mul
      ((measurable_of_countable idle).comp (measurable_pi_apply _))
  have hright_eq : right = pastRight ∘ history := by
    funext path
    rfl
  change (∫ path, integrand (historyNext path) ∂trajectory) = ∫ path, right path ∂trajectory
  calc
    (∫ path, integrand (historyNext path) ∂trajectory) =
        ∫ historyPair, integrand historyPair ∂Measure.map historyNext trajectory := by
          symm
          exact integral_map hhistoryNext.aemeasurable hintegrand.aestronglyMeasurable
    _ = ∫ historyPair, integrand historyPair ∂(historyMeasure ⊗ₘ historyKernel) := by
          rw [hhistoryLaw]
    _ = ∫ past, ∫ next, integrand (past, next) ∂historyKernel past ∂historyMeasure := by
          rw [Measure.integral_compProd hintegrand_int]
    _ = ∫ past, weight past * idle (last past) ∂historyMeasure := by
          apply integral_congr_ae
          filter_upwards [] with past
          by_cases hmem : past ∈ historyEvent
          · simp [integrand, weight, manyServerMarkedStateHistoryEventIndicator, hmem]
            rw [show historyKernel past = measureKernel (last past) by
              dsimp [historyKernel]
              rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]]
            change (∫ next,
              (manyServerMarkedStateUnrealizedPotentialServiceIncrement
                (last past) next : ℝ) ∂measureKernel (last past)) = idle (last past)
            dsimp [measureKernel, idle]
            exact manyServerMarkedStateUniformizationKernel_unrealizedPotentialServiceIncrement_integral
              trafficIntensity servers hservers (last past)
          · simp [integrand, weight, manyServerMarkedStateHistoryEventIndicator, hmem]
    _ = ∫ path, pastRight (history path) ∂trajectory := by
          exact integral_map hhistory.aemeasurable hpastRight.aestronglyMeasurable
    _ = ∫ path, right path ∂trajectory := by
          rw [hright_eq]
          rfl

/-- The finite-history compensator identity is equivalently the exact
conditional expectation of the next unrealized-potential-service increment
under the natural embedded-coordinate filtration. -/
theorem manyServerMarkedStateUnrealizedPotentialServiceIncrement_condExp_history_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      (fun path =>
        (manyServerMarkedStateUnrealizedPotentialServiceIncrement
          (path index) (path (index + 1)) : ℝ)) |
        piLE index] =ᵐ[trajectory]
      fun path => if (path index).2 then 0 else
        1 - (manyServerBusyFraction servers (path index).1 : ℝ) := by
  classical
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let history : (ℕ → ℕ × Bool) → ((i : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let last : ((i : Finset.Iic index) → ℕ × Bool) → ℕ × Bool :=
    fun past => past ⟨index, Finset.mem_Iic.mpr le_rfl⟩
  let f : (ℕ → ℕ × Bool) → ℝ :=
    fun path =>
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement
        (path index) (path (index + 1)) : ℝ)
  let idle : (ℕ × Bool) → ℝ :=
    fun current => if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ)
  let g : (ℕ → ℕ × Bool) → ℝ := fun path => idle (path index)
  let pastIdle : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    fun past => idle (last past)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hpair : Measurable (fun path : ℕ → ℕ × Bool =>
      (path index, path (index + 1))) :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  have hincrement : Measurable (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      manyServerMarkedStateUnrealizedPotentialServiceIncrement statePair.1 statePair.2) :=
    measurable_of_countable _
  have hfmeas : Measurable f := by
    exact (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp
      (hincrement.comp hpair)
  have hf : Integrable f trajectory := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [f]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast
      manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
        (path index) (path (index + 1))
  have hidle_meas : Measurable idle := measurable_of_countable _
  have hgmeas : Measurable g := hidle_meas.comp (measurable_pi_apply index)
  have hg : Integrable g trajectory := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [g, idle]
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hbusy_nonneg :
            0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
        have hbusy_le :
            (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast
            manyServerBusyFraction_le_one servers (path index).1 hservers
        have hnonnegative :
            0 ≤ 1 - (manyServerBusyFraction servers (path index).1 : ℝ) := by
          linarith
        have hle :
            1 - (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          linarith
        rw [abs_of_nonneg hnonnegative]
        exact hle
    | true => simp
  have hpastIdle_meas : Measurable pastIdle := measurable_of_countable _
  have hg_eq : g = pastIdle ∘ history := by
    funext path
    rfl
  have hgm : AEStronglyMeasurable[piLE index] g trajectory := by
    rw [hg_eq, piLE_eq_comap_frestrictLe]
    apply StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hpastIdle_meas.comap_le
  change trajectory[f | piLE index] =ᵐ[trajectory] g
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le index) hf
    (fun s _ _ => hg.integrableOn) ?_ hgm
  rintro s hs _
  rw [piLE_eq_comap_frestrictLe] at hs
  rcases hs with ⟨historyEvent, hhistoryEvent, rfl⟩
  have hcomp :=
    manyServerMarkedStateTrajectory_unrealizedPotentialServiceIncrement_history_indicator_integral_from_initial
      initial trafficIntensity servers hservers index historyEvent hhistoryEvent
  have hEvent : MeasurableSet (history ⁻¹' historyEvent) :=
    hhistoryEvent.preimage (Preorder.measurable_frestrictLe index)
  rw [← integral_indicator hEvent, ← integral_indicator hEvent]
  calc
    ∫ x, (history ⁻¹' historyEvent).indicator g x ∂trajectory =
        ∫ path,
          manyServerMarkedStateHistoryEventIndicator historyEvent (history path) *
            idle (path index) ∂trajectory := by
              apply integral_congr_ae
              filter_upwards [] with path
              by_cases hmem : history path ∈ historyEvent <;>
                simp [Set.indicator, manyServerMarkedStateHistoryEventIndicator, hmem, g]
    _ = ∫ path,
          manyServerMarkedStateHistoryEventIndicator historyEvent (history path) *
            f path ∂trajectory := by
              simpa [trajectory, markedInitial, measureKernel, history, f, idle] using hcomp.symm
    _ = ∫ x, (history ⁻¹' historyEvent).indicator f x ∂trajectory := by
              symm
              apply integral_congr_ae
              filter_upwards [] with path
              by_cases hmem : history path ∈ historyEvent <;>
                simp [Set.indicator, manyServerMarkedStateHistoryEventIndicator, hmem, f]

/-- The centered one-step unrealized-potential-service correction: the literal
unused potential-service count minus its state-dependent idle-fraction mean. -/
def manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
    (servers : ℕ) (index : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  (manyServerMarkedStateUnrealizedPotentialServiceIncrement
    (path index) (path (index + 1)) : ℝ) -
      if (path index).2 then 0 else
        1 - (manyServerBusyFraction servers (path index).1 : ℝ)

/-- The accumulated centered unrealized-potential-service correction through
the first `n` embedded events. -/
def manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
    (servers : ℕ) (n : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  ∑ i ∈ Finset.range n,
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers i path

/-- A centered correction prefix depends only on the embedded states through
the endpoint of that prefix. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_congr_prefix
    (servers n : ℕ) {first second : ℕ → ℕ × Bool}
    (hprefix : ∀ index ≤ n, first index = second index) :
    manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers n first =
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers n second := by
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
  apply Finset.sum_congr rfl
  intro index hindex
  have hindex_lt : index < n := Finset.mem_range.mp hindex
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
  rw [hprefix index (Nat.le_of_lt hindex_lt),
    hprefix (index + 1) (Nat.succ_le_of_lt hindex_lt)]

/-- The predictable embedded compensator obtained by summing the current
idle fraction at every potential-event index. -/
def manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) : ℝ :=
  ∑ index ∈ Finset.range steps,
    if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)

/-- The predictable idle-fraction compensator through a finite embedded
prefix depends only on the states used by that prefix. -/
theorem manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_congr_prefix
    (servers steps : ℕ) {first second : ℕ → ℕ × Bool}
    (hprefix : ∀ index < steps, first index = second index) :
    manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix servers first steps =
      manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix servers second steps := by
  unfold manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
  apply Finset.sum_congr rfl
  intro index hindex
  rw [hprefix index (Finset.mem_range.mp hindex)]

/-- The embedded idle-fraction compensator is measurable for every finite
prefix length. -/
theorem measurable_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
    (servers steps : ℕ) :
    Measurable
      (fun path : ℕ → ℕ × Bool =>
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps) := by
  unfold manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
  apply Finset.measurable_sum
  intro index _
  exact (measurable_of_countable (fun current : ℕ × Bool =>
    if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ))).comp
    (measurable_pi_apply index)

/-- The finite embedded idle-fraction compensator is nonnegative and is at
most the number of potential-event indices. -/
theorem manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_nonneg_le
    (servers : ℕ) (hservers : 0 < servers) (path : ℕ → ℕ × Bool) (steps : ℕ) :
    0 ≤ manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
      servers path steps ∧
    manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
      servers path steps ≤ steps := by
  unfold manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
  have hterm : ∀ index : ℕ,
      0 ≤ (if (path index).2 then 0 else
        1 - (manyServerBusyFraction servers (path index).1 : ℝ)) ∧
      (if (path index).2 then 0 else
        1 - (manyServerBusyFraction servers (path index).1 : ℝ)) ≤ 1 := by
    intro index
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hbusy_nonneg :
            0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
        have hbusy_le :
            (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast
            manyServerBusyFraction_le_one servers (path index).1 hservers
        constructor <;> linarith
    | true => simp
  constructor
  · exact Finset.sum_nonneg fun index _ => (hterm index).1
  · calc
      ∑ index ∈ Finset.range steps,
          (if (path index).2 then 0 else
            1 - (manyServerBusyFraction servers (path index).1 : ℝ)) ≤
          ∑ _index ∈ Finset.range steps, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro index _
            exact (hterm index).2
      _ = steps := by simp

/-- Along a service-only finite prefix, the predictable unused-service
compensator differs from its initial-idle-fraction approximation by at most
the horizon squared divided by the server count. -/
theorem abs_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_steps_mul_initialIdle_le
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) (hservers : 0 < servers)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
    (hmarks : ∀ index ≤ steps, (path index).2 = false) :
    |manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers path steps -
      (steps : ℝ) * manyServerMarkedStateIdleFractionAt servers 0 path| ≤
        (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by
  have hidleDiff : ∀ index : ℕ,
      |manyServerMarkedStateIdleFractionAt servers index path -
          manyServerMarkedStateIdleFractionAt servers 0 path| ≤
        (index : ℝ) * (1 / (servers : ℝ)) := by
    intro index
    induction index with
    | zero => simp
    | succ index ih =>
        calc
          |manyServerMarkedStateIdleFractionAt servers (index + 1) path -
              manyServerMarkedStateIdleFractionAt servers 0 path| ≤
              |manyServerMarkedStateIdleFractionAt servers (index + 1) path -
                  manyServerMarkedStateIdleFractionAt servers index path| +
                |manyServerMarkedStateIdleFractionAt servers index path -
                  manyServerMarkedStateIdleFractionAt servers 0 path| :=
            abs_sub_le _ _ _
          _ ≤ 1 / (servers : ℝ) + (index : ℝ) * (1 / (servers : ℝ)) := by
            apply add_le_add
            · exact (hstep index).abs_idleFraction_sub_le_one_div servers hservers
            · exact ih
          _ = ((index + 1 : ℕ) : ℝ) * (1 / (servers : ℝ)) := by
            norm_num [Nat.cast_add]
            ring
  have hcompensator : manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
      servers path steps = ∑ index ∈ Finset.range steps,
        manyServerMarkedStateIdleFractionAt servers index path := by
    unfold manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
    apply Finset.sum_congr rfl
    intro index hindex
    have hindex_le : index ≤ steps := Nat.le_of_lt (Finset.mem_range.mp hindex)
    simp [hmarks index hindex_le, manyServerMarkedStateIdleFractionAt]
  have hsum :
      manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps -
        (steps : ℝ) * manyServerMarkedStateIdleFractionAt servers 0 path =
        ∑ index ∈ Finset.range steps,
          (manyServerMarkedStateIdleFractionAt servers index path -
            manyServerMarkedStateIdleFractionAt servers 0 path) := by
    rw [hcompensator, Finset.sum_sub_distrib]
    simp
  rw [hsum]
  calc
    |∑ index ∈ Finset.range steps,
        (manyServerMarkedStateIdleFractionAt servers index path -
          manyServerMarkedStateIdleFractionAt servers 0 path)| ≤
        ∑ index ∈ Finset.range steps,
          |manyServerMarkedStateIdleFractionAt servers index path -
            manyServerMarkedStateIdleFractionAt servers 0 path| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index ∈ Finset.range steps,
        (steps : ℝ) * (1 / (servers : ℝ)) := by
      apply Finset.sum_le_sum
      intro index hindex
      have hindex_le : index ≤ steps := Nat.le_of_lt (Finset.mem_range.mp hindex)
      calc
        |manyServerMarkedStateIdleFractionAt servers index path -
            manyServerMarkedStateIdleFractionAt servers 0 path| ≤
            (index : ℝ) * (1 / (servers : ℝ)) := hidleDiff index
        _ ≤ (steps : ℝ) * (1 / (servers : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hindex_le
          · positivity
    _ = (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by simp

/-- Shifting the retained potential-service mark forward by one event gives
endpoint terms plus the discrete variation of the state idle fraction. -/
theorem manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_nextPotentialServiceIdlePrefix
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers path (steps + 1) -
      manyServerMarkedStateNextPotentialServiceIdlePrefix servers path (steps + 1) =
      (if (path 0).2 then 0 else manyServerMarkedStateIdleFractionAt servers 0 path) -
        (if (path (steps + 1)).2 then 0 else
          manyServerMarkedStateIdleFractionAt servers steps path) +
        ∑ index ∈ Finset.range steps,
          (if (path (index + 1)).2 then 0 else 1) *
            (manyServerMarkedStateIdleFractionAt servers (index + 1) path -
              manyServerMarkedStateIdleFractionAt servers index path) := by
  let current : ℕ → ℝ := fun index =>
    if (path index).2 then 0 else
      manyServerMarkedStateIdleFractionAt servers index path
  let shifted : ℕ → ℝ := fun index =>
    if (path (index + 1)).2 then 0 else
      manyServerMarkedStateIdleFractionAt servers index path
  have hcurrent (n : ℕ) :
      manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path n = ∑ index ∈ Finset.range n, current index := by
    unfold manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
    apply Finset.sum_congr rfl
    intro index _
    rfl
  have hshifted (n : ℕ) :
      manyServerMarkedStateNextPotentialServiceIdlePrefix servers path n =
        ∑ index ∈ Finset.range n, shifted index := by
    unfold manyServerMarkedStateNextPotentialServiceIdlePrefix
    apply Finset.sum_congr rfl
    intro index _
    rfl
  have htel : ∀ n : ℕ,
      (∑ index ∈ Finset.range (n + 1), current index) -
          ∑ index ∈ Finset.range (n + 1), shifted index =
        current 0 - shifted n +
          ∑ index ∈ Finset.range n, (current (index + 1) - shifted index) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hcurrent_sum :
            (∑ index ∈ Finset.range (n + 1 + 1), current index) =
              (∑ index ∈ Finset.range (n + 1), current index) + current (n + 1) := by
          rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
        have hshifted_sum :
            (∑ index ∈ Finset.range (n + 1 + 1), shifted index) =
              (∑ index ∈ Finset.range (n + 1), shifted index) + shifted (n + 1) := by
          rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
        have hvariation_sum :
            (∑ index ∈ Finset.range (n + 1),
              (current (index + 1) - shifted index)) =
              (∑ index ∈ Finset.range n,
                (current (index + 1) - shifted index)) +
                (current (n + 1) - shifted n) := by
          rw [show n + 1 = n + 1 by rfl, Finset.sum_range_succ]
        rw [hcurrent_sum, hshifted_sum, hvariation_sum]
        linear_combination ih
  rw [hcurrent, hshifted, htel]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  unfold current shifted
  cases (path (index + 1)).2 <;> simp

/-- On a transition-consistent prefix, replacing retained current marks by
the next fresh marks changes the idle compensator by at most endpoint terms
plus one server share per embedded transition. -/
theorem abs_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_nextPotentialServiceIdlePrefix_le
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) (hservers : 0 < servers)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1))) :
    |manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers path (steps + 1) -
      manyServerMarkedStateNextPotentialServiceIdlePrefix servers path (steps + 1)| ≤
      2 + (steps : ℝ) * (1 / (servers : ℝ)) := by
  have hidle : ∀ index : ℕ,
      0 ≤ manyServerMarkedStateIdleFractionAt servers index path ∧
        manyServerMarkedStateIdleFractionAt servers index path ≤ 1 := by
    intro index
    exact manyServerMarkedStateIdleFractionAt_nonneg_le_one
      servers index path hservers
  have hterm : ∀ markIndex idleIndex : ℕ,
      |if (path markIndex).2 then 0 else
        manyServerMarkedStateIdleFractionAt servers idleIndex path| ≤ 1 := by
    intro markIndex idleIndex
    cases hmark : (path markIndex).2 with
    | false =>
        simpa [hmark, abs_of_nonneg (hidle idleIndex).1] using (hidle idleIndex).2
    | true => simp
  have hvariation : ∀ index : ℕ,
      |(if (path (index + 1)).2 then 0 else 1) *
          (manyServerMarkedStateIdleFractionAt servers (index + 1) path -
            manyServerMarkedStateIdleFractionAt servers index path)| ≤
        1 / (servers : ℝ) := by
    intro index
    have hdiff :
        |manyServerMarkedStateIdleFractionAt servers (index + 1) path -
          manyServerMarkedStateIdleFractionAt servers index path| ≤
          1 / (servers : ℝ) := by
      unfold manyServerMarkedStateIdleFractionAt
      exact (hstep index).abs_idleFraction_sub_le_one_div servers hservers
    cases hmark : (path (index + 1)).2 with
    | false =>
        simpa [hmark] using hdiff
    | true => simp
  rw [manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_nextPotentialServiceIdlePrefix]
  calc
    |((if (path 0).2 then 0 else manyServerMarkedStateIdleFractionAt servers 0 path) -
        (if (path (steps + 1)).2 then 0 else
          manyServerMarkedStateIdleFractionAt servers steps path)) +
        ∑ index ∈ Finset.range steps,
          (if (path (index + 1)).2 then 0 else 1) *
            (manyServerMarkedStateIdleFractionAt servers (index + 1) path -
              manyServerMarkedStateIdleFractionAt servers index path)| ≤
        |(if (path 0).2 then 0 else manyServerMarkedStateIdleFractionAt servers 0 path) -
          (if (path (steps + 1)).2 then 0 else
            manyServerMarkedStateIdleFractionAt servers steps path)| +
          |∑ index ∈ Finset.range steps,
            (if (path (index + 1)).2 then 0 else 1) *
              (manyServerMarkedStateIdleFractionAt servers (index + 1) path -
                manyServerMarkedStateIdleFractionAt servers index path)| :=
      abs_add_le _ _
    _ ≤ 2 + ∑ _index ∈ Finset.range steps, 1 / (servers : ℝ) := by
      apply add_le_add
      · calc
          |(if (path 0).2 then 0 else manyServerMarkedStateIdleFractionAt servers 0 path) -
              (if (path (steps + 1)).2 then 0 else
                manyServerMarkedStateIdleFractionAt servers steps path)| ≤
              |if (path 0).2 then 0 else
                manyServerMarkedStateIdleFractionAt servers 0 path| +
                |if (path (steps + 1)).2 then 0 else
                  manyServerMarkedStateIdleFractionAt servers steps path| := by
                    simpa using (abs_sub_le
                      (if (path 0).2 then 0 else
                        manyServerMarkedStateIdleFractionAt servers 0 path)
                      0
                      (if (path (steps + 1)).2 then 0 else
                        manyServerMarkedStateIdleFractionAt servers steps path))
          _ ≤ 1 + 1 := add_le_add (hterm 0 0) (hterm (steps + 1) steps)
          _ = 2 := by norm_num
      · calc
          |∑ index ∈ Finset.range steps,
              (if (path (index + 1)).2 then 0 else 1) *
                (manyServerMarkedStateIdleFractionAt servers (index + 1) path -
                  manyServerMarkedStateIdleFractionAt servers index path)| ≤
              ∑ index ∈ Finset.range steps,
                |(if (path (index + 1)).2 then 0 else 1) *
                  (manyServerMarkedStateIdleFractionAt servers (index + 1) path -
                    manyServerMarkedStateIdleFractionAt servers index path)| := by
                    exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _index ∈ Finset.range steps, 1 / (servers : ℝ) := by
              apply Finset.sum_le_sum
              intro index _
              exact hvariation index
    _ = 2 + (steps : ℝ) * (1 / (servers : ℝ)) := by simp

/-- The centered correction is literally the unrealized-potential-service
prefix minus its predictable idle-fraction compensator. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_eq_unrealizedPotentialServicePrefix_sub_compensator
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) :
    manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
      servers steps path =
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) -
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps := by
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
    manyServerMarkedStateUnrealizedPotentialServicePrefix
    manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
  rw [Finset.sum_sub_distrib, Nat.cast_sum]

/-- The centered one-step correction is measurable on the full trajectory
space. -/
theorem measurable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
    (servers index : ℕ) :
    Measurable
      (manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index) := by
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
  apply Measurable.sub
  · have hpair : Measurable (fun path : ℕ → ℕ × Bool =>
        (path index, path (index + 1))) :=
      (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
    have hunrealized : Measurable (fun path : ℕ → ℕ × Bool =>
        manyServerMarkedStateUnrealizedPotentialServiceIncrement
          (path index) (path (index + 1))) := by
      exact (measurable_of_countable
        (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
          manyServerMarkedStateUnrealizedPotentialServiceIncrement
            statePair.1 statePair.2)).comp hpair
    exact (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp
      hunrealized
  · exact (measurable_of_countable
        (fun current : ℕ × Bool => if current.2 then (0 : ℝ) else
          1 - (manyServerBusyFraction servers current.1 : ℝ))).comp
      (measurable_pi_apply index)

/-- The finite centered correction partial sum is measurable on the full
trajectory space. -/
theorem measurable_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
    (servers n : ℕ) :
    Measurable
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers n) := by
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
  apply Finset.measurable_sum
  intro index _
  exact
    measurable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
      servers index

/-- The centered unrealized-potential-service increment has zero conditional
mean relative to the coordinate history available before that increment. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index |
      piLE index] =ᵐ[trajectory] 0 := by
  classical
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let f : (ℕ → ℕ × Bool) → ℝ := fun path =>
    (manyServerMarkedStateUnrealizedPotentialServiceIncrement
      (path index) (path (index + 1)) : ℝ)
  let idle : (ℕ × Bool) → ℝ := fun current =>
    if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ)
  let g : (ℕ → ℕ × Bool) → ℝ := fun path =>
    idle (path index)
  let history : (ℕ → ℕ × Bool) → ((i : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let last : ((i : Finset.Iic index) → ℕ × Bool) → ℕ × Bool :=
    fun past => past ⟨index, Finset.mem_Iic.mpr le_rfl⟩
  let pastIdle : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    fun past => idle (last past)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hpair : Measurable (fun path : ℕ → ℕ × Bool =>
      (path index, path (index + 1))) :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  have hincrement : Measurable (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      manyServerMarkedStateUnrealizedPotentialServiceIncrement statePair.1 statePair.2) :=
    measurable_of_countable _
  have hfmeas : Measurable f := by
    exact (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp
      (hincrement.comp hpair)
  have hf : Integrable f trajectory := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [f]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast
      manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
        (path index) (path (index + 1))
  have hidle_meas : Measurable idle := measurable_of_countable _
  have hgmeas : Measurable g := hidle_meas.comp (measurable_pi_apply index)
  have hg : Integrable g trajectory := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [g, idle]
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hbusy_nonneg :
            0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
        have hbusy_le :
            (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast
            manyServerBusyFraction_le_one servers (path index).1 hservers
        have hnonnegative :
            0 ≤ 1 - (manyServerBusyFraction servers (path index).1 : ℝ) := by
          linarith
        have hle :
            1 - (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          linarith
        rw [abs_of_nonneg hnonnegative]
        exact hle
    | true => simp
  have hgstrong : StronglyMeasurable[piLE index] g := by
    have hg_eq : g = pastIdle ∘ history := by
      funext path
      rfl
    rw [hg_eq, piLE_eq_comap_frestrictLe]
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (show Measurable pastIdle by exact measurable_of_countable _).comap_le
  have hmean :=
    manyServerMarkedStateUnrealizedPotentialServiceIncrement_condExp_history_from_initial
      initial trafficIntensity servers hservers index
  change trajectory[
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index |
    piLE index] =ᵐ[trajectory] 0
  change trajectory[f - g | piLE index] =ᵐ[trajectory] 0
  calc
    trajectory[f - g | piLE index] =ᵐ[trajectory]
        trajectory[f | piLE index] - trajectory[g | piLE index] :=
      condExp_sub hf hg _
    _ =ᵐ[trajectory] g - trajectory[g | piLE index] := by
      exact hmean.sub (Filter.Eventually.of_forall fun _ => rfl)
    _ =ᵐ[trajectory] 0 := by
      rw [condExp_of_stronglyMeasurable (piLE.le index) hgstrong hg]
      exact Filter.Eventually.of_forall fun _ => sub_self _

/-- The predictable conditional second moment of a centered unrealized
potential-service increment is the Bernoulli variance of its idle-fraction
mean. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_sq_condExp_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      (fun path =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
          servers index path) ^ 2) |
        piLE index] =ᵐ[trajectory]
      fun path =>
        (if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
        (1 - (if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ))) := by
  classical
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let f : (ℕ → ℕ × Bool) → ℝ := fun path =>
    (manyServerMarkedStateUnrealizedPotentialServiceIncrement
      (path index) (path (index + 1)) : ℝ)
  let idle : (ℕ × Bool) → ℝ := fun current =>
    if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ)
  let g : (ℕ → ℕ × Bool) → ℝ := fun path => idle (path index)
  let coefficient : (ℕ → ℕ × Bool) → ℝ := fun path => 1 - 2 * g path
  let history : (ℕ → ℕ × Bool) → ((i : Finset.Iic index) → ℕ × Bool) :=
    Preorder.frestrictLe index
  let last : ((i : Finset.Iic index) → ℕ × Bool) → ℕ × Bool :=
    fun past => past ⟨index, Finset.mem_Iic.mpr le_rfl⟩
  let pastIdle : ((i : Finset.Iic index) → ℕ × Bool) → ℝ :=
    fun past => idle (last past)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hpair : Measurable (fun path : ℕ → ℕ × Bool =>
      (path index, path (index + 1))) :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  have hincrement : Measurable (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      manyServerMarkedStateUnrealizedPotentialServiceIncrement statePair.1 statePair.2) :=
    measurable_of_countable _
  have hfmeas : Measurable f := by
    exact (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp
      (hincrement.comp hpair)
  have hf_bound : ∀ path, |f path| ≤ 1 := by
    intro path
    dsimp [f]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast
      manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
        (path index) (path (index + 1))
  have hf : Integrable f trajectory := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall hf_bound
  have hidle_meas : Measurable idle := measurable_of_countable _
  have hgmeas : Measurable g := hidle_meas.comp (measurable_pi_apply index)
  have hg_bounds : ∀ path, 0 ≤ g path ∧ g path ≤ 1 := by
    intro path
    dsimp [g, idle]
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hbusy_nonneg :
            0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
        have hbusy_le :
            (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast
            manyServerBusyFraction_le_one servers (path index).1 hservers
        constructor <;> linarith
    | true => simp
  have hg_bound : ∀ path, |g path| ≤ 1 := by
    intro path
    rw [abs_of_nonneg (hg_bounds path).1]
    exact (hg_bounds path).2
  have hg : Integrable g trajectory := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall hg_bound
  have hgstrong : StronglyMeasurable[piLE index] g := by
    have hg_eq : g = pastIdle ∘ history := by
      funext path
      rfl
    rw [hg_eq, piLE_eq_comap_frestrictLe]
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (show Measurable pastIdle by exact measurable_of_countable _).comap_le
  have hcoefficient_strong : StronglyMeasurable[piLE index] coefficient := by
    dsimp [coefficient]
    exact stronglyMeasurable_const.sub (hgstrong.const_mul 2)
  have hcoefficient_f : Integrable (coefficient * f) trajectory := by
    apply Integrable.of_bound
      ((hcoefficient_strong.mono (piLE.le index)).aestronglyMeasurable.mul
        hfmeas.aestronglyMeasurable) 1
    filter_upwards [] with path
    have hcoefficient_bound : |coefficient path| ≤ 1 := by
      dsimp [coefficient]
      rw [abs_le]
      constructor <;> nlinarith [(hg_bounds path).1, (hg_bounds path).2]
    simpa [Pi.mul_apply, abs_mul] using
      mul_le_mul hcoefficient_bound (hf_bound path) (abs_nonneg _) zero_le_one
  have hgsq : Integrable (g ^ 2) trajectory := by
    simpa [Pi.pow_apply] using
      (AppliedModelingLib.integrable_sq_of_ae_abs_le hgmeas.aestronglyMeasurable zero_le_one
        (Filter.Eventually.of_forall hg_bound))
  have hmean : trajectory[f | piLE index] =ᵐ[trajectory] g := by
    simpa [trajectory, markedInitial, measureKernel, f, g, idle] using
      manyServerMarkedStateUnrealizedPotentialServiceIncrement_condExp_history_from_initial
        initial trafficIntensity servers hservers index
  have hindicator : ∀ᵐ path ∂trajectory, f path ^ 2 = f path := by
    filter_upwards [] with path
    simpa [f] using
      sq_manyServerMarkedStateUnrealizedPotentialServiceIncrement_eq
        (path index) (path (index + 1))
  change trajectory[(fun path => (f path - g path) ^ 2) | piLE index] =ᵐ[trajectory]
    fun path => g path * (1 - g path)
  simpa [coefficient] using
    (AppliedModelingLib.condExp_centered_indicator_sq_eq_conditional_variance
      (μ := trajectory) (m := piLE index) (f := f) (g := g)
      (hf := hf)
      (hcoefficient_f := by simpa [coefficient] using hcoefficient_f)
      (hgsq := hgsq) (hm := piLE.le index) (hgstrong := hgstrong)
      (hmean := hmean) (hindicator := hindicator))

/-- Each centered unrealized-potential-service increment is integrable under
the arbitrary-initial marked trajectory law. -/
theorem integrable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (index : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Integrable
      (manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index)
      trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let f : (ℕ → ℕ × Bool) → ℝ := fun path =>
    (manyServerMarkedStateUnrealizedPotentialServiceIncrement
      (path index) (path (index + 1)) : ℝ)
  let idle : (ℕ × Bool) → ℝ := fun current =>
    if current.2 then 0 else
      1 - (manyServerBusyFraction servers current.1 : ℝ)
  let g : (ℕ → ℕ × Bool) → ℝ := fun path =>
    idle (path index)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hpair : Measurable (fun path : ℕ → ℕ × Bool =>
      (path index, path (index + 1))) :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  have hincrement : Measurable (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      manyServerMarkedStateUnrealizedPotentialServiceIncrement statePair.1 statePair.2) :=
    measurable_of_countable _
  have hfmeas : Measurable f := by
    exact (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp
      (hincrement.comp hpair)
  have hf : Integrable f trajectory := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [f]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast
      manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
        (path index) (path (index + 1))
  have hidle_meas : Measurable idle := measurable_of_countable _
  have hgmeas : Measurable g := hidle_meas.comp (measurable_pi_apply index)
  have hg : Integrable g trajectory := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [g, idle]
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hbusy_nonneg :
            0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
        have hbusy_le :
            (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast
            manyServerBusyFraction_le_one servers (path index).1 hservers
        have hnonnegative :
            0 ≤ 1 - (manyServerBusyFraction servers (path index).1 : ℝ) := by
          linarith
        have hle :
            1 - (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          linarith
        rw [abs_of_nonneg hnonnegative]
        exact hle
    | true => simp
  change Integrable (f - g) trajectory
  exact hf.sub hg

/-- The centered correction accumulated before each embedded index is adapted
to the natural coordinate-history filtration. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_stronglyAdapted
    (servers : ℕ) :
    StronglyAdapted piLE
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers) := by
  intro n
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
  have hsum : StronglyMeasurable[piLE n]
      (∑ i ∈ Finset.range n,
        manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers i) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hilt : i < n := Finset.mem_range.mp hi
    have hin : i ≤ n := Nat.le_of_lt hilt
    let history : (ℕ → ℕ × Bool) → ((j : Finset.Iic n) → ℕ × Bool) :=
      Preorder.frestrictLe n
    let term : ((j : Finset.Iic n) → ℕ × Bool) → ℝ := fun past =>
      (manyServerMarkedStateUnrealizedPotentialServiceIncrement
        (past ⟨i, Finset.mem_Iic.mpr hin⟩)
        (past ⟨i + 1, Finset.mem_Iic.mpr (Nat.succ_le_iff.mpr hilt)⟩) : ℝ) -
          if (past ⟨i, Finset.mem_Iic.mpr hin⟩).2 then 0 else
            1 - (manyServerBusyFraction servers
              (past ⟨i, Finset.mem_Iic.mpr hin⟩).1 : ℝ)
    have hterm : Measurable term := measurable_of_countable _
    have heq :
        manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers i =
          term ∘ history := by
      funext path
      rfl
    rw [heq, piLE_eq_comap_frestrictLe]
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hterm.comap_le
  convert hsum using 1
  ext path
  simp

/-- Every finite centered unused-service prefix has mean zero under an
arbitrary-initial marked many-server trajectory. -/
theorem integral_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_eq_zero_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (steps : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    ∫ path,
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers steps path ∂trajectory = 0 := by
  dsimp only
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro index _
    calc
      (∫ path,
        manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
          servers index path ∂trajectory) =
          ∫ path,
            trajectory[
              manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
                servers index | piLE index] path ∂trajectory := by
            exact (integral_condExp (μ := trajectory) (m := piLE index)
              (piLE.le index)
              (f := manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
                servers index)).symm
      _ = ∫ _path : ℕ → ℕ × Bool, (0 : ℝ) ∂trajectory := by
        apply integral_congr_ae
        simpa [trajectory, markedInitial, measureKernel] using
          manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
            initial trafficIntensity servers hservers index
      _ = 0 := by simp
  · intro index _
    simpa [trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers hservers index

/-- The mean unused-service reward over a finite arrival-free horizon differs
from the horizon times the initial idle fraction by at most the horizon
squared divided by the server count.  This is an endpoint-semigroup estimate:
the finite marked-path martingale supplies the mean identity, while the
one-event idle-fraction Lipschitz bound supplies the deterministic error. -/
theorem abs_integral_manyServerServiceOnlyUnrealizedPotentialService_sub_steps_mul_idleFraction_le
    (servers state steps : ℕ) (hservers : 0 < servers) :
    |(∫ next,
      (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ∂
        (CountableMarkovKernel.iterate
          (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure) -
      (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| ≤
      (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF (PMF.pure state) 0
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel 0 servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hunused : Integrable (fun path : ℕ → ℕ × Bool =>
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ))
      trajectory := by
    apply Integrable.of_bound
      ((Measurable.of_discrete : Measurable (fun count : ℕ => (count : ℝ))).comp
        (measurable_manyServerMarkedStateUnrealizedPotentialServicePrefix steps)).aestronglyMeasurable
      (steps : ℝ)
    filter_upwards [] with path
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) ≤
      (steps : ℝ)
    exact_mod_cast
      manyServerMarkedStateUnrealizedPotentialServicePrefix_le_steps path steps
  have hcompensator : Integrable (fun path : ℕ → ℕ × Bool =>
      manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers path steps) trajectory := by
    apply Integrable.of_bound
      (measurable_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers steps).aestronglyMeasurable (steps : ℝ)
    filter_upwards [] with path
    rw [Real.norm_eq_abs, abs_of_nonneg
      (manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_nonneg_le
        servers hservers path steps).1]
    exact
      (manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_nonneg_le
        servers hservers path steps).2
  have hcentered : (∫ path,
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers steps path ∂trajectory) = 0 := by
    simpa [trajectory, markedInitial, measureKernel] using
      (integral_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_eq_zero_from_initial
        (PMF.pure state) 0 servers hservers steps)
  have hmean : (∫ path : ℕ → ℕ × Bool,
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) ∂trajectory) =
      ∫ path : ℕ → ℕ × Bool,
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps ∂trajectory := by
    have hzero : (∫ path : ℕ → ℕ × Bool,
        (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) -
          manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
            servers path steps ∂trajectory) = 0 := by
      calc
        (∫ path : ℕ → ℕ × Bool,
          (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) -
            manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
              servers path steps ∂trajectory) =
            ∫ path,
              manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
                servers steps path ∂trajectory := by
              apply integral_congr_ae
              filter_upwards [] with path
              symm
              exact
                manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_eq_unrealizedPotentialServicePrefix_sub_compensator
                  servers path steps
        _ = 0 := hcentered
    rw [integral_sub hunused hcompensator] at hzero
    linarith
  have hinitialLaw : HasLaw (fun path : ℕ → ℕ × Bool => (path 0).1)
      (PMF.pure state).toMeasure trajectory := by
    simpa [trajectory, markedInitial, measureKernel, CountableMarkovKernel.iterate] using
      (manyServerMarkedStateTrajectory_queueStateAt_hasLaw
        (PMF.pure state) 0 servers hservers 0)
  have hinitial : ∀ᵐ path ∂trajectory, (path 0).1 = state := by
    refine (hinitialLaw.ae_iff (p := fun initialState : ℕ => initialState = state)
      (measurable_of_countable _)).2 ?_
    simp only [PMF.toMeasure_pure, ae_dirac_eq, Filter.eventually_pure]
  have hstep : ∀ᵐ path ∂trajectory,
      ∀ index : ℕ, ManyServerMarkedStateStepAllowed
        (path index) (path (index + 1)) := by
    simpa [trajectory, markedInitial, measureKernel] using
      (ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
        (PMF.pure state) 0 servers hservers)
  have hmarks : ∀ᵐ path ∂trajectory,
      ∀ index ≤ steps, (path index).2 = false := by
    simpa [trajectory, markedInitial, measureKernel] using
      (ae_manyServerMarkedStateTrajectory_serviceMarks_false_of_zero
        (PMF.pure state) servers hservers steps)
  have hpathBound : ∀ᵐ path ∂trajectory,
      |manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps -
        (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| ≤
        (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by
    filter_upwards [hstep, hmarks, hinitial] with path hpathStep hpathMarks hpathInitial
    simpa [manyServerMarkedStateIdleFractionAt, hpathInitial] using
      (abs_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_steps_mul_initialIdle_le
        servers path steps hservers hpathStep hpathMarks)
  have hcompensatorBound :
      |(∫ path : ℕ → ℕ × Bool,
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps ∂trajectory) -
        (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| ≤
        (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by
    calc
      |(∫ path : ℕ → ℕ × Bool,
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps ∂trajectory) -
          (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| =
          |(∫ path : ℕ → ℕ × Bool,
            manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
              servers path steps ∂trajectory) -
            ∫ _path : ℕ → ℕ × Bool,
              (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ)) ∂trajectory| := by
            simp
      _ = |∫ path : ℕ → ℕ × Bool,
          manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
            servers path steps -
            (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ)) ∂trajectory| := by
          rw [integral_sub hcompensator (integrable_const _)]
      _ ≤ ((steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ)))) *
          trajectory.real Set.univ := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_of_norm_le_const
              (μ := trajectory)
              (f := fun path : ℕ → ℕ × Bool =>
                manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
                  servers path steps -
                  (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ)))
              hpathBound)
      _ = (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by simp
  have hendpoint : (∫ path : ℕ → ℕ × Bool,
      (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) ∂trajectory) =
      ∫ next,
        (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ∂
          (CountableMarkovKernel.iterate
            (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure := by
    simpa [trajectory, markedInitial, measureKernel] using
      (integral_manyServerMarkedStateTrajectory_unrealizedPotentialServicePrefix_eq_serviceOnly
        servers state steps hservers)
  calc
    |(∫ next,
      (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ∂
        (CountableMarkovKernel.iterate
          (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure) -
      (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| =
        |(∫ path : ℕ → ℕ × Bool,
          (manyServerMarkedStateUnrealizedPotentialServicePrefix path steps : ℝ) ∂trajectory) -
          (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| := by
          rw [hendpoint]
    _ = |(∫ path : ℕ → ℕ × Bool,
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path steps ∂trajectory) -
        (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ))| := by
          rw [hmean]
    _ ≤ (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := hcompensatorBound

/-- The second moment of a finite arrival-free unrealized-service reward
retains the initial idle-fraction factor.  The elementary bound
`U² ≤ steps · U`, together with the finite-prefix mean estimate, gives a
third-order remainder in the number of potential opportunities. -/
theorem integral_sq_manyServerServiceOnlyUnrealizedPotentialService_le
    (servers state steps : ℕ) (hservers : 0 < servers) :
    (∫ next,
      (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ^ 2 ∂
        (CountableMarkovKernel.iterate
          (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure) ≤
      (steps : ℝ) ^ 2 * (1 - (manyServerBusyFraction servers state : ℝ)) +
        (steps : ℝ) ^ 3 * (1 / (servers : ℝ)) := by
  let endpointLaw : Measure ℕ :=
    (CountableMarkovKernel.iterate
      (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure
  let reward : ℕ → ℝ := fun next =>
    (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ)
  have hreward : Integrable reward endpointLaw := by
    simpa [reward, endpointLaw] using
      integrable_manyServerServiceOnlyUnrealizedPotentialService servers state steps hservers
  have hrewardSq : Integrable (fun next => reward next ^ 2) endpointLaw := by
    simpa [reward, endpointLaw] using
      integrable_sq_manyServerServiceOnlyUnrealizedPotentialService servers state steps hservers
  have hmeanBound :
      (∫ next, reward next ∂endpointLaw) ≤
        (steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ)) +
          (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ))) := by
    dsimp only [reward, endpointLaw]
    linarith [
      (abs_le.mp
        (abs_integral_manyServerServiceOnlyUnrealizedPotentialService_sub_steps_mul_idleFraction_le
          servers state steps hservers)).2]
  have hpointwise (next : ℕ) : reward next ^ 2 ≤ (steps : ℝ) * reward next := by
    change (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ^ 2 ≤
      (steps : ℝ) * (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ)
    have hreward_nonneg :
        0 ≤ (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) := by
      exact_mod_cast
        (Nat.zero_le (manyServerServiceOnlyUnrealizedPotentialService state steps next))
    have hreward_le :
        (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ≤
          (steps : ℝ) := by
      exact_mod_cast manyServerServiceOnlyUnrealizedPotentialService_le_steps state steps next
    nlinarith [mul_nonneg hreward_nonneg (sub_nonneg.mpr hreward_le)]
  have hquadratic :
      (∫ next, reward next ^ 2 ∂endpointLaw) ≤
        (steps : ℝ) * (∫ next, reward next ∂endpointLaw) := by
    calc
      (∫ next, reward next ^ 2 ∂endpointLaw) ≤
          ∫ next, (steps : ℝ) * reward next ∂endpointLaw := by
            exact integral_mono hrewardSq (hreward.const_mul _) hpointwise
      _ = (steps : ℝ) * (∫ next, reward next ∂endpointLaw) := by
            rw [integral_const_mul]
  change (∫ next, reward next ^ 2 ∂endpointLaw) ≤ _
  calc
    (∫ next, reward next ^ 2 ∂endpointLaw) ≤
        (steps : ℝ) * (∫ next, reward next ∂endpointLaw) := hquadratic
    _ ≤ (steps : ℝ) *
          ((steps : ℝ) * (1 - (manyServerBusyFraction servers state : ℝ)) +
            (steps : ℝ) * ((steps : ℝ) * (1 / (servers : ℝ)))) :=
      mul_le_mul_of_nonneg_left hmeanBound (by positivity)
    _ = (steps : ℝ) ^ 2 * (1 - (manyServerBusyFraction servers state : ℝ)) +
          (steps : ℝ) ^ 3 * (1 / (servers : ℝ)) := by
      ring

/-- The compensated unrealized-potential-service partial sums form a
discrete-time martingale under the arbitrary-initial marked trajectory law. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_martingale_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Martingale
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers)
      piLE trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  apply AppliedModelingLib.martingale_partial_sum_of_condExp_eq_zero
  · exact
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_stronglyAdapted
        servers
  · intro n
    apply integrable_finset_sum
    intro i _
    simpa [trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers hservers i
  · intro n
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers n

/-- The unused-service correction stopped before the marked path's predictable
arrival-minus-potential-service lower bound enters a prescribed lower region. -/
noncomputable def manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
    (servers lowerThreshold : ℕ) : ℕ → (ℕ → ℕ × Bool) → ℝ :=
  stoppedProcess
    (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers)
    (manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold)

/-- The lower-barrier-stopped correction is adapted to the same natural
embedded history as the original correction. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_stronglyAdapted
    (servers lowerThreshold : ℕ) :
    StronglyAdapted piLE
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold) := by
  simpa [manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum] using
    StronglyAdapted.stoppedProcess_of_discrete
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_stronglyAdapted
        servers)
      (manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime
        lowerThreshold)

/-- Each stopped correction partial sum is measurable on the full trajectory
space. -/
theorem measurable_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
    (servers lowerThreshold n : ℕ) :
    Measurable
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold n) := by
  exact
    ((manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_stronglyAdapted
      servers lowerThreshold n).mono (piLE.le n)).measurable

/-- Up to a lower-barrier exit time, stopping leaves the original compensated
unused-service partial sum unchanged. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_centered_of_le_lowerExit
    (servers lowerThreshold steps : ℕ) (path : ℕ → ℕ × Bool)
    (hbefore : (steps : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path) :
    manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
      servers lowerThreshold steps path =
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers steps path := by
  unfold manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
  exact stoppedProcess_eq_of_le hbefore

/-- If the predictable lower barrier has not been reached through a finite
prefix, the stopped and original finite correction maxima agree on that
prefix. -/
theorem maximalCenteredUnrealizedPotentialServicePartialSum_eq_stopped_of_le_lowerExit
    (servers lowerThreshold n : ℕ) (path : ℕ → ℕ × Bool)
    (hbefore : (n : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path) :
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index path) ^ 2) =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index path) ^ 2) := by
  apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
  intro index hindex
  have hindex_le : index ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hindex)
  have hindex_exit : (index : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path :=
    le_trans (by exact_mod_cast hindex_le) hbefore
  symm
  rw [manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_centered_of_le_lowerExit
    servers lowerThreshold index path hindex_exit]

/-- The finite stopped correction maximum is measurable on the trajectory
space. -/
theorem measurable_maximalStoppedUnrealizedPotentialServicePartialSum
    (servers lowerThreshold n : ℕ) :
    Measurable (fun path : ℕ → ℕ × Bool =>
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index path) ^ 2)) := by
  induction n with
  | zero =>
      simpa using
        (measurable_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold 0).pow measurable_const
  | succ n ih =>
      simpa [Finset.range_add_one, Finset.sup'_insert] using
        ((measurable_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold (n + 1)).pow measurable_const).max ih

/-- The centered unused-service increment retained before the predictable
lower-barrier exit. -/
noncomputable def manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
    (servers lowerThreshold index : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  if (index : ENat) <
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path then
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index path
  else 0

/-- The retained stopped increment is the indicator of remaining before the
lower exit times the original centered increment. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_eq_indicator
    (servers lowerThreshold index : ℕ) :
    manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index =
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
        (manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index) := by
  funext path
  by_cases hactive : path ∈
      manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · have hcondition : (index : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    unfold manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
    rw [if_pos hcondition, Set.indicator_of_mem hactive]
  · have hcondition : ¬(index : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    unfold manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
    rw [if_neg hcondition, Set.indicator_of_notMem hactive]

/-- The stopped correction is the sum of exactly the centered increments that
occur strictly before the predictable lower-barrier exit. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_sum_before_lowerExit
    (servers lowerThreshold steps : ℕ) (path : ℕ → ℕ × Bool) :
    manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
      servers lowerThreshold steps path =
      ∑ index ∈ Finset.range steps,
        manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
          servers lowerThreshold index path := by
  unfold manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
    stoppedProcess manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
  cases hexit : manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path with
  | top =>
      have hmin : ((steps : WithTop ℕ) ⊓ (⊤ : WithTop ℕ)).untopA = steps := by
        rw [inf_eq_left.mpr le_top]
        exact WithTop.untopA_eq_untop
          (WithTop.coe_ne_top : (steps : WithTop ℕ) ≠ (⊤ : WithTop ℕ)) |>.trans
          (WithTop.untop_coe steps _)
      change (∑ index ∈ Finset.range
        ((steps : WithTop ℕ) ⊓ (⊤ : WithTop ℕ)).untopA,
        manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index path) = _
      rw [hmin]
      apply Finset.sum_congr rfl
      intro index _
      unfold manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      rw [hexit]
      rw [if_pos (ENat.coe_lt_top index)]
  | coe exit =>
      by_cases hsteps : steps ≤ exit
      · have hmin : (steps : WithTop ℕ) ⊓ (exit : WithTop ℕ) = steps := by
          exact inf_eq_left.mpr (by exact_mod_cast hsteps)
        have hmin_untop : ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA = steps := by
          calc
            ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA =
                (steps : WithTop ℕ).untopA := congrArg WithTop.untopA hmin
            _ = steps := by
              exact WithTop.untopA_eq_untop
                (WithTop.coe_ne_top : (steps : WithTop ℕ) ≠ (⊤ : WithTop ℕ)) |>.trans
                (WithTop.untop_coe steps _)
        change (∑ index ∈ Finset.range
          ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA,
          manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index path) = _
        rw [hmin_untop]
        apply Finset.sum_congr rfl
        intro index hindex
        unfold manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
        rw [hexit]
        have hindex_lt : index < exit :=
          lt_of_lt_of_le (Finset.mem_range.mp hindex) hsteps
        have hindex_lt' : (index : ENat) < (exit : ENat) :=
          ENat.coe_lt_coe.mpr hindex_lt
        rw [if_pos hindex_lt']
      · have hexit_lt_steps : exit < steps := Nat.lt_of_not_ge hsteps
        have hmin : (steps : WithTop ℕ) ⊓ (exit : WithTop ℕ) = exit := by
          exact inf_eq_right.mpr (by exact_mod_cast (Nat.le_of_lt hexit_lt_steps))
        have hmin_untop : ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA = exit := by
          calc
            ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA =
                (exit : WithTop ℕ).untopA := congrArg WithTop.untopA hmin
            _ = exit := by
              exact WithTop.untopA_eq_untop
                (WithTop.coe_ne_top : (exit : WithTop ℕ) ≠ (⊤ : WithTop ℕ)) |>.trans
                (WithTop.untop_coe exit _)
        change (∑ index ∈ Finset.range
          ((steps : WithTop ℕ) ⊓ (exit : WithTop ℕ)).untopA,
          manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index path) = _
        rw [hmin_untop]
        have hfilter : (Finset.range steps).filter
            (fun index : ℕ => (index : ENat) < (exit : ENat)) = Finset.range exit := by
          ext index
          simp only [Finset.mem_filter, Finset.mem_range]
          rw [ENat.coe_lt_coe]
          omega
        simp only [manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement, hexit]
        rw [← Finset.sum_filter]
        rw [hfilter]

/-- Each retained stopped increment is the one-step difference of the stopped
compensated unused-service partial sum. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_eq_partialSum_succ_sub
    (servers lowerThreshold index : ℕ) (path : ℕ → ℕ × Bool) :
    manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index path =
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold (index + 1) path -
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold index path := by
  rw [manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_sum_before_lowerExit,
    manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_sum_before_lowerExit,
    Finset.sum_range_succ]
  ring

/-- Stopping at the predictable lower-barrier exit preserves the compensated
unused-service martingale under every initial queue law. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_martingale_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Martingale
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold)
      piLE trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers hservers
  rw [manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum,
    martingale_iff]
  constructor
  · have hneg : Submartingale
        (-stoppedProcess
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers)
          (manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold))
        piLE trajectory := by
      simpa only [Pi.neg_apply] using
        Submartingale.stoppedProcess hmartingale.neg.submartingale
          (manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime lowerThreshold)
    simpa only [neg_neg] using hneg.neg
  · exact Submartingale.stoppedProcess hmartingale.submartingale
      (manyServerMarkedStateArrivalPotentialLowerExitTime_isStoppingTime lowerThreshold)

/-- Under every initial law, each increment retained by the lower-barrier
stopping rule is integrable. -/
theorem integrable_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    Integrable
      (manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
        servers lowerThreshold index)
      trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have heq : manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index =
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold (index + 1) -
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold index := by
    funext path
    exact
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_eq_partialSum_succ_sub
        servers lowerThreshold index path
  rw [heq]
  exact (hmartingale.integrable (index + 1)).sub (hmartingale.integrable index)

/-- The lower-barrier-stopped unused-service increment has conditional mean
zero with respect to the current marked embedded history. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
        servers lowerThreshold index | piLE index] =ᵐ[trajectory] 0 := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have heq : manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index =
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold (index + 1) -
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold index := by
    funext path
    exact
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_eq_partialSum_succ_sub
        servers lowerThreshold index path
  rw [heq]
  calc
    trajectory[
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold (index + 1) -
          manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index | piLE index] =ᵐ[trajectory]
        trajectory[
          manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold (index + 1) | piLE index] -
          trajectory[
            manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
              servers lowerThreshold index | piLE index] :=
      condExp_sub (hmartingale.integrable (index + 1))
        (hmartingale.integrable index) _
    _ =ᵐ[trajectory]
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold index -
          manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index :=
      (hmartingale.condExp_ae_eq (Nat.le_succ index)).sub
        (Filter.Eventually.of_forall fun path =>
          congrFun
            (condExp_of_stronglyMeasurable (piLE.le index)
              (hmartingale.stronglyMeasurable index) (hmartingale.integrable index))
            path)
    _ =ᵐ[trajectory] 0 := Filter.Eventually.of_forall fun _ => sub_self _

/-- Every centered unrealized-potential-service increment is bounded by one
in absolute value. -/
theorem abs_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_le_one
    (servers : ℕ) (hservers : 0 < servers) (index : ℕ)
    (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
      servers index path| ≤ 1 := by
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement
  by_cases hmark : (path index).2
  · simp [manyServerMarkedStateUnrealizedPotentialServiceIncrement,
      manyServerMarkedStatePotentialServiceIncrement,
      manyServerMarkedStateDepartureIncrement, hmark]
  · simp only [hmark]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hpotential_nonneg :
        0 ≤ (manyServerMarkedStateUnrealizedPotentialServiceIncrement
          (path index) (path (index + 1)) : ℝ) := by positivity
    have hpotential_le :
        (manyServerMarkedStateUnrealizedPotentialServiceIncrement
          (path index) (path (index + 1)) : ℝ) ≤ 1 := by
      exact_mod_cast
        manyServerMarkedStateUnrealizedPotentialServiceIncrement_le_one
          (path index) (path (index + 1))
    have hbusy_nonneg :
        0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
    have hbusy_le :
        (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
      exact_mod_cast
        manyServerBusyFraction_le_one servers (path index).1 hservers
    rw [abs_le]
    constructor <;> linarith

/-- Lower-barrier stopping never enlarges a centered unused-service
increment. -/
theorem abs_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_le_one
    (servers lowerThreshold index : ℕ) (hservers : 0 < servers)
    (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index path| ≤ 1 := by
  rw [manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_eq_indicator]
  by_cases hactive : path ∈
      manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · rw [Set.indicator_of_mem hactive]
    exact abs_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_le_one
      servers hservers index path
  · rw [Set.indicator_of_notMem hactive]
    norm_num

/-- The predictable conditional second moment of the stopped unused-service
increment is the original Bernoulli variance, retained only while the
lower-barrier stopping rule is active. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_sq_condExp_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    trajectory[
      (fun path =>
        (manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
          servers lowerThreshold index path) ^ 2) | piLE index] =ᵐ[trajectory]
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
        (fun path =>
          (if (path index).2 then 0 else
            1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
          (1 - (if (path index).2 then 0 else
            1 - (manyServerBusyFraction servers (path index).1 : ℝ)))) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Y : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers index
  let Z : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index
  let active : Set (ℕ → ℕ × Bool) :=
    manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  let variance : (ℕ → ℕ × Bool) → ℝ := fun path =>
    (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
    (1 - (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)))
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hY : Integrable Y trajectory := by
    simpa [Y, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers hservers index
  have hYbound : ∀ᵐ path ∂trajectory, |Y path| ≤ 1 :=
    Filter.Eventually.of_forall fun path =>
      abs_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_le_one
        servers hservers index path
  have hYsq : Integrable (fun path => (Y path) ^ 2) trajectory := by
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le hY.aestronglyMeasurable zero_le_one
    exact hYbound
  have hactive : MeasurableSet[piLE index] active := by
    simpa [active] using
      manyServerMarkedStateLowerExitActiveSet_measurableSet lowerThreshold index
  have hZeq : Z = active.indicator Y := by
    simpa [Z, active, Y] using
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_eq_indicator
        servers lowerThreshold index
  have hZsq : (fun path => (Z path) ^ 2) =
      active.indicator (fun path => (Y path) ^ 2) := by
    rw [hZeq]
    funext path
    by_cases hpath : path ∈ active
    · rw [Set.indicator_of_mem hpath, Set.indicator_of_mem hpath]
    · rw [Set.indicator_of_notMem hpath, Set.indicator_of_notMem hpath]
      simp
  have hvariance : trajectory[(fun path => (Y path) ^ 2) | piLE index] =ᵐ[trajectory]
      variance := by
    simpa [Y, variance, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_sq_condExp_from_initial
        initial trafficIntensity servers hservers index
  change trajectory[(fun path => (Z path) ^ 2) | piLE index] =ᵐ[trajectory]
    active.indicator variance
  rw [hZsq]
  calc
    trajectory[active.indicator (fun path => (Y path) ^ 2) | piLE index] =ᵐ[trajectory]
        active.indicator (trajectory[(fun path => (Y path) ^ 2) | piLE index]) :=
      condExp_indicator hYsq hactive
    _ =ᵐ[trajectory] active.indicator variance := by
      filter_upwards [hvariance] with path hpath
      by_cases hpath_active : path ∈ active
      · rw [Set.indicator_of_mem hpath_active, Set.indicator_of_mem hpath_active, hpath]
      · rw [Set.indicator_of_notMem hpath_active, Set.indicator_of_notMem hpath_active]

/-- On a transition-consistent marked path, the stopped conditional-variance
integrand is bounded by the idle fraction at its fixed lower threshold. -/
theorem manyServerMarkedStateStoppedVariance_le_idleFraction_at_lowerThreshold
    (servers lowerThreshold index : ℕ) (hservers : 0 < servers)
    (path : ℕ → ℕ × Bool)
    (hstep : ∀ step : ℕ,
      ManyServerMarkedStateStepAllowed (path step) (path (step + 1))) :
    (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
      (fun path =>
        (if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
        (1 - (if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ)))) path ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  have hthreshold_nonneg : 0 ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  by_cases hactive : path ∈
      manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · rw [Set.indicator_of_mem hactive]
    have hbefore : (index : ℕ∞) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    have hidle : 1 - (manyServerBusyFraction servers (path index).1 : ℝ) ≤
        1 - (manyServerBusyFraction servers lowerThreshold : ℝ) :=
      one_sub_manyServerBusyFraction_le_of_lt_lowerExitTime
        servers lowerThreshold index path hstep hbefore
    by_cases hmark : (path index).2
    · simp [hmark, hthreshold_nonneg]
    · simp only [hmark, Bool.false_eq_true, ↓reduceIte]
      have hidle_nonneg : 0 ≤
          1 - (manyServerBusyFraction servers (path index).1 : ℝ) := by
        have hbusy_le : (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast manyServerBusyFraction_le_one servers (path index).1 hservers
        linarith
      have hfactor_le_one :
          1 - (1 - (manyServerBusyFraction servers (path index).1 : ℝ)) ≤ 1 := by
        linarith
      calc
        (1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
            (1 - (1 - (manyServerBusyFraction servers (path index).1 : ℝ))) ≤
            1 - (manyServerBusyFraction servers (path index).1 : ℝ) :=
          mul_le_of_le_one_right hidle_nonneg hfactor_le_one
        _ ≤ 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := hidle
  · rw [Set.indicator_of_notMem hactive]
    exact hthreshold_nonneg

/-- The second moment of one stopped unused-service increment is bounded by
the deterministic idle fraction at the lower threshold. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_secondMoment_le_idleFraction_at_lowerThreshold_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold index : ℕ)
    (hservers : 0 < servers) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
        servers lowerThreshold index path) ^ 2 ∂trajectory) ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Z : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold index
  let variance : (ℕ → ℕ × Bool) → ℝ := fun path =>
    (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
    (1 - (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)))
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hZintegrable : Integrable Z trajectory := by
    simpa [Z, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hZbound : ∀ᵐ path ∂trajectory, |Z path| ≤ 1 :=
    Filter.Eventually.of_forall fun path =>
      abs_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_le_one
        servers lowerThreshold index hservers path
  have hZsq : Integrable (fun path => (Z path) ^ 2) trajectory := by
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le hZintegrable.aestronglyMeasurable zero_le_one
    exact hZbound
  have hcond : trajectory[(fun path => (Z path) ^ 2) | piLE index] =ᵐ[trajectory]
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator variance := by
    simpa [Z, variance, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_sq_condExp_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hvariance_bound : ∀ᵐ path ∂trajectory,
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
        variance path ≤ 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    filter_upwards [ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers] with path hstep
    exact manyServerMarkedStateStoppedVariance_le_idleFraction_at_lowerThreshold
      servers lowerThreshold index hservers path hstep
  have hindicatorVarianceInt :
      Integrable
        ((manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator variance)
        trajectory :=
    (integrable_condExp (μ := trajectory) (m := piLE index)
      (f := fun path => (Z path) ^ 2)).congr hcond
  calc
    (∫ path, (Z path) ^ 2 ∂trajectory) =
        ∫ path, trajectory[(fun path => (Z path) ^ 2) | piLE index] path ∂trajectory := by
          exact (integral_condExp (μ := trajectory) (m := piLE index)
            (piLE.le index) (f := fun path => (Z path) ^ 2)).symm
    _ = ∫ path,
        (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
          variance path ∂trajectory := integral_congr_ae hcond
    _ ≤ ∫ _path : ℕ → ℕ × Bool,
        1 - (manyServerBusyFraction servers lowerThreshold : ℝ) ∂trajectory := by
          exact integral_mono_ae hindicatorVarianceInt (integrable_const _) hvariance_bound
    _ = 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by simp

/-- Before the predictable lower-barrier exit, the stopped unused-service
martingale has second moment at most its horizon times the idle fraction at the
barrier. -/
theorem manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_secondMoment_le_lowerThreshold_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold n path) ^ 2 ∂trajectory) ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Y : ℕ → (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
      servers lowerThreshold
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have hsum_eq :
      (fun steps path => ∑ index ∈ Finset.range steps, Y index path) =
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold := by
    funext steps path
    symm
    exact
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_sum_before_lowerExit
        servers lowerThreshold steps path
  have hadapted : StronglyAdapted piLE
      (fun steps path => ∑ index ∈ Finset.range steps, Y index path) := by
    rw [hsum_eq]
    exact hmartingale.stronglyAdapted
  have hY_integrable : ∀ index, Integrable (Y index) trajectory := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hY_bound : ∀ index, ∀ᵐ path ∂trajectory, |Y index path| ≤ 1 := by
    intro index
    exact Filter.Eventually.of_forall fun path =>
      abs_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_le_one
        servers lowerThreshold index hservers path
  have hsum_bound : ∀ steps, ∀ᵐ path ∂trajectory,
      |∑ index ∈ Finset.range steps, Y index path| ≤ steps := by
    intro steps
    exact Filter.Eventually.of_forall fun path => by
      calc
        |∑ index ∈ Finset.range steps, Y index path| ≤
            ∑ index ∈ Finset.range steps, |Y index path| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _index ∈ Finset.range steps, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro index hindex
              exact
                abs_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_le_one
                  servers lowerThreshold index hservers path
        _ = steps := by simp
  have hsum_sq_int : ∀ steps,
      Integrable (fun path =>
        (∑ index ∈ Finset.range steps, Y index path) ^ 2) trajectory := by
    intro steps
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (((hadapted steps).mono (piLE.le steps)).aestronglyMeasurable)
      (Nat.cast_nonneg steps)
    exact hsum_bound steps
  have hcross_int : ∀ index,
      Integrable (fun path =>
        (∑ previous ∈ Finset.range index, Y previous path) * Y index path)
        trajectory := by
    intro index
    apply Integrable.of_bound
      ((((hadapted index).mono (piLE.le index)).aestronglyMeasurable).mul
        (hY_integrable index).aestronglyMeasurable) index
    filter_upwards [hsum_bound index, hY_bound index] with path hsum hY
    change |(∑ previous ∈ Finset.range index, Y previous path) * Y index path| ≤ index
    rw [abs_mul]
    calc
      |∑ previous ∈ Finset.range index, Y previous path| * |Y index path| ≤
          (index : ℝ) * |Y index path| :=
        mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
      _ ≤ (index : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg index)
      _ = index := by ring
  have hY_sq_int : ∀ index,
      Integrable (fun path => (Y index path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (hY_integrable index).aestronglyMeasurable zero_le_one
    exact hY_bound index
  have hY_second : ∀ index,
      (∫ path, (Y index path) ^ 2 ∂trajectory) ≤
        1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_secondMoment_le_idleFraction_at_lowerThreshold_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hcond : ∀ index, trajectory[Y index | piLE index] =ᵐ[trajectory] 0 := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers lowerThreshold index hservers
  have hcross_nonpos : ∀ index,
      (∫ path,
        (∑ previous ∈ Finset.range index, Y previous path) * Y index path ∂trajectory) ≤ 0 :=
    AppliedModelingLib.partial_sum_cross_integral_nonpos_of_condExp_eq_zero
      hadapted hcross_int hY_integrable hcond
  have hsecond := AppliedModelingLib.partial_sum_secondMoment_le_sum_of_cross_nonpos
    (Y := Y)
    (b := fun _ => 1 - (manyServerBusyFraction servers lowerThreshold : ℝ))
    hsum_sq_int hcross_int hY_sq_int hY_second hcross_nonpos n
  change
    (∫ path,
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold n path) ^ 2 ∂trajectory) ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))
  rw [← hsum_eq]
  convert hsecond using 1
  simp [Finset.sum_const, Finset.card_range]
  ring

/-- The lower-barrier-stopped correction cannot exceed the number of retained
embedded increments in absolute value. -/
theorem abs_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_le
    (servers lowerThreshold n : ℕ) (hservers : 0 < servers)
    (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
      servers lowerThreshold n path| ≤ n := by
  rw [manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_sum_before_lowerExit]
  calc
    |∑ index ∈ Finset.range n,
        manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
          servers lowerThreshold index path| ≤
        ∑ index ∈ Finset.range n,
          |manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement
            servers lowerThreshold index path| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro index hindex
          exact
            abs_manyServerMarkedStateStoppedUnrealizedPotentialServiceIncrement_le_one
              servers lowerThreshold index hservers path
    _ = n := by simp

/-- Every stopped correction value is square-integrable under an arbitrary
initial marked trajectory law. -/
theorem memLp_two_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    MemLp (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
      servers lowerThreshold n) 2 trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have hmeas : AEStronglyMeasurable
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold n)
      trajectory :=
    ((hmartingale.stronglyMeasurable n).mono (piLE.le n)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  apply AppliedModelingLib.integrable_sq_of_ae_abs_le hmeas (Nat.cast_nonneg n)
  exact Filter.Eventually.of_forall fun path =>
    abs_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_le
      servers lowerThreshold n hservers path

/-- Doob's finite-prefix estimate for the unused-service correction stopped
at the predictable lower barrier. -/
theorem ennreal_mul_measure_maximalStoppedUnrealizedPotentialServicePartialSum_le_lowerThreshold_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) (threshold : ℝ≥0) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index path) ^ 2)} ≤
      ENNReal.ofReal ((n : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers lowerThreshold hservers
  have hL2 : ∀ index : ℕ, MemLp
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold index)
      2 trajectory := by
    intro index
    simpa [trajectory, markedInitial, measureKernel] using
      memLp_two_manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_from_initial
        initial trafficIntensity servers lowerThreshold hservers index
  have hmax := AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
    hmartingale hL2 threshold n
  have hsecond : (∫ path,
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold n path) ^ 2 ∂trajectory) ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_secondMoment_le_lowerThreshold_idleFraction_from_initial
        initial trafficIntensity servers lowerThreshold hservers n
  calc
    threshold * trajectory {path | (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
              servers lowerThreshold index path) ^ 2)} ≤
        ENNReal.ofReal (∫ path,
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold n path) ^ 2 ∂trajectory) := hmax
    _ ≤ ENNReal.ofReal ((n : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) :=
      ENNReal.ofReal_le_ofReal hsecond

/-- On the event that the predictable lower barrier remains unhit through a
finite prefix, the original correction inherits the stopped-martingale Doob
bound. -/
theorem ennreal_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_and_no_lowerExit_le_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers lowerThreshold : ℕ)
    (hservers : 0 < servers) (threshold : ℝ≥0) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path |
      (n : ENat) ≤ manyServerMarkedStateArrivalPotentialLowerExitTime
        lowerThreshold path ∧
      (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index path) ^ 2)} ≤
      ENNReal.ofReal ((n : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let event : Set (ℕ → ℕ × Bool) := {path |
    (n : ENat) ≤ manyServerMarkedStateArrivalPotentialLowerExitTime
      lowerThreshold path ∧
    (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index path) ^ 2)}
  let stoppedEvent : Set (ℕ → ℕ × Bool) := {path |
    (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index path) ^ 2)}
  have hsubset : event ⊆ stoppedEvent := by
    intro path hpath
    change (n : ENat) ≤ manyServerMarkedStateArrivalPotentialLowerExitTime
      lowerThreshold path ∧
      (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index path) ^ 2) at hpath
    change (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index path) ^ 2)
    rw [← maximalCenteredUnrealizedPotentialServicePartialSum_eq_stopped_of_le_lowerExit
      servers lowerThreshold n path hpath.1]
    exact hpath.2
  have hstopped :=
    ennreal_mul_measure_maximalStoppedUnrealizedPotentialServicePartialSum_le_lowerThreshold_idleFraction_from_initial
      initial trafficIntensity servers lowerThreshold hservers threshold n
  change threshold * trajectory event ≤ _
  calc
    threshold * trajectory event ≤ threshold * trajectory stoppedEvent :=
      mul_le_mul_right (measure_mono hsubset) threshold
    _ ≤ ENNReal.ofReal ((n : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) := by
      simpa [trajectory, markedInitial, measureKernel, stoppedEvent] using hstopped

/-- The accumulated centered correction is bounded pathwise by its number of
embedded increments. -/
theorem abs_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_le
    (servers : ℕ) (hservers : 0 < servers) (n : ℕ)
    (path : ℕ → ℕ × Bool) :
    |manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
      servers n path| ≤ n := by
  unfold manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
  calc
    |∑ i ∈ Finset.range n,
        manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers i path| ≤
        ∑ i ∈ Finset.range n,
          |manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers i path| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact
            abs_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_le_one
              servers hservers i path
    _ = n := by simp

/-- Each finite centered unrealized-potential-service partial sum has a finite
second moment under the arbitrary-initial marked trajectory law. -/
theorem memLp_two_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    MemLp (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
      servers n) 2 trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmeas : AEStronglyMeasurable
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers n)
      trajectory :=
    (measurable_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
      servers n).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  apply AppliedModelingLib.integrable_sq_of_ae_abs_le hmeas (Nat.cast_nonneg n)
  exact Filter.Eventually.of_forall fun path =>
    abs_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_le
      servers hservers n path

/-- The exact finite-horizon second-moment bound for the compensated
unrealized-potential-service martingale. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) ≤ n := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Y : ℕ → (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hadapted : StronglyAdapted piLE
      (fun n path => ∑ i ∈ Finset.range n, Y i path) := by
    simpa [Y] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_stronglyAdapted
        servers
  have hY_integrable : ∀ index, Integrable (Y index) trajectory := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers hservers index
  have hY_bound : ∀ index, ∀ᵐ path ∂trajectory, |Y index path| ≤ 1 := by
    intro index
    exact Filter.Eventually.of_forall fun path =>
      abs_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_le_one
        servers hservers index path
  have hsum_bound : ∀ index, ∀ᵐ path ∂trajectory,
      |∑ i ∈ Finset.range index, Y i path| ≤ index := by
    intro index
    exact Filter.Eventually.of_forall fun path => by
      simpa [Y, manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum] using
        abs_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_le
          servers hservers index path
  have hsum_sq_int : ∀ index,
      Integrable (fun path => (∑ i ∈ Finset.range index, Y i path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (((hadapted index).mono (piLE.le index)).aestronglyMeasurable)
      (Nat.cast_nonneg index)
    exact hsum_bound index
  have hcross_int : ∀ index,
      Integrable (fun path =>
        (∑ i ∈ Finset.range index, Y i path) * Y index path) trajectory := by
    intro index
    apply Integrable.of_bound
      ((((hadapted index).mono (piLE.le index)).aestronglyMeasurable).mul
        (hY_integrable index).aestronglyMeasurable) index
    filter_upwards [hsum_bound index, hY_bound index] with path hsum hY
    change |(∑ i ∈ Finset.range index, Y i path) * Y index path| ≤ index
    rw [abs_mul]
    calc
      |∑ i ∈ Finset.range index, Y i path| * |Y index path| ≤
          (index : ℝ) * |Y index path| :=
        mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
      _ ≤ (index : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg index)
      _ = index := by ring
  have hY_sq_int : ∀ index,
      Integrable (fun path => (Y index path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (hY_integrable index).aestronglyMeasurable zero_le_one
    exact hY_bound index
  have hY_second : ∀ index,
      (∫ path, (Y index path) ^ 2 ∂trajectory) ≤ 1 := by
    intro index
    simpa using AppliedModelingLib.integral_sq_le_sq_of_ae_abs_le
      (hY_sq_int index) zero_le_one (hY_bound index)
  have hcond : ∀ index, trajectory[Y index | piLE index] =ᵐ[trajectory] 0 := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers index
  have hcross_nonpos : ∀ index,
      (∫ path,
        (∑ i ∈ Finset.range index, Y i path) * Y index path ∂trajectory) ≤ 0 :=
    AppliedModelingLib.partial_sum_cross_integral_nonpos_of_condExp_eq_zero
      hadapted hcross_int hY_integrable hcond
  have hsecond := AppliedModelingLib.partial_sum_secondMoment_le_sum_of_cross_nonpos
    (Y := Y) (b := fun _ => (1 : ℝ)) hsum_sq_int hcross_int hY_sq_int hY_second
      hcross_nonpos n
  simpa [Y, manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum] using
    hsecond

/-- The embedded centered potential-service correction has second moment
equal to the sum of its predictable Bernoulli variances.  This is the exact
finite-prefix quadratic-variation identity, prior to any scaling or limiting
argument. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_eq_sum_expectedVariance_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) =
      ∑ index ∈ Finset.range n, ∫ path,
        (if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
        (1 - (if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ))) ∂trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let Y : ℕ → (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement servers
  let variance : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
    (1 - (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)))
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hadapted : StronglyAdapted piLE
      (fun index path => ∑ i ∈ Finset.range index, Y i path) := by
    simpa [Y] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_stronglyAdapted
        servers
  have hY_integrable : ∀ index, Integrable (Y index) trajectory := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      integrable_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_from_initial
        initial trafficIntensity servers hservers index
  have hY_bound : ∀ index, ∀ᵐ path ∂trajectory, |Y index path| ≤ 1 := by
    intro index
    exact Filter.Eventually.of_forall fun path =>
      abs_manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_le_one
        servers hservers index path
  have hsum_bound : ∀ index, ∀ᵐ path ∂trajectory,
      |∑ i ∈ Finset.range index, Y i path| ≤ index := by
    intro index
    exact Filter.Eventually.of_forall fun path => by
      simpa [Y, manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum] using
        abs_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_le
          servers hservers index path
  have hsum_sq_int : ∀ index,
      Integrable (fun path => (∑ i ∈ Finset.range index, Y i path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (((hadapted index).mono (piLE.le index)).aestronglyMeasurable)
      (Nat.cast_nonneg index)
    exact hsum_bound index
  have hcross_int : ∀ index,
      Integrable (fun path =>
        (∑ i ∈ Finset.range index, Y i path) * Y index path) trajectory := by
    intro index
    apply Integrable.of_bound
      ((((hadapted index).mono (piLE.le index)).aestronglyMeasurable).mul
        (hY_integrable index).aestronglyMeasurable) index
    filter_upwards [hsum_bound index, hY_bound index] with path hsum hY
    change |(∑ i ∈ Finset.range index, Y i path) * Y index path| ≤ index
    rw [abs_mul]
    calc
      |∑ i ∈ Finset.range index, Y i path| * |Y index path| ≤
          (index : ℝ) * |Y index path| :=
        mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
      _ ≤ (index : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg index)
      _ = index := by ring
  have hY_sq_int : ∀ index,
      Integrable (fun path => (Y index path) ^ 2) trajectory := by
    intro index
    apply AppliedModelingLib.integrable_sq_of_ae_abs_le
      (hY_integrable index).aestronglyMeasurable zero_le_one
    exact hY_bound index
  have hcond_zero : ∀ index, trajectory[Y index | piLE index] =ᵐ[trajectory] 0 := by
    intro index
    simpa [Y, trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_condExp_eq_zero_from_initial
        initial trafficIntensity servers hservers index
  have hcross_zero : ∀ index,
      (∫ path, (∑ i ∈ Finset.range index, Y i path) * Y index path ∂trajectory) = 0 :=
    AppliedModelingLib.partial_sum_cross_integral_eq_zero_of_condExp_eq_zero
      hadapted hcross_int hY_integrable hcond_zero
  have hY_second : ∀ index,
      (∫ path, (Y index path) ^ 2 ∂trajectory) = ∫ path, variance index path ∂trajectory := by
    intro index
    have hvariance_condExp :
        trajectory[(fun path => (Y index path) ^ 2) | piLE index] =ᵐ[trajectory]
          variance index := by
      simpa [Y, variance, trajectory, markedInitial, measureKernel] using
        manyServerMarkedStateCenteredUnrealizedPotentialServiceIncrement_sq_condExp_from_initial
          initial trafficIntensity servers hservers index
    calc
      (∫ path, (Y index path) ^ 2 ∂trajectory) =
          ∫ path, trajectory[(fun path => (Y index path) ^ 2) | piLE index] path ∂trajectory := by
            exact (integral_condExp (μ := trajectory) (m := piLE index)
              (piLE.le index) (f := fun path => (Y index path) ^ 2)).symm
      _ = ∫ path, variance index path ∂trajectory :=
        integral_congr_ae hvariance_condExp
  have hsecond := AppliedModelingLib.partial_sum_secondMoment_eq_sum_of_cross_zero
    hsum_sq_int hcross_int hY_sq_int hY_second hcross_zero n
  simpa [Y, variance, manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum] using
    hsecond

/-- The finite-prefix correction variance is bounded by the expected
potential-event idle occupation.  This retains the state-dependent factor
that is lost in the coarse `E[M_n^2] ≤ n` estimate. -/
theorem manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_le_sum_expectedIdleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) ≤
      ∑ index ∈ Finset.range n, ∫ path,
        if (path index).2 then 0 else
          1 - (manyServerBusyFraction servers (path index).1 : ℝ) ∂trajectory := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let variance : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)) *
    (1 - (if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)))
  let idle : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have heq : (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) =
      ∑ index ∈ Finset.range n, ∫ path, variance index path ∂trajectory := by
    simpa [trajectory, markedInitial, measureKernel, variance] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_eq_sum_expectedVariance_from_initial
        initial trafficIntensity servers hservers n
  change (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) ≤
      ∑ index ∈ Finset.range n, ∫ path, idle index path ∂trajectory
  rw [heq]
  apply Finset.sum_le_sum
  intro index _
  have hbusy_bounds : ∀ path : ℕ → ℕ × Bool,
      0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) ∧
      (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
    intro path
    constructor
    · positivity
    · exact_mod_cast manyServerBusyFraction_le_one servers (path index).1 hservers
  have hidle_bounds : ∀ path, 0 ≤ idle index path ∧ idle index path ≤ 1 := by
    intro path
    dsimp [idle]
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        constructor <;> linarith [(hbusy_bounds path).1, (hbusy_bounds path).2]
    | true => simp
  have hidle_meas : Measurable (idle index) := by
    dsimp [idle]
    exact (measurable_of_countable (fun current : ℕ × Bool =>
      if current.2 then 0 else
        1 - (manyServerBusyFraction servers current.1 : ℝ))).comp
      (measurable_pi_apply index)
  have hidle_int : Integrable (idle index) trajectory := by
    apply Integrable.of_bound hidle_meas.aestronglyMeasurable 1
    filter_upwards [] with path
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hidle_bounds path).1] using
      (hidle_bounds path).2
  have hvariance_meas : Measurable (variance index) := by
    dsimp [variance]
    exact (measurable_of_countable (fun current : ℕ × Bool =>
      (if current.2 then 0 else
        1 - (manyServerBusyFraction servers current.1 : ℝ)) *
      (1 - (if current.2 then 0 else
        1 - (manyServerBusyFraction servers current.1 : ℝ))))).comp
      (measurable_pi_apply index)
  have hvariance_int : Integrable (variance index) trajectory := by
    apply Integrable.of_bound hvariance_meas.aestronglyMeasurable 1
    filter_upwards [] with path
    have hle : variance index path ≤ 1 := by
      dsimp [variance]
      cases hmark : (path index).2 with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          nlinarith [(hbusy_bounds path).1, (hbusy_bounds path).2]
      | true => simp
    have hnonneg : 0 ≤ variance index path := by
      dsimp [variance]
      cases hmark : (path index).2 with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          nlinarith [(hbusy_bounds path).1, (hbusy_bounds path).2]
      | true => simp
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  apply integral_mono_ae hvariance_int hidle_int
  filter_upwards [] with path
  dsimp [variance, idle]
  cases hmark : (path index).2 with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      nlinarith [(hbusy_bounds path).1, (hbusy_bounds path).2]
  | true => simp

/-- A finite-horizon Doob estimate for the centered unrealized-potential-
service martingale.  The event is the maximum squared embedded correction over
the first `n` potential events. -/
theorem ennreal_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (threshold : ℝ≥0) (n : ℕ) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index path) ^ 2)} ≤ ENNReal.ofReal n := by
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  letI : IsProbabilityMeasure markedInitial.toMeasure := by infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers hservers
  have hL2 : ∀ index : ℕ, MemLp
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers index)
      2 trajectory := by
    intro index
    simpa [trajectory, markedInitial, measureKernel] using
      memLp_two_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_from_initial
        initial trafficIntensity servers hservers index
  have hmax := AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
    hmartingale hL2 threshold n
  have hsecond : (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) ≤ n := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_le_from_initial
        initial trafficIntensity servers hservers n
  calc
    threshold * trajectory {path | (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index path) ^ 2)} ≤
        ENNReal.ofReal (∫ path,
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers n path) ^ 2 ∂trajectory) := hmax
    _ ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal hsecond

/-- The embedded queue-conservation identity holds along every finite prefix
of an arbitrary-initial marked trajectory, on one common full-measure event. -/
theorem ae_manyServerMarkedStateTrajectory_queue_balance_prefix_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (steps : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers),
      (path steps).1 + manyServerMarkedStateDeparturePrefix path steps =
        (path 0).1 + manyServerMarkedStateArrivalPrefix path steps := by
  filter_upwards [ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
    initial trafficIntensity servers hservers] with path hpath
  exact manyServerMarkedState_queue_balance_prefix path hpath steps

/-- On the common marked-trajectory event, every finite embedded prefix
satisfies the exact queue conservation identity. -/
theorem ae_stationaryManyServerMarkedStateTrajectory_queue_balance_prefix
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial)
    (steps : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers),
      (path steps).1 + manyServerMarkedStateDeparturePrefix path steps =
        (path 0).1 + manyServerMarkedStateArrivalPrefix path steps := by
  filter_upwards [ae_all_stationaryManyServerMarkedStateTrajectory_stepAllowed
    trafficIntensity servers hservers hstationary] with path hpath
  exact manyServerMarkedState_queue_balance_prefix path hpath steps

/-- The pair of current/next marks under the product of an augmented initial
law and its marked transition kernel has the explicit current/next mark PMF. -/
theorem map_manyServerCurrentNextArrivalMarks_compProd
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    Measure.map (fun statePair : (ℕ × Bool) × (ℕ × Bool) =>
      (statePair.1.2, statePair.2.2))
      ((manyServerMarkedStatePMF initial trafficIntensity).toMeasure ⊗ₘ
        manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers) =
      (manyServerCurrentNextArrivalMarkPMF
        initial trafficIntensity servers hservers).toMeasure := by
  let markPair : (ℕ × Bool) × (ℕ × Bool) → Bool × Bool :=
    fun statePair => (statePair.1.2, statePair.2.2)
  let markedInitial := manyServerMarkedStatePMF initial trafficIntensity
  let markedKernel := manyServerMarkedStateUniformizationKernel
    trafficIntensity servers hservers
  calc
    Measure.map markPair (markedInitial.toMeasure ⊗ₘ countablePMFKernel markedKernel) =
        Measure.map markPair
          (CountableMarkovKernel.initialTransitionPairPMF
            markedInitial markedKernel).toMeasure := by
              rw [CountableMarkovKernel.initialTransitionPairPMF_toMeasure_eq_compProd]
    _ = ((CountableMarkovKernel.initialTransitionPairPMF
          markedInitial markedKernel).map markPair).toMeasure := by
            exact PMF.toMeasure_map markPair
              (CountableMarkovKernel.initialTransitionPairPMF markedInitial markedKernel)
              (measurable_of_countable _)
    _ = (manyServerCurrentNextArrivalMarkPMF
          initial trafficIntensity servers hservers).toMeasure := by
            rw [manyServerCurrentNextArrivalMarkPMF_eq_initialTransitionPair_map]

/-- Two consecutive marks in the stationary augmented many-server trajectory
have the independent Bernoulli product law. -/
theorem stationaryManyServerMarkedStateTrajectory_consecutiveArrivalMarks_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial)
    (index : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool => ((path index).2, (path (index + 1)).2))
      (AppliedModelingLib.pmfProd (manyServerUniformizationArrivalMark trafficIntensity)
        (manyServerUniformizationArrivalMark trafficIntensity)).toMeasure
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  let markedInitial := manyServerMarkedStatePMF initial trafficIntensity
  let markedKernel := manyServerMarkedStateUniformizationMeasureKernel
    trafficIntensity servers hservers
  let pair : (ℕ → ℕ × Bool) → (ℕ × Bool) × (ℕ × Bool) :=
    fun path => (path index, path (index + 1))
  let markPair : (ℕ × Bool) × (ℕ × Bool) → Bool × Bool :=
    fun statePair => (statePair.1.2, statePair.2.2)
  have hpair : Measurable pair :=
    (measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))
  have hmarkPair : Measurable markPair := measurable_of_countable _
  refine ⟨(hmarkPair.comp hpair).aemeasurable, ?_⟩
  change Measure.map (fun path : ℕ → ℕ × Bool => ((path index).2, (path (index + 1)).2))
    (stationaryTrajMeasure markedInitial.toMeasure markedKernel) = _
  calc
    Measure.map (fun path : ℕ → ℕ × Bool => ((path index).2, (path (index + 1)).2))
        (stationaryTrajMeasure markedInitial.toMeasure markedKernel) =
        Measure.map markPair (Measure.map pair
          (stationaryTrajMeasure markedInitial.toMeasure markedKernel)) := by
            symm
            rw [Measure.map_map hmarkPair hpair]
            rfl
    _ = Measure.map markPair (markedInitial.toMeasure ⊗ₘ markedKernel) := by
          rw [stationaryTrajMeasure_consecutivePair
            (manyServerMarkedStatePMF_kernelInvariant
              trafficIntensity servers hservers hstationary) index]
    _ = (manyServerCurrentNextArrivalMarkPMF
          initial trafficIntensity servers hservers).toMeasure := by
          exact map_manyServerCurrentNextArrivalMarks_compProd
            initial trafficIntensity servers hservers
    _ = (AppliedModelingLib.pmfProd (manyServerUniformizationArrivalMark trafficIntensity)
          (manyServerUniformizationArrivalMark trafficIntensity)).toMeasure := by
          rw [manyServerCurrentNextArrivalMarkPMF_eq_pmfProd]

private theorem manyServer_pmf_map_pair_apply {α β : Type*} (law : PMF β)
    (first : α) (second : β) :
    (law.map (fun value => (first, value))) (first, second) = law second := by
  classical
  rw [PMF.map_apply, tsum_eq_single second]
  · simp
  · intro other hother
    split_ifs with h
    · exact (hother (congrArg Prod.snd h).symm).elim
    · rfl

private theorem manyServer_pmf_map_pair_apply_of_ne {α β : Type*} (law : PMF β)
    {first otherFirst : α} (hfirst : otherFirst ≠ first) (second : β) :
    (law.map (fun value => (first, value))) (otherFirst, second) = 0 := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro value
  simp [hfirst]

private theorem manyServerMarkedStatePMF_apply
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (state : ℕ) (arrival : Bool) :
    manyServerMarkedStatePMF initial trafficIntensity (state, arrival) =
      initial state * manyServerUniformizationArrivalMark trafficIntensity arrival := by
  unfold manyServerMarkedStatePMF
  rw [PMF.bind_apply, tsum_eq_single state]
  · rw [manyServer_pmf_map_pair_apply]
  · intro other hother
    rw [manyServer_pmf_map_pair_apply_of_ne
      (manyServerUniformizationArrivalMark trafficIntensity) (Ne.symm hother) arrival]
    simp

/-- The literal invariant marked-state PMF is the product of its queue-state
PMF and the current Bernoulli potential-event mark PMF. -/
theorem manyServerMarkedStatePMF_toMeasure_eq_prod
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) :
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure =
      initial.toMeasure.prod
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨state, arrival⟩
  rw [PMF.toMeasure_apply_singleton
      (manyServerMarkedStatePMF initial trafficIntensity) (state, arrival)
      (measurableSet_singleton _),
    manyServerMarkedStatePMF_apply, ← Set.singleton_prod_singleton,
    Measure.prod_prod,
    initial.toMeasure_apply_singleton state (measurableSet_singleton _),
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure_apply_singleton arrival
      (measurableSet_singleton _)]

/-- Under the product stationary marked-state law, the mean idle fraction at
one potential-event epoch factors into the service-mark probability and the
stationary queue-state idle fraction. -/
theorem integral_manyServerStationaryMarkedState_idleFraction
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    (∫ current : ℕ × Bool,
      if current.2 then 0 else 1 - (manyServerBusyFraction servers current.1 : ℝ) ∂
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).toMeasure.prod
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure) =
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ)) := by
  let stationary : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let mark : PMF Bool := manyServerUniformizationArrivalMark trafficIntensity
  let idle : ℕ → ℝ := fun state => 1 - (manyServerBusyFraction servers state : ℝ)
  let reward : ℕ × Bool → ℝ := fun current =>
    if current.2 then 0 else idle current.1
  letI : IsProbabilityMeasure stationary.toMeasure := by
    dsimp [stationary]
    infer_instance
  letI : IsProbabilityMeasure mark.toMeasure := by
    dsimp [mark]
    infer_instance
  have hmeas : Measurable reward := measurable_of_countable _
  have hint : Integrable reward (stationary.toMeasure.prod mark.toMeasure) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with current
    cases hmark : current.2 with
    | true => simp [reward, hmark]
    | false =>
        have hbusy_nonneg : 0 ≤ (manyServerBusyFraction servers current.1 : ℝ) := by
          positivity
        have hbusy_le : (manyServerBusyFraction servers current.1 : ℝ) ≤ 1 := by
          exact_mod_cast manyServerBusyFraction_le_one servers current.1 hservers
        rw [show reward current = 1 - (manyServerBusyFraction servers current.1 : ℝ) by
          simp [reward, idle, hmark], Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
  calc
    (∫ current : ℕ × Bool, reward current ∂stationary.toMeasure.prod mark.toMeasure) =
        ∫ state : ℕ, ∫ arrival : Bool, reward (state, arrival) ∂mark.toMeasure ∂stationary.toMeasure := by
          exact MeasureTheory.integral_prod
            (Function.uncurry (fun state arrival => reward (state, arrival))) hint
    _ = ∫ state : ℕ,
          ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            idle state ∂stationary.toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with state
          simpa [reward, mark, idle] using
            integral_manyServerUniformizationArrivalMark_serviceOnly trafficIntensity (idle state)
    _ = ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ)) := by
          rw [MeasureTheory.integral_const_mul,
            integral_manyServerStationary_idleFraction servers hservers
              (by exact_mod_cast htraffic_pos) (by exact_mod_cast htraffic_lt_one)]


/-- At every embedded index, a stationary marked many-server trajectory has
the literal product law of its queue state and its current event mark. -/
theorem stationaryManyServerMarkedStateTrajectory_stateMark_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial)
    (index : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool => path index)
      (initial.toMeasure.prod
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure)
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  refine ⟨(measurable_pi_apply index).aemeasurable, ?_⟩
  rw [stationaryTrajMeasure_marginal
    (manyServerMarkedStatePMF_kernelInvariant
      trafficIntensity servers hservers hstationary) index,
    manyServerMarkedStatePMF_toMeasure_eq_prod]

/-- At every embedded epoch of the stable stationary marked trajectory, the
mean unrealized-potential-service probability is the potential-event share
times the spare-capacity fraction. -/
theorem integral_stationaryManyServerMarkedStateTrajectory_idleFraction
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (index : ℕ) :
    (∫ path,
      if (path index).2 then 0 else
        1 - (manyServerBusyFraction servers (path index).1 : ℝ) ∂
      stationaryTrajMeasure
        (manyServerMarkedStatePMF
          (manyServerStationaryPMF (trafficIntensity : ℝ) servers
            (by positivity) (by exact_mod_cast htraffic_lt_one)) trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) =
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ)) := by
  let initial : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let trajectory := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel trafficIntensity servers hservers)
  let reward : (ℕ → ℕ × Bool) → ℝ := fun path =>
    if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)
  let rewardState : ℕ × Bool → ℝ := fun current =>
    if current.2 then 0 else 1 - (manyServerBusyFraction servers current.1 : ℝ)
  have hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial := by
    dsimp [initial]
    exact manyServerStationaryPMF_uniformized_stationary
      trafficIntensity servers hservers htraffic_lt_one
  have hlaw := stationaryManyServerMarkedStateTrajectory_stateMark_hasLaw
    (initial := initial) trafficIntensity servers hservers hstationary index
  have hreward_meas : Measurable rewardState := measurable_of_countable _
  calc
    (∫ path, reward path ∂trajectory) =
        ∫ current, rewardState current ∂Measure.map (fun path => path index) trajectory := by
          change (∫ path, rewardState (path index) ∂trajectory) = _
          symm
          exact MeasureTheory.integral_map hlaw.aemeasurable hreward_meas.aestronglyMeasurable
    _ = ∫ current, rewardState current ∂
          initial.toMeasure.prod (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
          rw [hlaw.map_eq]
    _ = ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ)) := by
          simpa [rewardState, initial] using
            integral_manyServerStationaryMarkedState_idleFraction
              trafficIntensity servers hservers htraffic_pos htraffic_lt_one

/-- In the stationary stable many-server chain, Doob's finite-prefix maximal
inequality retains the exact spare-capacity factor in the predictable variance.
This is an embedded-time estimate; coupling it to a physical-time Poisson clock
is a separate step. -/
theorem ennreal_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_stationary_le
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (threshold : ℝ≥0) (n : ℕ) :
    let initial := manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one)
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    threshold * trajectory {path | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index path) ^ 2)} ≤
      ENNReal.ofReal ((n : ℝ) *
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ))) := by
  dsimp only
  let initial : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let markedInitial : PMF (ℕ × Bool) :=
    manyServerMarkedStatePMF initial trafficIntensity
  let measureKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial.toMeasure measureKernel
  let idle : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)
  let gap : ℝ :=
    ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
      (1 - (trafficIntensity : ℝ))
  letI : IsProbabilityMeasure markedInitial.toMeasure := by
    dsimp [markedInitial]
    infer_instance
  letI : IsMarkovKernel measureKernel := by
    dsimp [measureKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  have hmartingale : Martingale
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers)
      piLE trajectory := by
    simpa [trajectory, markedInitial, measureKernel] using
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_martingale_from_initial
        initial trafficIntensity servers hservers
  have hL2 : ∀ index : ℕ, MemLp
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum servers index)
      2 trajectory := by
    intro index
    simpa [trajectory, markedInitial, measureKernel] using
      memLp_two_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_from_initial
        initial trafficIntensity servers hservers index
  have hmax := AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
    hmartingale hL2 threshold n
  have hsecond : (∫ path,
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers n path) ^ 2 ∂trajectory) ≤ n * gap := by
    have hidle : ∀ index : ℕ, (∫ path, idle index path ∂trajectory) = gap := by
      intro index
      simpa [trajectory, markedInitial, measureKernel, idle, gap] using
        integral_stationaryManyServerMarkedStateTrajectory_idleFraction
          trafficIntensity servers hservers htraffic_pos htraffic_lt_one index
    calc
      (∫ path,
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers n path) ^ 2 ∂trajectory) ≤
          ∑ index ∈ Finset.range n, ∫ path, idle index path ∂trajectory := by
        simpa [trajectory, markedInitial, measureKernel, idle] using
          manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_le_sum_expectedIdleFraction_from_initial
            initial trafficIntensity servers hservers n
      _ = n * gap := by
        simp_rw [hidle]
        simp
  calc
    threshold * trajectory {path | (threshold : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index path) ^ 2)} ≤
        ENNReal.ofReal (∫ path,
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers n path) ^ 2 ∂trajectory) := hmax
    _ ≤ ENNReal.ofReal ((n : ℝ) * gap) := ENNReal.ofReal_le_ofReal hsecond
    _ = ENNReal.ofReal ((n : ℝ) *
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ))) := by
      congr 1
      dsimp [gap]
      ring

/-- The real-probability form of the stationary embedded maximal estimate.
It is convenient when this embedded-time control is combined with a
continuous-time clock tail bound. -/
theorem real_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_stationary_le
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (threshold : ℝ≥0) (n : ℕ) :
    let initial := manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one)
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    (threshold : ℝ) * trajectory.real {path | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index path) ^ 2)} ≤
      (n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ)) := by
  dsimp only
  let initial : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let event : Set (ℕ → ℕ × Bool) := {path | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index path) ^ 2)}
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hbase := ennreal_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_stationary_le
    trafficIntensity servers hservers htraffic_pos htraffic_lt_one threshold n
  change (threshold : ℝ) * trajectory.real event ≤ _
  change (threshold : ℝ) * (trajectory event).toReal ≤ _
  calc
    (threshold : ℝ) * (trajectory event).toReal =
        ((threshold : ℝ≥0∞) * trajectory event).toReal := by
          simp [ENNReal.toReal_mul]
    _ ≤ (ENNReal.ofReal ((n : ℝ) *
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ)))).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.ofReal_ne_top
      · simpa [initial, trajectory, event] using hbase
    _ = (n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ)) := by
      rw [ENNReal.toReal_ofReal]
      apply mul_nonneg
      · exact mul_nonneg (Nat.cast_nonneg n) (by positivity)
      · exact sub_nonneg.mpr (by exact_mod_cast htraffic_lt_one.le)

/-- The finite embedded maximum used in the stationary Doob estimate is a
measurable random variable. -/
theorem measurable_maximalCenteredUnrealizedPotentialServicePartialSum
    (servers n : ℕ) :
    Measurable (fun path : ℕ → ℕ × Bool =>
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index path) ^ 2)) := by
  induction n with
  | zero =>
      simpa using
        (measurable_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers 0).pow measurable_const
  | succ n ih =>
      simpa [Finset.range_add_one, Finset.sup'_insert] using
        ((measurable_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers (n + 1)).pow measurable_const).max ih

/-- In the stable regime, the canonical many-server stationary PMF together
with the potential-event mark is invariant for the augmented embedded chain. -/
theorem manyServerStationaryPMF_markedState_stationary
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    PMFStationary
      (manyServerMarkedStateUniformizationKernel trafficIntensity servers hservers)
      (manyServerMarkedStatePMF
        (manyServerStationaryPMF (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)) trafficIntensity) := by
  apply manyServerMarkedStatePMF_stationary
  exact manyServerStationaryPMF_uniformized_stationary
    trafficIntensity servers hservers htraffic_lt_one

end

end AppliedModelingLib.Probability.Queueing
