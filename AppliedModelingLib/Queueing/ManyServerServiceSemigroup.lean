import AppliedModelingLib.Queueing.ManyServerMarkedUniformization
import AppliedModelingLib.Queueing.MM1.Kernel
import AppliedModelingLib.Queueing.RandomDurationKernel
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Arrival-free many-server service semigroup

This module specializes the many-server potential-event uniformization to zero
arrival intensity and Poissonizes it at the aggregate service-clock rate.  The
result is the continuous-time queue-length semigroup during an interval in
which no arrivals occur: at state `q`, departures occur at rate
`μ min(q, n)`.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The zero-arrival potential-event kernel for `servers` identical
exponential-service clocks. -/
noncomputable def manyServerServiceOnlyKernel (servers : ℕ) (hservers : 0 < servers) :
    CountableMarkovKernel ℕ :=
  manyServerUniformizedKernel 0 servers hservers

/-- The continuous-time queue-length transition during an arrival-free
interval. Potential service clocks run at aggregate rate `servers * μ`; a
clock changes the state precisely when its server is busy. -/
noncomputable def manyServerServiceOnlyTransition
    (servers : ℕ) (hservers : 0 < servers) (serviceRate : ℝ)
    (hserviceRate_nonneg : 0 ≤ serviceRate) (time : ℝ≥0) : Kernel ℕ ℕ :=
  CountableMarkovKernel.poissonizedKernelAtRate
    (manyServerServiceOnlyKernel servers hservers)
    ((servers : ℝ) * serviceRate)
    (mul_nonneg (Nat.cast_nonneg servers) hserviceRate_nonneg) time

/-- With no arrivals, state zero is absorbing for the potential-event chain. -/
lemma manyServerServiceOnlyKernel_apply_zero
    (servers : ℕ) (hservers : 0 < servers) (state : ℕ) :
    manyServerServiceOnlyKernel servers hservers 0 state =
      if state = 0 then 1 else 0 := by
  rw [manyServerServiceOnlyKernel, manyServerUniformizedKernel_apply_zero]
  by_cases hzero : state = 0
  · subst state
    simp [uniformizedBirthProbability]
  by_cases hone : state = 1
  · subst state
    simp [uniformizedBirthProbability]
  · simp [hzero, hone]

/-- Away from zero, an arrival-free potential service event either removes one
busy customer or leaves the queue length unchanged. -/
lemma manyServerServiceOnlyKernel_apply_succ
    (servers n : ℕ) (hservers : 0 < servers) (state : ℕ) :
    manyServerServiceOnlyKernel servers hservers (n + 1) state =
      if state = n then (manyServerBusyFraction servers (n + 1) : ℝ≥0∞) else
      if state = n + 1 then (1 - manyServerBusyFraction servers (n + 1) : ℝ≥0) else 0 := by
  rw [manyServerServiceOnlyKernel, manyServerUniformizedKernel_apply_succ]
  by_cases hdown : state = n
  · subst state
    simp [uniformizedBirthProbability]
  by_cases hstay : state = n + 1
  · subst state
    simp [uniformizedBirthProbability]
  by_cases hup : state = n + 2
  · subst state
    simp [uniformizedBirthProbability]
  · simp [hdown, hstay, hup]

/-- If every server is busy, one potential service-clock event removes one
customer with probability one. -/
lemma manyServerServiceOnlyKernel_eq_pure_sub_one
    (servers state : ℕ) (hservers : 0 < servers) (hstate : servers ≤ state) :
    manyServerServiceOnlyKernel servers hservers state = PMF.pure (state - 1) := by
  cases state with
  | zero => omega
  | succ predecessor =>
      have hbusy : manyServerBusyFraction servers (predecessor + 1) = 1 := by
        unfold manyServerBusyFraction
        simp only [Nat.min_eq_right (by simpa using hstate)]
        exact div_self (by exact_mod_cast Nat.ne_of_gt hservers)
      ext next
      rw [manyServerServiceOnlyKernel_apply_succ servers predecessor hservers, hbusy]
      simp

/-- If enough customers are initially waiting to keep all servers busy for a
given number of potential service-clock events, the finite-step service-only
transition is exactly the deterministic downward translation. -/
theorem manyServerServiceOnlyKernel_iterate_eq_pure_sub
    (servers state steps : ℕ) (hservers : 0 < servers)
    (hstate : servers + steps ≤ state) :
    CountableMarkovKernel.iterate (manyServerServiceOnlyKernel servers hservers) steps state =
      PMF.pure (state - steps) := by
  induction steps generalizing state with
  | zero => simp [CountableMarkovKernel.iterate]
  | succ steps ih =>
      rw [CountableMarkovKernel.iterate_succ]
      change (manyServerServiceOnlyKernel servers hservers state).bind
        (CountableMarkovKernel.iterate (manyServerServiceOnlyKernel servers hservers) steps) = _
      have hstateHigh : servers ≤ state := by omega
      rw [manyServerServiceOnlyKernel_eq_pure_sub_one servers state hservers hstateHigh,
        PMF.pure_bind]
      have hnext : servers + steps ≤ state - 1 := by omega
      rw [ih (state - 1) hnext]
      congr 1
      omega

/-- If the initial queue keeps all servers busy throughout a fixed number of
potential service-clock events, retaining that event count gives the exact
joint deterministic transition.  This distinguishes the sampled potential
clock count from the number of completed services outside the stated
high-occupancy regime. -/
theorem manyServerServiceOnlyKernel_iterateWithCount_eq_dirac
    (servers state steps : ℕ) (hservers : 0 < servers)
    (hstate : servers + steps ≤ state) :
    countableIterateTransitionWithCountKernel
      (manyServerServiceOnlyKernel servers hservers) (steps, state) =
      Measure.dirac (steps, state - steps) := by
  rw [countableIterateTransitionWithCountKernel_apply,
    manyServerServiceOnlyKernel_iterate_eq_pure_sub servers state steps hservers hstate,
    PMF.toMeasure_pure, Measure.dirac_prod_dirac]

/-- A single potential service-clock event cannot increase the queue and can
remove at most one customer. -/
theorem manyServerServiceOnlyKernel_support_bounds
    (servers state next : ℕ) (hservers : 0 < servers)
    (hnext : next ∈ (manyServerServiceOnlyKernel servers hservers state).support) :
    state - 1 ≤ next ∧ next ≤ state := by
  rw [PMF.mem_support_iff] at hnext
  cases state with
  | zero =>
      rw [manyServerServiceOnlyKernel_apply_zero] at hnext
      by_cases hzero : next = 0
      · subst next
        omega
      · simp [hzero] at hnext
  | succ predecessor =>
      rw [manyServerServiceOnlyKernel_apply_succ] at hnext
      by_cases hdown : next = predecessor
      · subst next
        omega
      by_cases hstay : next = predecessor + 1
      · subst next
        omega
      simp [hdown, hstay] at hnext

/-- After any fixed number of potential service-clock events, the service-only
queue has neither gained customers nor lost more customers than the event
count. -/
theorem manyServerServiceOnlyKernel_iterate_support_bounds
    (servers state steps next : ℕ) (hservers : 0 < servers)
    (hnext : next ∈
      (CountableMarkovKernel.iterate (manyServerServiceOnlyKernel servers hservers) steps state).support) :
    state - steps ≤ next ∧ next ≤ state := by
  induction steps generalizing state with
  | zero =>
      have hstate : next = state := by
        simpa [CountableMarkovKernel.iterate] using hnext
      subst next
      omega
  | succ steps ih =>
      rw [CountableMarkovKernel.iterate_succ] at hnext
      rw [PMF.mem_support_bind_iff] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      obtain ⟨hlower, hupper⟩ :=
        manyServerServiceOnlyKernel_support_bounds servers state middle hservers hmiddle
      obtain ⟨hlower', hupper'⟩ := ih middle hnext
      constructor <;> omega

/-- Once enough potential service-clock events have occurred to reach the
server count, an arrival-free service-only trajectory cannot finish above that
count. -/
theorem manyServerServiceOnlyKernel_iterate_support_le_servers_of_sub_le
    (servers state steps next : ℕ) (hservers : 0 < servers)
    (hsteps : state - servers ≤ steps)
    (hnext : next ∈
      (CountableMarkovKernel.iterate (manyServerServiceOnlyKernel servers hservers)
        steps state).support) :
    next ≤ servers := by
  by_cases hstate : state ≤ servers
  · exact (manyServerServiceOnlyKernel_iterate_support_bounds
      servers state steps next hservers hnext).2.trans hstate
  · have hserversState : servers ≤ state := by omega
    let initialSteps := state - servers
    let remaining := steps - initialSteps
    have hdecomp : steps = initialSteps + remaining := by
      dsimp [initialSteps, remaining]
      omega
    have hprefix : CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) initialSteps state =
        PMF.pure servers := by
      rw [manyServerServiceOnlyKernel_iterate_eq_pure_sub servers state initialSteps hservers]
      · congr 1
        dsimp [initialSteps]
        omega
      · dsimp [initialSteps]
        omega
    rw [hdecomp, CountableMarkovKernel.iterate_add_apply, hprefix, PMF.pure_bind] at hnext
    exact (manyServerServiceOnlyKernel_iterate_support_bounds
      servers servers remaining next hservers hnext).2

/-- The number of completed services recovered from the endpoints of a
finite arrival-free potential-service prefix. -/
def manyServerServiceOnlyCompletedServiceCount (state next : ℕ) : ℕ :=
  state - next

/-- The potential service opportunities in a finite arrival-free prefix that
did not become completed services.  This is a generic pathwise accounting
quantity, independent of any particular arrival model. -/
def manyServerServiceOnlyUnrealizedPotentialService
    (state steps next : ℕ) : ℕ :=
  steps - manyServerServiceOnlyCompletedServiceCount state next

/-- The arrival-free row is the busy-server Bernoulli trial, with the queue
decreased exactly when that trial succeeds. -/
theorem manyServerServiceOnlyKernel_eq_busyBernoulli_map
    (servers state : ℕ) (hservers : 0 < servers) :
    manyServerServiceOnlyKernel servers hservers state =
      (PMF.bernoulli (manyServerBusyFraction servers state)
        (manyServerBusyFraction_le_one servers state hservers)).map
        (fun service => if service then state - 1 else state) := by
  rw [manyServerServiceOnlyKernel,
    manyServerUniformizedKernel_eq_arrivalMark_bind 0 servers hservers state,
    manyServerUniformizationArrivalMark_zero, PMF.pure_bind]
  rfl

/-- The zero-arrival many-server transition is precisely the conditional
state update associated with a retained potential-service mark. -/
theorem manyServerServiceOnlyKernel_eq_stateUpdate_false
    (servers state : ℕ) (hservers : 0 < servers) :
    manyServerServiceOnlyKernel servers hservers state =
      manyServerUniformizedStateUpdate servers hservers state false := by
  rw [manyServerServiceOnlyKernel,
    manyServerUniformizedKernel_eq_arrivalMark_bind 0 servers hservers state,
    manyServerUniformizationArrivalMark_zero, PMF.pure_bind]

/-- The expected unrealized service contribution of one arrival-free
potential-service opportunity is exactly the current idle fraction. -/
theorem integral_manyServerServiceOnlyUnrealizedPotentialService_one
    (servers state : ℕ) (hservers : 0 < servers) :
    (∫ next,
      (manyServerServiceOnlyUnrealizedPotentialService state 1 next : ℝ) ∂
        (manyServerServiceOnlyKernel servers hservers state).toMeasure) =
      1 - (manyServerBusyFraction servers state : ℝ) := by
  cases state with
  | zero =>
      have hkernel : manyServerServiceOnlyKernel servers hservers 0 = PMF.pure 0 := by
        ext next
        rw [manyServerServiceOnlyKernel_apply_zero]
        simp
      rw [hkernel]
      simp [manyServerServiceOnlyUnrealizedPotentialService,
        manyServerServiceOnlyCompletedServiceCount, manyServerBusyFraction]
  | succ state =>
      rw [manyServerServiceOnlyKernel_eq_busyBernoulli_map]
      rw [← PMF.toMeasure_map
        (fun service : Bool => if service then state + 1 - 1 else state + 1)
        (PMF.bernoulli (manyServerBusyFraction servers (state + 1))
          (manyServerBusyFraction_le_one servers (state + 1) hservers))
        (measurable_of_countable _)]
      rw [integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
      have hfunction :
          (fun service : Bool =>
            (manyServerServiceOnlyUnrealizedPotentialService (state + 1) 1
              (if service then state + 1 - 1 else state + 1) : ℝ)) =
            fun service => if service then 0 else 1 := by
        funext service
        cases service <;>
          simp [manyServerServiceOnlyUnrealizedPotentialService,
            manyServerServiceOnlyCompletedServiceCount]
      rw [hfunction]
      simp [PMF.integral_eq_sum, PMF.bernoulli]
      rw [ENNReal.toReal_sub_of_le]
      · norm_num
      · exact_mod_cast manyServerBusyFraction_le_one servers (state + 1) hservers
      · simp

/-- On the support of a finite arrival-free service transition, potential
opportunities split exactly into completed and unrealized services. -/
theorem manyServerServiceOnlyCompletedServiceCount_add_unrealized_eq_steps_of_support
    (servers state steps next : ℕ) (hservers : 0 < servers)
    (hnext : next ∈
      (CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).support) :
    manyServerServiceOnlyCompletedServiceCount state next +
      manyServerServiceOnlyUnrealizedPotentialService state steps next = steps := by
  obtain ⟨hlower, _hupper⟩ := manyServerServiceOnlyKernel_iterate_support_bounds
    servers state steps next hservers hnext
  have hcompleted_le : state - next ≤ steps := by
    omega
  unfold manyServerServiceOnlyUnrealizedPotentialService
  exact Nat.add_sub_of_le hcompleted_le

/-- In an arrival-free finite prefix, the unrealized-service count cannot
exceed the number of potential service opportunities. -/
theorem manyServerServiceOnlyUnrealizedPotentialService_le_steps
    (state steps next : ℕ) :
    manyServerServiceOnlyUnrealizedPotentialService state steps next ≤ steps := by
  unfold manyServerServiceOnlyUnrealizedPotentialService
  exact Nat.sub_le _ _

/-- The finite-prefix unrealized-service reward is integrable under its
arrival-free endpoint law. -/
theorem integrable_manyServerServiceOnlyUnrealizedPotentialService
    (servers state steps : ℕ) (hservers : 0 < servers) :
    Integrable (fun next : ℕ =>
      (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ))
      ((CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (steps : ℝ)
  filter_upwards [] with next
  rw [Real.norm_of_nonneg (by positivity)]
  exact_mod_cast manyServerServiceOnlyUnrealizedPotentialService_le_steps state steps next

/-- The square of the finite-prefix unrealized-service reward is integrable
under its arrival-free endpoint law. -/
theorem integrable_sq_manyServerServiceOnlyUnrealizedPotentialService
    (servers state steps : ℕ) (hservers : 0 < servers) :
    Integrable (fun next : ℕ =>
      (manyServerServiceOnlyUnrealizedPotentialService state steps next : ℝ) ^ 2)
      ((CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).toMeasure) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((steps : ℝ) ^ 2)
  filter_upwards [] with next
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  exact_mod_cast manyServerServiceOnlyUnrealizedPotentialService_le_steps state steps next

/-- If enough customers are present to keep all servers busy over a finite
arrival-free prefix, no potential service opportunity is unrealized. -/
theorem manyServerServiceOnlyUnrealizedPotentialService_eq_zero_of_high_support
    (servers state steps next : ℕ) (hservers : 0 < servers)
    (hstate : servers + steps ≤ state)
    (hnext : next ∈
      (CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).support) :
    manyServerServiceOnlyUnrealizedPotentialService state steps next = 0 := by
  have hkernel : CountableMarkovKernel.iterate
      (manyServerServiceOnlyKernel servers hservers) steps state =
      PMF.pure (state - steps) :=
    manyServerServiceOnlyKernel_iterate_eq_pure_sub servers state steps hservers hstate
  rw [hkernel] at hnext
  have hvalue : next = state - steps := by simpa using hnext
  rw [hvalue]
  unfold manyServerServiceOnlyUnrealizedPotentialService
    manyServerServiceOnlyCompletedServiceCount
  omega

/-- In every finite arrival-free prefix, unrealized potential services are
bounded by the potential-event overshoot beyond the initial busy-server
margin. -/
theorem manyServerServiceOnlyUnrealizedPotentialService_le_sub_excess
    (servers state steps next : ℕ) (hservers : 0 < servers)
    (hnext : next ∈
      (CountableMarkovKernel.iterate
        (manyServerServiceOnlyKernel servers hservers) steps state).support) :
    manyServerServiceOnlyUnrealizedPotentialService state steps next ≤
      steps - (state - servers) := by
  by_cases hhigh : steps ≤ state - servers
  · by_cases hstate : servers ≤ state
    · have hstate' : servers + steps ≤ state := by omega
      rw [manyServerServiceOnlyUnrealizedPotentialService_eq_zero_of_high_support
        servers state steps next hservers hstate' hnext]
      omega
    · have hzero : state - servers = 0 := by omega
      rw [hzero]
      exact Nat.sub_le _ _
  · have hlow : state - servers ≤ steps := by omega
    have hnext_le : next ≤ servers :=
      manyServerServiceOnlyKernel_iterate_support_le_servers_of_sub_le
        servers state steps next hservers hlow hnext
    unfold manyServerServiceOnlyUnrealizedPotentialService
      manyServerServiceOnlyCompletedServiceCount
    omega

/-- An arrival-free potential-event step has no upward transition. -/
lemma manyServerServiceOnlyKernel_upward
    (servers state : ℕ) (hservers : 0 < servers) :
    manyServerServiceOnlyKernel servers hservers state (state + 1) = 0 := by
  rw [manyServerServiceOnlyKernel, manyServerUniformizedKernel_birth]
  simp [uniformizedBirthProbability]

/-- The downward potential-event probability is exactly the busy-server
fraction. -/
lemma manyServerServiceOnlyKernel_downward
    (servers state : ℕ) (hservers : 0 < servers) :
    manyServerServiceOnlyKernel servers hservers (state + 1) state =
      (manyServerBusyFraction servers (state + 1) : ℝ≥0∞) := by
  rw [manyServerServiceOnlyKernel, manyServerUniformizedKernel_death]
  simp [uniformizedBirthProbability]

/-- Arrival-free transitions form a time-homogeneous continuous-time
semigroup. -/
theorem manyServerServiceOnlyTransition_comp
    (servers : ℕ) (hservers : 0 < servers) (serviceRate : ℝ)
    (hserviceRate_nonneg : 0 ≤ serviceRate) (firstTime secondTime : ℝ≥0) :
    manyServerServiceOnlyTransition servers hservers serviceRate hserviceRate_nonneg secondTime ∘ₖ
        manyServerServiceOnlyTransition servers hservers serviceRate hserviceRate_nonneg firstTime =
      manyServerServiceOnlyTransition servers hservers serviceRate hserviceRate_nonneg
        (firstTime + secondTime) := by
  exact CountableMarkovKernel.poissonizedKernelAtRate_comp
    (manyServerServiceOnlyKernel servers hservers)
    ((servers : ℝ) * serviceRate)
    (mul_nonneg (Nat.cast_nonneg servers) hserviceRate_nonneg) firstTime secondTime

end AppliedModelingLib.Probability.Queueing
