import AppliedModelingLib.Queueing.ExternalityPricing
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import AppliedModelingLib.Queueing.NonpreemptivePriority
import AppliedModelingLib.Queueing.StationaryPriorityInput

/-!
# Multiclass pricing definitions

The first section of Mendelson--Whang evaluates a finite vector of class flow
rates through gross class value minus delay cost times the steady-state class
population.  Little's-law population is represented as `flow i * waiting i`.
The queueing construction that supplies the waiting-time map is developed
separately; these definitions are the source-level economic layer.
-/

namespace MendelsonWhang1990PriorityPricing

open MeasureTheory ProbabilityTheory

/-- Equation (4): finite-class gross value less than total steady-state delay
cost, with `flow j * waitingTime j flow` as the class population. -/
noncomputable def netValue
    {Class : Type*} [Fintype Class]
    (value : Class → ℝ → ℝ) (delayCost : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ) (flow : Class → ℝ) : ℝ :=
  AppliedModelingLib.finiteDelayNetValue value delayCost waitingTime flow

/-- Equation (6): the marginal delay externality price for a class whose flow
coordinate is increased infinitesimally. -/
noncomputable def externalityPrice
    {Class : Type*} [Fintype Class]
    (delayCost flow partialWaiting : Class → ℝ) : ℝ :=
  AppliedModelingLib.finiteMarginalExternalityPrice delayCost flow partialWaiting

/-- The Appendix (A-1) nonpreemptive-priority queueing-time expression, with
lower `Fin` indices denoting higher priority.  This paper-level name records
the source convention; the reusable definition itself is source-neutral. -/
noncomputable def priorityQueueingTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  AppliedModelingLib.Queueing.finiteNonpreemptivePriorityQueueWait arrivalRate meanService i

/-- The total time in system in (A-1): queueing time plus a job's mean service
requirement. -/
noncomputable def prioritySojournTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  AppliedModelingLib.Queueing.finiteNonpreemptivePrioritySojournTime arrivalRate meanService i

/-- The total-time expression decomposes into its queueing and service parts. -/
theorem prioritySojournTime_eq_queueingTime_add_service
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) :
    prioritySojournTime arrivalRate meanService i =
      priorityQueueingTime arrivalRate meanService i + meanService i := rfl

/-- Appendix (A-1)'s stationary class population, expressed through Little's
law as its arrival rate times mean time in system. -/
noncomputable def priorityPopulation
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  arrivalRate i * prioritySojournTime arrivalRate meanService i

/-- The population-to-arrival-rate ratio in Appendix (A-1) is the class's
mean time in system whenever the displayed ratio is defined. -/
theorem priorityPopulation_div_arrivalRate_eq_prioritySojournTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n)
    (harrivalRate : 0 < arrivalRate i) :
    priorityPopulation arrivalRate meanService i / arrivalRate i =
      prioritySojournTime arrivalRate meanService i := by
  unfold priorityPopulation
  field_simp [ne_of_gt harrivalRate]

/-- The directional derivative of the Appendix (A-1) total-time expression
when the arrival rate of `arrivalClass` changes.  It is written explicitly so
the price in Theorem 1 is a visible finite sum, rather than a derivative
placeholder. -/
noncomputable def prioritySojournDerivative
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (arrivalClass priorityClass : Fin n) : ℝ :=
  (meanService arrivalClass ^ 2 *
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate priorityClass *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate priorityClass) -
    AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService *
      ((-(if arrivalClass < priorityClass then meanService arrivalClass else 0)) *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate priorityClass +
        AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate priorityClass *
          (-(if arrivalClass ≤ priorityClass then meanService arrivalClass else 0)))) /
    (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate priorityClass *
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate priorityClass) ^ 2

/-- The feasible arrival-rate vectors for the source's stationary M/M/1
priority-queue welfare problem: class service means are positive, every rate
is nonnegative, and the total offered work is strictly below the unit service
capacity.  The strict load condition is needed for the Appendix (A-1)
stationary waiting-time expression used in the objective. -/
def stablePriorityFlowDomain
    {n : ℕ} (meanService : Fin n → ℝ) : Set (Fin n → ℝ) :=
  { flow | (∀ j, 0 < meanService j) ∧
      (∀ j, 0 ≤ flow j) ∧ ∑ j, flow j * meanService j < 1 }

/-- A nonpreemptive priority schedule enumerates original classes in decreasing
priority order.  The Appendix (A-1) performance formula is evaluated after
that reindexing, then returned to the original class label. -/
noncomputable def priorityScheduleSojournTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) (customer : Fin n) : ℝ :=
  prioritySojournTime (arrivalRate ∘ schedule) (meanService ∘ schedule)
    (schedule.symm customer)

/-- Total delay cost per unit time under a scheduled priority ordering. -/
noncomputable def priorityScheduleDelayCost
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) : ℝ :=
  ∑ customer, delayCost customer * arrivalRate customer *
    priorityScheduleSojournTime arrivalRate meanService schedule customer

/-- The ordering-dependent queue-wait portion of scheduled delay cost.  The
own-service portion is invariant under a priority permutation. -/
noncomputable def priorityScheduleQueueDelayCost
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) : ℝ :=
  ∑ position, (delayCost ∘ schedule) position * (arrivalRate ∘ schedule) position *
    priorityQueueingTime (arrivalRate ∘ schedule) (meanService ∘ schedule) position

/-- Scheduled total delay cost separates into its ordering-dependent queue
component and the ordering-invariant own-service component. -/
theorem priorityScheduleDelayCost_eq_queueDelayCost_add_service
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) :
    priorityScheduleDelayCost arrivalRate delayCost meanService schedule =
      priorityScheduleQueueDelayCost arrivalRate delayCost meanService schedule +
        ∑ customer, delayCost customer * arrivalRate customer * meanService customer := by
  rw [priorityScheduleDelayCost]
  rw [← Equiv.sum_comp schedule]
  simp only [Function.comp_apply, priorityScheduleSojournTime,
    Equiv.symm_apply_apply, prioritySojournTime_eq_queueingTime_add_service]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [Equiv.sum_comp schedule
    (fun customer => delayCost customer * arrivalRate customer * meanService customer)]
  rfl

/-- The source welfare objective with both the arrival vector and the
nonpreemptive priority ordering visible. -/
noncomputable def priorityScheduleNetValue
    {n : ℕ} (value : Fin n → ℝ → ℝ)
    (arrivalRate delayCost meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) : ℝ :=
  (∑ customer, value customer (arrivalRate customer)) -
    priorityScheduleDelayCost arrivalRate delayCost meanService schedule

/-- The displayed class indexing is the identity priority schedule. -/
theorem priorityScheduleSojournTime_refl
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (customer : Fin n) :
    priorityScheduleSojournTime arrivalRate meanService (Equiv.refl _) customer =
      prioritySojournTime arrivalRate meanService customer := by
  rfl

/-- At the displayed priority ordering, the joint welfare objective reduces to
Equation (4)'s fixed-order form. -/
theorem priorityScheduleNetValue_refl
    {n : ℕ} (value : Fin n → ℝ → ℝ)
    (arrivalRate delayCost meanService : Fin n → ℝ) :
    priorityScheduleNetValue value arrivalRate delayCost meanService (Equiv.refl _) =
      netValue value delayCost
        (fun customer rates => prioritySojournTime rates meanService customer) arrivalRate := by
  simp only [priorityScheduleNetValue, priorityScheduleDelayCost,
    priorityScheduleSojournTime_refl, netValue,
    AppliedModelingLib.finiteDelayNetValue]
  rw [← Finset.sum_sub_distrib]

/-- Stability is invariant under a reindexing of priority positions. -/
theorem stablePriorityFlowDomain_comp_perm
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n))
    (hstable : arrivalRate ∈ stablePriorityFlowDomain meanService) :
    arrivalRate ∘ schedule ∈ stablePriorityFlowDomain (meanService ∘ schedule) := by
  rcases hstable with ⟨hmeanService, harrivalRate, htotalStable⟩
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · simpa only [Function.comp_apply] using hmeanService (schedule k)
  · simpa only [Function.comp_apply] using harrivalRate (schedule k)
  · calc
      ∑ k, (arrivalRate ∘ schedule) k * (meanService ∘ schedule) k =
          ∑ k, (fun j => arrivalRate j * meanService j) (schedule k) := by
            apply Finset.sum_congr rfl
            intro k _
            rfl
      _ = ∑ j, arrivalRate j * meanService j := by
            simpa using (Equiv.sum_comp schedule
              (fun j => arrivalRate j * meanService j))
      _ < 1 := htotalStable

/-- In the homogeneous-service specialization of Section 2, each mean service
requirement is one. -/
noncomputable def homogeneousPriorityQueueingTime
    {n : ℕ} (arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  priorityQueueingTime arrivalRate (fun _ => 1) i

/-- Equation (9)'s total waiting time in the homogeneous-service model. -/
noncomputable def homogeneousPrioritySojournTime
    {n : ℕ} (arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  prioritySojournTime arrivalRate (fun _ => 1) i

/-- Equation (8)'s class population, written through Little's law. -/
noncomputable def homogeneousPriorityPopulation
    {n : ℕ} (arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  arrivalRate i * homogeneousPrioritySojournTime arrivalRate i

/-- The next lower priority's value, with the source convention that the
quantity indexed by `R + 1` is zero. -/
noncomputable def prioritySuccessorOrZero
    {n : ℕ} (value : Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : i.1 + 1 < n then value ⟨i.1 + 1, h⟩ else 0

/-- At immediately adjacent priority levels, the zero-padded successor is the
actual next class. -/
theorem prioritySuccessorOrZero_eq_of_adjacent
    {n : ℕ} (value : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    prioritySuccessorOrZero value i = value k := by
  change i.1 < k.1 at hik
  have hnext : i.1 + 1 < n := by omega
  have hvalue : i.1 + 1 = k.1 := by
    by_contra hne
    have hlt : i.1 + 1 < k.1 := by omega
    let j : Fin n := ⟨i.1 + 1, hnext⟩
    have hij : i < j := by
      change i.1 < i.1 + 1
      omega
    have hjk : j < k := by
      change i.1 + 1 < k.1
      exact hlt
    exact hnoIntermediate j hij hjk
  simp [prioritySuccessorOrZero, hvalue]

/-- Equation (10): the homogeneous-service priority-dependent price.  The
first sum is the common marginal residual-work cost; the suffix sum is the
priority-specific component. -/
noncomputable def homogeneousPriorityPrice
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ k,
    arrivalRate k * delayCost k /
      (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate k)) +
    ∑ k, if i ≤ k then
      (arrivalRate k * delayCost k * homogeneousPriorityQueueingTime arrivalRate k +
        prioritySuccessorOrZero
          (fun j => arrivalRate j * delayCost j *
            homogeneousPriorityQueueingTime arrivalRate j) k) /
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k
      else 0

/-- Equation (19)'s priority- and time-dependent charge. -/
noncomputable def priorityTimeDependentPrice
    (linearCoefficient quadraticCoefficient processingTime : ℝ) : ℝ :=
  linearCoefficient * processingTime + (1 / 2 : ℝ) * quadraticCoefficient * processingTime ^ 2

/-- The expectation of a quadratic time-dependent charge reduces to the
first two processing-time moments.  This is the analytic part of the
optimality calculation for the PTD price, independent of a particular service
distribution. -/
theorem integral_priorityTimeDependentPrice
    (μ : Measure ℝ) (linearCoefficient quadraticCoefficient : ℝ)
    (hlinear : Integrable id μ)
    (hquadratic : Integrable (fun t : ℝ => t ^ 2) μ) :
    ∫ t, priorityTimeDependentPrice linearCoefficient quadraticCoefficient t ∂μ =
      linearCoefficient * ∫ t, t ∂μ +
        (1 / 2 : ℝ) * quadraticCoefficient * ∫ t, t ^ 2 ∂μ := by
  unfold priorityTimeDependentPrice
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
  · exact hlinear.const_mul linearCoefficient
  · exact hquadratic.const_mul ((1 / 2 : ℝ) * quadraticCoefficient)

/-- For an exponential service-time law with mean `meanService`, the first
and second moment identities turn the expected quadratic charge into the
closed form used in the source's Theorem 3 calculation.  The distributional
moment bridge is kept separate from this algebraic consequence. -/
theorem integral_priorityTimeDependentPrice_of_exponentialMoments
    (μ : Measure ℝ) (linearCoefficient quadraticCoefficient meanService : ℝ)
    (hlinear : Integrable id μ)
    (hquadratic : Integrable (fun t : ℝ => t ^ 2) μ)
    (hmean : ∫ t, t ∂μ = meanService)
    (hsecondMoment : ∫ t, t ^ 2 ∂μ = 2 * meanService ^ 2) :
    ∫ t, priorityTimeDependentPrice linearCoefficient quadraticCoefficient t ∂μ =
      linearCoefficient * meanService + quadraticCoefficient * meanService ^ 2 := by
  rw [integral_priorityTimeDependentPrice μ linearCoefficient quadraticCoefficient
    hlinear hquadratic, hmean, hsecondMoment]
  ring

/-- Equation (20)'s common quadratic coefficient for the heterogeneous-service
priority- and time-dependent price. -/
noncomputable def priorityTimeQuadraticCoefficient
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) : ℝ :=
  ∑ k,
    delayCost k * arrivalRate k /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k)

/-- The `a_i = v_i λ_i A_R` abbreviation in Equation (21). -/
noncomputable def priorityLinearNumerator
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  delayCost i * arrivalRate i *
    AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService

/-- Equation (21)'s linear coefficient.  The strict and inclusive slacks are
respectively the source's `S̄_{k-1}` and `S̄_k`. -/
noncomputable def priorityTimeLinearCoefficient
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  priorityLinearNumerator arrivalRate delayCost meanService i /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i ^ 2) +
    ∑ k, if i < k then
      (1 / (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k ^ 2 *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k) +
        1 / (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k ^ 2)) *
        priorityLinearNumerator arrivalRate delayCost meanService k
      else 0

/-- Equations (19)--(21)'s heterogeneous-service PTD charge for a declared
priority class and realized processing requirement. -/
noncomputable def heterogeneousPriorityTimeDependentPrice
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (priorityClass : Fin n) (processingTime : ℝ) : ℝ :=
  priorityTimeDependentPrice
    (priorityTimeLinearCoefficient arrivalRate delayCost meanService priorityClass)
    (priorityTimeQuadraticCoefficient arrivalRate delayCost meanService)
    processingTime

/-- The source's expected total cost for a class-`customer` job that declares
`declaredPriority` under a priority- and time-dependent schedule.  Its direct
charge is averaged against the customer's own exponential service law, while
the queueing-time and own service components determine delay cost. -/
noncomputable def priorityTimeDependentExpectedCost
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (pricing : Fin n → ℝ → ℝ)
    (customer declaredPriority : Fin n) : ℝ :=
  (∫ processingTime, pricing declaredPriority processingTime
      ∂expMeasure (meanService customer)⁻¹) +
    delayCost customer *
      (priorityQueueingTime arrivalRate meanService declaredPriority +
        meanService customer)

/-- The expected-cost increment from a class choosing a declared priority
instead of its assigned priority after the common quadratic expected-price
term has cancelled.  This is the cheating penalty used in Theorem 4. -/
noncomputable def priorityCheatingPenalty
    {n : ℕ} (meanService delayCost queueingTime linearCoefficient : Fin n → ℝ)
    (customer declaredPriority : Fin n) : ℝ :=
  meanService customer *
      (linearCoefficient declaredPriority - linearCoefficient customer) +
    delayCost customer *
      (queueingTime declaredPriority - queueingTime customer)

/-- The expected PTD charge for a class with exponential first and second
moments.  This is the expectation calculation in the optimality part of
Theorem 3, before identifying the resulting expression with Theorem 1's
marginal-externality price. -/
theorem integral_heterogeneousPriorityTimeDependentPrice_of_exponentialMoments
    (μ : Measure ℝ) {n : ℕ}
    (arrivalRate delayCost meanService : Fin n → ℝ)
    (customer declaredPriority : Fin n)
    (hlinear : Integrable id μ)
    (hquadratic : Integrable (fun t : ℝ => t ^ 2) μ)
    (hmean : ∫ t, t ∂μ = meanService customer)
    (hsecondMoment : ∫ t, t ^ 2 ∂μ = 2 * meanService customer ^ 2) :
    ∫ t, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost
      meanService declaredPriority t ∂μ =
      priorityTimeLinearCoefficient arrivalRate delayCost meanService declaredPriority *
        meanService customer +
      priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
        meanService customer ^ 2 := by
  exact integral_priorityTimeDependentPrice_of_exponentialMoments μ
    (priorityTimeLinearCoefficient arrivalRate delayCost meanService declaredPriority)
    (priorityTimeQuadraticCoefficient arrivalRate delayCost meanService)
    (meanService customer) hlinear hquadratic hmean hsecondMoment

/-- For the source's exponential service distribution, the expected PTD
charge has the closed form used in the heterogeneous priority calculation. -/
theorem integral_heterogeneousPriorityTimeDependentPrice_expMeasure
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (hmeanService : ∀ i, 0 < meanService i)
    (customer declaredPriority : Fin n) :
    ∫ t, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost
      meanService declaredPriority t ∂expMeasure (meanService customer)⁻¹ =
      priorityTimeLinearCoefficient arrivalRate delayCost meanService declaredPriority *
        meanService customer +
      priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
        meanService customer ^ 2 := by
  exact integral_heterogeneousPriorityTimeDependentPrice_of_exponentialMoments
    (expMeasure (meanService customer)⁻¹) arrivalRate delayCost meanService customer declaredPriority
    (AppliedModelingLib.Probability.integrable_id_expMeasure_inv (hmeanService customer))
    (AppliedModelingLib.Probability.integrable_sq_expMeasure_inv (hmeanService customer))
    (AppliedModelingLib.Probability.integral_id_expMeasure_inv (hmeanService customer))
    (AppliedModelingLib.Probability.integral_sq_expMeasure_inv (hmeanService customer))

/-- The concrete stationary marked-Poisson input realizes the service-time
expectation used by the heterogeneous PTD charge. -/
theorem integral_heterogeneousPriorityTimeDependentPrice_stationaryWorkRequirement
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (priorityClass : Fin n) (eventIndex : ℤ) :
    ∫ omega, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService
        priorityClass
        (AppliedModelingLib.Queueing.stationaryPriorityWorkRequirement meanService priorityClass
          omega eventIndex)
      ∂AppliedModelingLib.Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      priorityTimeLinearCoefficient arrivalRate delayCost meanService priorityClass *
        meanService priorityClass +
      priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
        meanService priorityClass ^ 2 := by
  calc
    ∫ omega, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService
        priorityClass
        (AppliedModelingLib.Queueing.stationaryPriorityWorkRequirement meanService priorityClass
          omega eventIndex)
      ∂AppliedModelingLib.Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
        ∫ t, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService
          priorityClass t ∂expMeasure (meanService priorityClass)⁻¹ := by
      simpa [Function.comp_def] using
        (AppliedModelingLib.Queueing.stationaryPriorityWorkRequirement_hasLaw arrivalRate meanService
          harrivalRate hmeanService priorityClass eventIndex).integral_comp
          (f := heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService priorityClass)
          (by
            unfold heterogeneousPriorityTimeDependentPrice priorityTimeDependentPrice
            fun_prop)
    _ = _ := integral_heterogeneousPriorityTimeDependentPrice_expMeasure
      arrivalRate delayCost meanService hmeanService priorityClass priorityClass

/-- The same expected PTD charge under the genuine multiclass Palm law of an
arriving customer in the stated class.  The passive classes remain in the
tagged carrier, shifted to the selected customer's physical arrival epoch. -/
theorem integral_heterogeneousPriorityTimeDependentPrice_stationaryClassTaggedWorkRequirement
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (customer declaredPriority : Fin n) :
    ∫ omega, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost
        meanService declaredPriority
        (AppliedModelingLib.Queueing.stationaryPriorityClassTaggedWorkRequirement
          meanService customer omega)
      ∂(AppliedModelingLib.Probability.Palm.targetPassiveTaggedArrivalAtZero
        (AppliedModelingLib.Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate customer))
        (AppliedModelingLib.Queueing.multiclassStationaryPoissonWorkRestLaw
          arrivalRate harrivalRate customer)).Ptag =
      priorityTimeLinearCoefficient arrivalRate delayCost meanService declaredPriority *
        meanService customer +
      priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
        meanService customer ^ 2 := by
  calc
    ∫ omega, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost
        meanService declaredPriority
        (AppliedModelingLib.Queueing.stationaryPriorityClassTaggedWorkRequirement
          meanService customer omega)
      ∂(AppliedModelingLib.Probability.Palm.targetPassiveTaggedArrivalAtZero
        (AppliedModelingLib.Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate customer))
        (AppliedModelingLib.Queueing.multiclassStationaryPoissonWorkRestLaw
          arrivalRate harrivalRate customer)).Ptag =
        ∫ t, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost
          meanService declaredPriority t ∂expMeasure (meanService customer)⁻¹ := by
      simpa [Function.comp_def] using
        (AppliedModelingLib.Queueing.stationaryPriorityClassTaggedWorkRequirement_hasLaw
          arrivalRate meanService harrivalRate hmeanService customer).integral_comp
          (f := heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService declaredPriority)
          (by
            unfold heterogeneousPriorityTimeDependentPrice priorityTimeDependentPrice
            fun_prop)
    _ = _ := integral_heterogeneousPriorityTimeDependentPrice_expMeasure
      arrivalRate delayCost meanService hmeanService customer declaredPriority

end MendelsonWhang1990PriorityPricing
