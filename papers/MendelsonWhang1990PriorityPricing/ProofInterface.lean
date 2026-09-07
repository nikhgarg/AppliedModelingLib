import MendelsonWhang1990PriorityPricing.PaperInterface

/-!
# Proof Interface: Optimal Incentive-Compatible Priority Pricing for the M/M/1 Queue

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace MendelsonWhang1990PriorityPricing

/-- Appendix (A-1)'s stationary sojourn-time and population-ratio endpoint. -/
theorem appendixPriorityQueueingTime : appendixPriorityQueueingTimeSpec := by
  intro n arrivalRate meanService harrivalRate hmeanService hstable i
  refine ⟨stationaryPriorityClassTaggedExpectedResponse_eq_prioritySojournTime
    arrivalRate meanService harrivalRate hmeanService hstable i, rfl, ?_⟩
  exact priorityPopulation_div_arrivalRate_eq_prioritySojournTime
    arrivalRate meanService i (harrivalRate i)

/-- Theorem 1's proof endpoint. -/
theorem theoremOneExternalityPricing : theoremOneExternalityPricingSpec := by
  classical
  intro Class _ value delayCost flow price waitingTime i marginalValue
    partialWaiting _hvalueConditions _hdelayCostConditions hflow hflow_i hmax
    hdemand hwaiting
  rcases hdemand with ⟨hvalue, hdemand⟩
  have hcoordinateMax : IsMaxOn
      (fun t => netValue value delayCost waitingTime
        (Function.update flow i t))
      (Set.Ici 0) (flow i) := by
    rw [isMaxOn_iff]
    intro t ht
    have hupdate : Function.update flow i t ∈
        Set.Ici (fun _ : Class => 0) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using ht
      · simpa [hji, Function.update_of_ne hji] using hflow j
    rw [isMaxOn_iff] at hmax
    simpa using hmax (Function.update flow i t) hupdate
  have hfirstOrder := theoremOneExternalityPricing_impl value delayCost
    waitingTime flow i marginalValue partialWaiting hvalue hwaiting
    (hcoordinateMax.isLocalMax (Ici_mem_nhds hflow_i))
  rw [hdemand] at hfirstOrder
  linarith

/-- Total-load stability supplies all slack inequalities in the homogeneous
priority model. -/
private theorem homogeneousPriority_slacks_of_totalStable
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (htotalStable : ∑ j, arrivalRate j < 1) :
    ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j := by
  intro j
  have hloadNonneg : ∀ k, 0 ≤ (fun _ : Fin n => (1 : ℝ)) k * arrivalRate k := by
    intro k
    simpa using harrivalRate k
  have htotal : ∑ k, (fun _ : Fin n => (1 : ℝ)) k * arrivalRate k < 1 := by
    simpa using htotalStable
  constructor
  · exact AppliedModelingLib.Queueing.finitePriorityStrictSlack_pos_of_totalLoad_lt_one
      (fun _ => 1) arrivalRate hloadNonneg htotal j
  · exact AppliedModelingLib.Queueing.finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
      (fun _ => 1) arrivalRate hloadNonneg htotal j

/-- Total-load stability supplies all slack inequalities in the heterogeneous
priority model. -/
private theorem priority_slacks_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (htotalStable : ∑ j, arrivalRate j * meanService j < 1) :
    ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j := by
  intro j
  have hloadNonneg : ∀ k, 0 ≤ meanService k * arrivalRate k := by
    intro k
    exact mul_nonneg (hmeanService k).le (harrivalRate k).le
  have htotal : ∑ k, meanService k * arrivalRate k < 1 := by
    simpa [mul_comm] using htotalStable
  constructor
  · exact AppliedModelingLib.Queueing.finitePriorityStrictSlack_pos_of_totalLoad_lt_one
      meanService arrivalRate hloadNonneg htotal j
  · exact AppliedModelingLib.Queueing.finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
      meanService arrivalRate hloadNonneg htotal j

/-- Theorem 2's strict incentive-compatibility endpoint. -/
theorem theoremTwoPriorityIncentiveCompatibility :
    theoremTwoPriorityIncentiveCompatibilitySpec := by
  intro n arrivalRate delayCost harrivalRate htotalStable hdelayCost i
    selectedPriority hmisreport
  simpa [homogeneousPriorityExpectedCost] using
    homogeneousPriority_incentiveCompatible_strict arrivalRate delayCost harrivalRate
      (homogeneousPriority_slacks_of_totalStable arrivalRate
        (fun j => (harrivalRate j).le) htotalStable)
      hdelayCost i selectedPriority hmisreport

/-- Theorem 3's PTD optimality and strict incentive-compatibility endpoint. -/
theorem theoremThreePriorityTimeDependentPricing :
    theoremThreePriorityTimeDependentPricingSpec := by
  intro n value arrivalRate delayCost meanService marginalValue
    _hvalueConditions _hdelayCostConditions harrivalRate hmeanService
    htotalStable hpriority hvalue hmax
  have hslack := priority_slacks_of_totalStable arrivalRate meanService
    harrivalRate hmeanService htotalStable
  have hjointMax : IsMaxOn
      (fun pair : (Fin n → ℝ) × Equiv.Perm (Fin n) =>
        priorityScheduleNetValue value pair.1 delayCost meanService pair.2)
      (Set.prod (stablePriorityFlowDomain meanService) Set.univ)
      (arrivalRate, Equiv.refl _) := by
    apply priorityScheduleNetValue_refl_isMaxOn value arrivalRate delayCost meanService
      (fun {i k} hik => (hpriority hik).le) hmax
  have hcharge : ∀ i,
      stationaryClassTaggedExpectedPriorityTimeDependentPrice
          arrivalRate delayCost meanService harrivalRate i i =
        externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i) := by
    intro i
    calc
      stationaryClassTaggedExpectedPriorityTimeDependentPrice
          arrivalRate delayCost meanService harrivalRate i i =
          priorityTimeLinearCoefficient arrivalRate delayCost meanService i * meanService i +
            priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
              meanService i ^ 2 := by
            simpa [stationaryClassTaggedExpectedPriorityTimeDependentPrice] using
              integral_heterogeneousPriorityTimeDependentPrice_stationaryClassTaggedWorkRequirement
                arrivalRate delayCost meanService harrivalRate hmeanService i i
      _ = externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i) := by
            apply heterogeneousPriority_expectedPrice_eq_externalityPrice
            intro j
            exact ⟨ne_of_gt (hslack j).1, ne_of_gt (hslack j).2⟩
  have hcostDifference : ∀ i selectedPriority,
      priorityTimeDependentExpectedCost arrivalRate delayCost meanService
          (heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService)
          i selectedPriority -
        priorityTimeDependentExpectedCost arrivalRate delayCost meanService
          (heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService)
          i i =
        priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService)
          i selectedPriority := by
    intro i selectedPriority
    unfold priorityTimeDependentExpectedCost
    rw [integral_heterogeneousPriorityTimeDependentPrice_expMeasure
      arrivalRate delayCost meanService hmeanService i selectedPriority,
      integral_heterogeneousPriorityTimeDependentPrice_expMeasure
        arrivalRate delayCost meanService hmeanService i i]
    unfold priorityCheatingPenalty
    ring
  refine ⟨?_, hcharge, ?_⟩
  · refine ⟨hjointMax, ?_, ?_, ?_⟩
    · intro i
      refine ⟨hvalue i, ?_⟩
      have hfirstOrder := priorityQueueFirstOrderPricing_of_globalMax_of_totalStable
        value delayCost arrivalRate meanService i (marginalValue i)
        (fun j => (harrivalRate j).le) hmeanService
        htotalStable (harrivalRate i) (hvalue i) hmax
      calc
        marginalValue i =
            delayCost i * prioritySojournTime arrivalRate meanService i +
              externalityPrice delayCost arrivalRate
                (prioritySojournDerivative arrivalRate meanService i) := hfirstOrder
        _ = priorityTimeDependentExpectedCost arrivalRate delayCost meanService
              (heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService)
              i (id i) := by
              simp only [id_eq]
              unfold priorityTimeDependentExpectedCost
              rw [integral_heterogeneousPriorityTimeDependentPrice_expMeasure
                arrivalRate delayCost meanService hmeanService i i]
              rw [heterogeneousPriority_expectedPrice_eq_externalityPrice
                arrivalRate delayCost meanService i (fun j =>
                  ⟨ne_of_gt (hslack j).1, ne_of_gt (hslack j).2⟩)]
              rw [prioritySojournTime_eq_queueingTime_add_service]
              ring
    · intro i selectedPriority
      change priorityTimeDependentExpectedCost arrivalRate delayCost meanService
          (heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService)
          i i ≤
        priorityTimeDependentExpectedCost arrivalRate delayCost meanService
          (heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService)
          i selectedPriority
      by_cases hassigned : selectedPriority = i
      · subst selectedPriority
        rfl
      · have hstrict := heterogeneousPriority_incentiveCompatible_strict
          arrivalRate delayCost meanService harrivalRate hmeanService hslack hpriority
          i selectedPriority hassigned
        have hdifference := hcostDifference i selectedPriority
        linarith
    · intro i
      rfl
  · intro i selectedPriority hmisreport
    exact heterogeneousPriority_incentiveCompatible_strict
      arrivalRate delayCost meanService harrivalRate hmeanService hslack hpriority
      i selectedPriority hmisreport

/-- Theorem 4's cheating-penalty monotonicity endpoint. -/
theorem theoremFourCheatingPenaltyMonotonicity :
    theoremFourCheatingPenaltyMonotonicitySpec := by
  intro n arrivalRate delayCost meanService harrivalRate hmeanService htotalStable hpriority
  have hslack := priority_slacks_of_totalStable arrivalRate meanService
    harrivalRate hmeanService htotalStable
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [priorityCheatingPenalty]
  · intro i j k hij hjk
    exact heterogeneousPriority_cheatingPenalty_strictMono_below
      arrivalRate delayCost meanService harrivalRate hmeanService hslack hpriority hij hjk
  · intro i j k hki hjk
    exact heterogeneousPriority_cheatingPenalty_strictMono_above
      arrivalRate delayCost meanService harrivalRate hmeanService hslack hpriority hki hjk

end MendelsonWhang1990PriorityPricing
