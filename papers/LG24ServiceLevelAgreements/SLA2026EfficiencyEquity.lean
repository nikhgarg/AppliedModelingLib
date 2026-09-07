import LG24ServiceLevelAgreements.SLA2026Model
import LG24ServiceLevelAgreements.ProposedCategoryPooling
import LG24ServiceLevelAgreements.ProposedPriceFormulas
import Mathlib.Tactic

/-!
# Active 2026 SLA efficiency and equity endpoints

This module proves the two endpoint propositions compiled by `main_msom.tex`:

* extreme efficiency is the displayed square-root allocation; and
* extreme equity has a feasible zero-disparity point and chooses the least
  all-request efficiency loss among those zero-disparity points.

The assumptions in the two paper-facing theorems are the source primitives,
not a packaged optimization certificate.  The queueing tail result is outside
this finite-dimensional endpoint module.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Direct source-model bridges -/

/-- Flattening the source's matrix feasible set into the finite-cell certificate. -/
theorem sla2026Feasible_iff_boroughSeparated
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : ℝ) (admitted : Category → Borough → ℝ)
    (delay : Category → Borough → ℝ) :
    sla2026Feasible tail capacity admitted delay ↔
      reciprocalCapacityFeasible
        (boroughSeparatedTail (Borough := Borough) (fun _ : Category ↦ tail))
        (sla2026ExcessCapacity capacity admitted)
        (fun i ↦ delay i.1 i.2) := by
  simpa [sla2026Feasible] using
    (finiteMatrixReciprocalCapacityFeasible_categoryTail_iff
      (Borough := Borough) (fun _ : Category ↦ tail)
      (sla2026ExcessCapacity capacity admitted) delay)

/-- The source's `A_eff(s)` is the finite-cell square-root aggregate. -/
theorem sla2026EffectiveLoad_eq_boroughSeparatedRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : ℝ) (admitted priority : Category → Borough → ℝ) :
    sla2026EffectiveLoad tail admitted priority =
      boroughSeparatedRoot (fun _ : Category ↦ tail) admitted priority := by
  classical
  unfold sla2026EffectiveLoad boroughSeparatedRoot
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro b _hb
  congr 1
  ring

/-- The source delay-dependent sum is the flattened served-delay objective. -/
theorem sla2026ServedDelayCost_eq_boroughSeparated
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (admitted priority delay : Category → Borough → ℝ) :
    sla2026ServedDelayCost admitted priority delay =
      servedDelayEfficiency (boroughSeparatedWeight admitted priority)
        (fun i ↦ delay i.1 i.2) := by
  classical
  unfold sla2026ServedDelayCost servedDelayEfficiency boroughSeparatedWeight
  rw [Fintype.sum_prod_type]

/-- The full source efficiency objective is served delay plus a fixed term. -/
theorem sla2026Efficiency_eq_servedDelayCost_add_fixed
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ)
    (harrival : ∀ k b, arrival k b ≠ 0) :
    sla2026Efficiency arrival admitted priority noninspectionPenalty delay =
      sla2026ServedDelayCost admitted priority delay +
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty := by
  classical
  have h := finiteArrivalWeightedBurden_fixedLoad_eq_served_add_noninspection
    arrival admitted priority noninspectionPenalty delay harrival
  simpa [sla2026Efficiency, sla2026Cost, sla2026InspectionProbability,
    finiteFixedLoadAllRequestBurdenProfile, fixedLoadAllRequestBurden,
    sla2026ServedDelayCost, sla2026FixedNoninspectionCost,
    servedDelayEfficiency, boroughSeparatedWeight, fixedLoadNoninspectionCost,
    Fintype.sum_prod_type] using h

/-- The generic certified endpoint is exactly the active source's display. -/
theorem sla2026EfficientDelay_eq_boroughSeparatedAllocationDelay
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (k : Category) (b : Borough) :
    sla2026EfficientDelay tail capacity admitted priority k b =
      boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
        admitted priority (sla2026ExcessCapacity capacity admitted) k b := by
  unfold sla2026EfficientDelay boroughSeparatedAllocationDelay
  rw [squareRootAllocationDelay_eq_fixedLoadEfficiencyDelay
    (tail := boroughSeparatedTail (Borough := Borough) (fun _ : Category ↦ tail))
    (weight := boroughSeparatedWeight admitted priority)
    (fun i ↦ by simpa [boroughSeparatedTail] using htail)
    (fun i ↦ by
      simpa [boroughSeparatedWeight] using
        mul_pos (hadmitted i.1 i.2) (hpriority i.1 i.2)) (k, b)]
  rw [← boroughSeparatedRoot_eq_aggregateRootWeight]
  rw [← sla2026EffectiveLoad_eq_boroughSeparatedRoot]
  simp [fixedLoadEfficiencyDelay, boroughSeparatedTail,
    boroughSeparatedWeight]

/-! ## Extreme efficiency -/

/-- At `gamma = 1`, the source tradeoff objective is exactly efficiency loss. -/
theorem sla2026Tradeoff_one
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ) :
    sla2026Tradeoff 1 arrival admitted priority noninspectionPenalty delay =
      sla2026Efficiency arrival admitted priority noninspectionPenalty delay := by
  simp [sla2026Tradeoff]

/-- The active source's square-root endpoint is globally efficiency optimal. -/
theorem sla2026_extreme_efficiency
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (sla2026Feasible tail capacity admitted)
      (sla2026Efficiency arrival admitted priority noninspectionPenalty)
      (sla2026EfficientDelay tail capacity admitted priority) := by
  let endpoint := boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
    admitted priority (sla2026ExcessCapacity capacity admitted)
  have hendpoint_min := boroughSeparatedAllocationDelay_isMinimizerOn
    (tail := fun _ : Category ↦ tail) (admitted := admitted) (risk := priority)
    (excessCapacity := sla2026ExcessCapacity capacity admitted)
    (fun _ ↦ htail) hadmitted hpriority hexcess
  have hformula : ∀ k b,
      sla2026EfficientDelay tail capacity admitted priority k b = endpoint k b := by
    intro k b
    exact sla2026EfficientDelay_eq_boroughSeparatedAllocationDelay
      htail hadmitted hpriority k b
  have hendpoint_eq :
      (fun i : Category × Borough ↦
        sla2026EfficientDelay tail capacity admitted priority i.1 i.2) =
        (fun i ↦ endpoint i.1 i.2) := by
    funext i
    exact hformula i.1 i.2
  constructor
  · apply (sla2026Feasible_iff_boroughSeparated
      tail capacity admitted
      (sla2026EfficientDelay tail capacity admitted priority)).2
    rw [hendpoint_eq]
    exact hendpoint_min.1
  · intro delay hdelay
    have hdelay_flat : reciprocalCapacityFeasible
        (boroughSeparatedTail (Borough := Borough) (fun _ : Category ↦ tail))
        (sla2026ExcessCapacity capacity admitted)
        (fun i ↦ delay i.1 i.2) :=
      (sla2026Feasible_iff_boroughSeparated tail capacity admitted delay).1 hdelay
    have hserved :
        sla2026ServedDelayCost admitted priority
            (sla2026EfficientDelay tail capacity admitted priority) ≤
          sla2026ServedDelayCost admitted priority delay := by
      rw [sla2026ServedDelayCost_eq_boroughSeparated,
        sla2026ServedDelayCost_eq_boroughSeparated, hendpoint_eq]
      exact hendpoint_min.2 _ hdelay_flat
    rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
      arrival admitted priority noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority)
        (fun k b ↦ (harrival k b).ne'),
      sla2026Efficiency_eq_servedDelayCost_add_fixed
        arrival admitted priority noninspectionPenalty delay
        (fun k b ↦ (harrival k b).ne')]
    linarith

/--
The displayed extreme-efficiency delay is the unique source feasible
efficiency minimizer.  This is the equality case behind the source wording
that gives the optimizing delay by its closed formula.
-/
theorem sla2026_extreme_efficiency_unique
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {delay : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hmin : AppliedModelingLib.Optimization.IsMinimizerOn
      (sla2026Feasible tail capacity admitted)
      (sla2026Efficiency arrival admitted priority noninspectionPenalty)
      delay) :
    delay = sla2026EfficientDelay tail capacity admitted priority := by
  classical
  let endpoint := sla2026EfficientDelay tail capacity admitted priority
  let effective := sla2026EffectiveLoad tail admitted priority
  let excess := sla2026ExcessCapacity capacity admitted
  let multiplier : ℝ := effective ^ 2 / excess ^ 2
  let deviation : Category → Borough → ℝ := fun k b ↦
    admitted k b * priority k b * (delay k b - endpoint k b) ^ 2 / delay k b
  change delay = endpoint
  have hexcessNe : excess ≠ 0 := by
    simpa [excess] using hexcess.ne'
  have hendpointMin : AppliedModelingLib.Optimization.IsMinimizerOn
      (sla2026Feasible tail capacity admitted)
      (sla2026Efficiency arrival admitted priority noninspectionPenalty)
      endpoint := by
    simpa [endpoint] using
      (sla2026_extreme_efficiency htail harrival hadmitted
        hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess)
  have hendpointFormula : ∀ k b, endpoint k b =
      boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
        admitted priority excess k b := by
    intro k b
    simpa [endpoint, excess] using
      (sla2026EfficientDelay_eq_boroughSeparatedAllocationDelay
        htail hadmitted hpriority k b)
  have hendpoint_eq :
      (fun i : Category × Borough ↦ endpoint i.1 i.2) =
        (fun i ↦ boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
          admitted priority excess i.1 i.2) := by
    funext i
    exact hendpointFormula i.1 i.2
  have hservedEndpoint :
      sla2026ServedDelayCost admitted priority endpoint =
        effective ^ 2 / excess := by
    calc
      sla2026ServedDelayCost admitted priority endpoint =
          servedDelayEfficiency (boroughSeparatedWeight admitted priority)
            (fun i ↦ endpoint i.1 i.2) :=
        sla2026ServedDelayCost_eq_boroughSeparated admitted priority endpoint
      _ = servedDelayEfficiency (boroughSeparatedWeight admitted priority)
          (fun i ↦ boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
            admitted priority excess i.1 i.2) := by rw [hendpoint_eq]
      _ = boroughSeparatedRoot (fun _ : Category ↦ tail) admitted priority ^ 2 /
          excess := by
        simpa [excess] using
          (servedDelayEfficiency_boroughSeparatedAllocationDelay
            (fun _ ↦ htail) hadmitted hpriority hexcess)
      _ = effective ^ 2 / excess := by
        rw [← sla2026EffectiveLoad_eq_boroughSeparatedRoot]
  have hobjective :
      sla2026Efficiency arrival admitted priority noninspectionPenalty endpoint =
        sla2026Efficiency arrival admitted priority noninspectionPenalty delay :=
    AppliedModelingLib.Optimization.IsMinimizerOn.objective_eq_of_isMinimizerOn
      hendpointMin hmin
  have hservedValue :
      sla2026ServedDelayCost admitted priority endpoint =
        sla2026ServedDelayCost admitted priority delay := by
    rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
        arrival admitted priority noninspectionPenalty endpoint
        (fun k b ↦ (harrival k b).ne'),
      sla2026Efficiency_eq_servedDelayCost_add_fixed
        arrival admitted priority noninspectionPenalty delay
        (fun k b ↦ (harrival k b).ne')] at hobjective
    linarith
  rcases hmin.1 with ⟨hdelayPositive, hcapacityUse⟩
  have hstationary : ∀ k b,
      multiplier * tail =
        (admitted k b * priority k b) * endpoint k b ^ 2 := by
    intro k b
    let weight := admitted k b * priority k b
    let root := Real.sqrt (tail / weight)
    have hweight : 0 < weight := by
      dsimp [weight]
      exact mul_pos (hadmitted k b) (hpriority k b)
    have hrootSq : root ^ 2 = tail / weight := by
      dsimp [root]
      exact Real.sq_sqrt (div_nonneg htail.le hweight.le)
    change effective ^ 2 / excess ^ 2 * tail =
      weight * (effective / excess * root) ^ 2
    calc
      effective ^ 2 / excess ^ 2 * tail =
          weight * (effective ^ 2 / excess ^ 2) * (tail / weight) := by
        field_simp [hexcessNe, hweight.ne']
      _ = weight * (effective / excess * root) ^ 2 := by
        rw [← hrootSq]
        field_simp [hexcessNe]
  have hcell : ∀ k b,
      admitted k b * priority k b * delay k b +
          multiplier * (tail / delay k b) -
          2 * (admitted k b * priority k b * endpoint k b) =
        deviation k b := by
    intro k b
    dsimp [deviation]
    field_simp [(hdelayPositive k b).ne']
    rw [hstationary k b]
    ring
  have hsum :
      sla2026ServedDelayCost admitted priority delay +
          multiplier * (∑ k, ∑ b, tail / delay k b) -
          2 * sla2026ServedDelayCost admitted priority endpoint =
        ∑ k, ∑ b, deviation k b := by
    calc
      sla2026ServedDelayCost admitted priority delay +
          multiplier * (∑ k, ∑ b, tail / delay k b) -
          2 * sla2026ServedDelayCost admitted priority endpoint =
          (∑ k, ∑ b, admitted k b * priority k b * delay k b) +
            (∑ k, ∑ b, multiplier * (tail / delay k b)) -
            (∑ k, ∑ b, 2 *
              (admitted k b * priority k b * endpoint k b)) := by
          unfold sla2026ServedDelayCost
          simp_rw [Finset.mul_sum]
      _ = ∑ k, ∑ b,
          (admitted k b * priority k b * delay k b +
            multiplier * (tail / delay k b) -
            2 * (admitted k b * priority k b * endpoint k b)) := by
          simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = ∑ k, ∑ b, deviation k b := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro b _hb
          exact hcell k b
  have hmultiplierNonneg : 0 ≤ multiplier := by
    dsimp [multiplier]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmultiplierCapacity :
      multiplier * (∑ k, ∑ b, tail / delay k b) ≤ multiplier * excess :=
    mul_le_mul_of_nonneg_left hcapacityUse hmultiplierNonneg
  have hmultiplierExcess : multiplier * excess = effective ^ 2 / excess := by
    dsimp [multiplier]
    field_simp [hexcessNe]
  have hupper :
      sla2026ServedDelayCost admitted priority delay +
          multiplier * (∑ k, ∑ b, tail / delay k b) -
          2 * sla2026ServedDelayCost admitted priority endpoint ≤ 0 := by
    nlinarith [hmultiplierCapacity, hmultiplierExcess,
      hservedEndpoint, hservedValue]
  have hdeviationNonneg : ∀ k b, 0 ≤ deviation k b := by
    intro k b
    dsimp [deviation]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (hadmitted k b).le (hpriority k b).le)
        (sq_nonneg _))
      (hdelayPositive k b).le
  have hdeviationSumNonneg : 0 ≤ ∑ k, ∑ b, deviation k b := by
    exact Finset.sum_nonneg fun k _hk ↦
      Finset.sum_nonneg fun b _hb ↦ hdeviationNonneg k b
  have hdeviationSumZero : (∑ k, ∑ b, deviation k b) = 0 := by
    apply le_antisymm
    · rw [← hsum]
      exact hupper
    · exact hdeviationSumNonneg
  have hdeviationZero : ∀ k b, deviation k b = 0 := by
    have houter := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_hk : k ∈ (Finset.univ : Finset Category)) ↦
        Finset.sum_nonneg fun b _hb ↦ hdeviationNonneg k b)).1 hdeviationSumZero
    intro k b
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun c (_hc : c ∈ (Finset.univ : Finset Borough)) ↦
        hdeviationNonneg k c)).1
      (houter k (Finset.mem_univ k)) b (Finset.mem_univ b)
  funext k b
  have hzero := hdeviationZero k b
  dsimp [deviation] at hzero
  have hnumerator :
      admitted k b * priority k b * (delay k b - endpoint k b) ^ 2 = 0 :=
    (div_eq_zero_iff).1 hzero |>.resolve_right (hdelayPositive k b).ne'
  have hsquare : (delay k b - endpoint k b) ^ 2 = 0 :=
    (mul_eq_zero.mp hnumerator).resolve_left
      (mul_pos (hadmitted k b) (hpriority k b)).ne'
  exact sub_eq_zero.mp ((sq_eq_zero_iff).1 hsquare)

/-! ## Extreme equity -/

/-- A source-facing form of efficiency tie-breaking among equitable delays. -/
def sla2026EfficiencyBestEquitable
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (tail capacity : ℝ)
    (arrival admitted priority noninspectionPenalty : Category → Borough → ℝ)
    (delay : Category → Borough → ℝ) : Prop :=
  sla2026Feasible tail capacity admitted delay ∧
    sla2026Equity arrival admitted priority noninspectionPenalty delay = 0 ∧
    ∀ other, sla2026Feasible tail capacity admitted other →
      sla2026Equity arrival admitted priority noninspectionPenalty other = 0 →
        sla2026Efficiency arrival admitted priority noninspectionPenalty delay ≤
          sla2026Efficiency arrival admitted priority noninspectionPenalty other

/-- At `gamma = 0`, the scalarized source objective is precisely equity loss. -/
theorem sla2026Tradeoff_zero
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ) :
    sla2026Tradeoff 0 arrival admitted priority noninspectionPenalty delay =
      sla2026Equity arrival admitted priority noninspectionPenalty delay := by
  simp [sla2026Tradeoff]

/--
The active source's extreme-equity endpoint exists, has zero within-category
cost range, and is efficiency-best among all feasible zero-range endpoints.
-/
theorem sla2026_extreme_equity
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    ∃ delay, sla2026EfficiencyBestEquitable tail capacity arrival admitted
        priority noninspectionPenalty delay ∧
      ∃ level : Category → ℝ, ∀ k b,
        sla2026Cost arrival admitted priority noninspectionPenalty delay k b =
          level k := by
  let inspectionProbability := sla2026InspectionProbability arrival admitted
  have hinspect : ∀ k b, 0 < inspectionProbability k b := by
    intro k b
    exact div_pos (hadmitted k b) (harrival k b)
  have hslope : ∀ k b,
      0 < allRequestDelaySlope (priority k b) (inspectionProbability k b) := by
    intro k b
    unfold allRequestDelaySlope
    exact mul_pos (hpriority k b) (hinspect k b)
  have hcoefficient : ∀ k b,
      0 < allRequestParityCapacityCoefficient tail (priority k b)
        (inspectionProbability k b) := by
    intro k b
    unfold allRequestParityCapacityCoefficient
    exact mul_pos (mul_pos htail (hpriority k b)) (hinspect k b)
  have harrivalMass : ∀ k,
      0 < heterogeneousParityArrivalMass arrival k := by
    intro k
    unfold heterogeneousParityArrivalMass
    exact Finset.sum_pos (fun b _hb ↦ harrival k b) Finset.univ_nonempty
  rcases exists_lexicographicDelay_minimizer_of_positive_primitives
      (logTail := fun _ _ ↦ tail) (arrival := arrival) (risk := priority)
      (inspectionProbability := inspectionProbability)
      (noninspectionPenalty := noninspectionPenalty)
      (excessCapacity := sla2026ExcessCapacity capacity admitted)
      hslope hcoefficient harrivalMass hexcess with ⟨level, _hlevel, hlex⟩
  let delay := finiteAllRequestParityDelay level priority inspectionProbability
    noninspectionPenalty
  have hdelay_zero : finiteAllRequestRangeObjective
      (finiteAllRequestDelayBurden priority inspectionProbability
        noninspectionPenalty delay) = 0 := by
    apply finiteAllRequestRangeObjective_eq_zero_of_constant
      (level := level)
    exact finiteAllRequestDelayBurden_parityDelay_eq_level level hslope
  have hsource_delay_zero :
      sla2026Equity arrival admitted priority noninspectionPenalty delay = 0 := by
    simpa [sla2026Equity, sla2026Cost, sla2026InspectionProbability,
      finiteAllRequestDelayBurden, inspectionProbability] using hdelay_zero
  refine ⟨delay, ?_, ?_⟩
  · refine ⟨?_, hsource_delay_zero, ?_⟩
    · simpa [sla2026Feasible, sla2026ExcessCapacity, delay,
        inspectionProbability] using hlex.1
    · intro other hother hother_zero
      have hother_lex_feasible : finiteMatrixReciprocalCapacityFeasible
          (fun _ _ ↦ tail) (sla2026ExcessCapacity capacity admitted) other := by
        simpa [sla2026Feasible, sla2026ExcessCapacity] using hother
      have hother_lex_zero : finiteAllRequestRangeObjective
          (finiteAllRequestDelayBurden priority inspectionProbability
            noninspectionPenalty other) = 0 := by
        simpa [sla2026Equity, sla2026Cost, sla2026InspectionProbability,
          finiteAllRequestDelayBurden, inspectionProbability] using hother_zero
      have hlex_efficiency := hlex.2.2 other hother_lex_feasible
        (hother_lex_zero.trans hdelay_zero.symm)
      simpa [sla2026Efficiency, sla2026Cost, sla2026InspectionProbability,
        finiteAllRequestArrivalWeightedEfficiency,
        finiteAllRequestDelayBurden, delay, inspectionProbability] using
          hlex_efficiency
  · have hlevels :=
      (finiteAllRequestRangeObjective_eq_zero_iff_exists_levels
        (finiteAllRequestDelayBurden priority inspectionProbability
          noninspectionPenalty delay)).1 hdelay_zero
    rcases hlevels with ⟨costLevel, hcostLevel⟩
    refine ⟨costLevel, ?_⟩
    intro k b
    simpa [sla2026Cost, sla2026InspectionProbability,
      finiteAllRequestDelayBurden, inspectionProbability] using hcostLevel k b

end

end LG24ServiceLevelAgreements
