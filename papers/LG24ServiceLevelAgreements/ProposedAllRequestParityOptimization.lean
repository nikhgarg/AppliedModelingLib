import LG24ServiceLevelAgreements.ProposedCategoryPooling
import LG24ServiceLevelAgreements.ProposedConditionalEquity
import Mathlib.Tactic

/-!
# Proposed theory: homogeneous-offset all-request parity optimization

This file closes the homogeneous non-inspection-offset special case in the
July 2026 revision memo.  The notation reuses the finite aggregators already
introduced in `ProposedCategoryPooling`:

* `categoryArrivalMass` is `Λ_k = ∑_b λ_kb`;
* `categoryTailRiskInspectionMass` is
  `R_k^π = ∑_b a_k r_kb π_kb`; and
* `allRequestParityRoot` is
  `B_all = ∑_k sqrt (Λ_k R_k^π)`.

When every cell in category `k` has the same fixed non-inspection offset
`q_k`, write the common burden as `u_k = q_k + v_k`.  The cellwise parity
capacity constraint then becomes the positive reciprocal program

`min ∑_k Λ_k v_k` subject to `∑_k R_k^π / v_k ≤ E`.

We certify its square-root minimizer and value, recover the memo's displayed
formula for `u_k`, and prove `B_all ≥ A`.  Hence the aligned-offset additive
price `(B_all² - A²) / E` is nonnegative.  All active-cell and denominator
assumptions are explicit.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Reduced homogeneous-offset endpoint -/

/--
The positive increment `v_k = u_k - q_k` at the homogeneous-offset
all-request parity endpoint.
-/
def homogeneousOffsetParityIncrement
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ)
    (arrival risk inspectionProbability : Category → Borough → ℝ)
    (excessCapacity : ℝ) : Category → ℝ :=
  squareRootAllocationDelay
    (categoryTailRiskInspectionMass tail risk inspectionProbability)
    (categoryArrivalMass arrival)
    excessCapacity

/-- Common category burden `u_k = q_k + v_k` at the parity endpoint. -/
def homogeneousOffsetParityLevel
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ)
    (arrival risk inspectionProbability : Category → Borough → ℝ)
    (offset : Category → ℝ) (excessCapacity : ℝ) : Category → ℝ :=
  fun k ↦ offset k + homogeneousOffsetParityIncrement
    tail arrival risk inspectionProbability excessCapacity k

/-- Positive arrivals give positive category arrival masses `Λ_k`. -/
theorem categoryArrivalMass_pos
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {arrival : Category → Borough → ℝ}
    (harrival : ∀ k b, 0 < arrival k b) (k : Category) :
    0 < categoryArrivalMass arrival k := by
  classical
  unfold categoryArrivalMass
  exact Finset.sum_pos (fun b _hb ↦ harrival k b) Finset.univ_nonempty

/-- Positive active primitives give positive parity coefficients `R_k^π`. -/
theorem categoryTailRiskInspectionMass_pos
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {risk inspectionProbability : Category → Borough → ℝ}
    (htail : ∀ k, 0 < tail k)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (k : Category) :
    0 < categoryTailRiskInspectionMass tail risk inspectionProbability k := by
  classical
  unfold categoryTailRiskInspectionMass
  exact Finset.sum_pos
    (fun b _hb ↦ mul_pos (mul_pos (htail k) (hrisk k b))
      (hprobability k b))
    Finset.univ_nonempty

/-- Every reduced parity increment is positive. -/
theorem homogeneousOffsetParityIncrement_pos
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hexcess : 0 < excessCapacity) :
    ∀ k, 0 < homogeneousOffsetParityIncrement
      tail arrival risk inspectionProbability excessCapacity k := by
  exact squareRootAllocationDelay_pos
    (fun k ↦ categoryTailRiskInspectionMass_pos
      htail hrisk hprobability k)
    (fun k ↦ categoryArrivalMass_pos harrival k)
    hexcess

/--
The reduced all-request parity endpoint is a certified global minimizer of
the positive reciprocal program in the revision memo.
-/
theorem homogeneousOffsetParityIncrement_isMinimizerOn
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hexcess : 0 < excessCapacity) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (reciprocalCapacityFeasible
        (categoryTailRiskInspectionMass tail risk inspectionProbability)
        excessCapacity)
      (servedDelayEfficiency (categoryArrivalMass arrival))
      (homogeneousOffsetParityIncrement
        tail arrival risk inspectionProbability excessCapacity) := by
  exact squareRootAllocationDelay_isMinimizerOn
    (fun k ↦ categoryTailRiskInspectionMass_pos
      htail hrisk hprobability k)
    (fun k ↦ categoryArrivalMass_pos harrival k)
    hexcess

/-- The generic aggregate root is exactly the memo's `B_all`. -/
theorem aggregateRootWeight_parityMass_eq_allRequestParityRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ)
    (arrival risk inspectionProbability : Category → Borough → ℝ) :
    aggregateRootWeight
        (categoryTailRiskInspectionMass tail risk inspectionProbability)
        (categoryArrivalMass arrival) =
      allRequestParityRoot tail arrival risk inspectionProbability := by
  classical
  unfold aggregateRootWeight allRequestParityRoot
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  ring

/--
The reduced endpoint attains the delay contribution `B_all² / E`.
-/
theorem servedDelayEfficiency_homogeneousOffsetParityIncrement
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hexcess : 0 < excessCapacity) :
    servedDelayEfficiency (categoryArrivalMass arrival)
        (homogeneousOffsetParityIncrement
          tail arrival risk inspectionProbability excessCapacity) =
      allRequestParityRoot tail arrival risk inspectionProbability ^ 2 /
        excessCapacity := by
  rw [homogeneousOffsetParityIncrement,
    servedDelayEfficiency_squareRootAllocationDelay
      (fun k ↦ categoryTailRiskInspectionMass_pos
        htail hrisk hprobability k)
      (fun k ↦ categoryArrivalMass_pos harrival k)
      hexcess,
    aggregateRootWeight_parityMass_eq_allRequestParityRoot]

/-- Memo closed form `v_k = (B_all/E) sqrt (R_k^π/Λ_k)`. -/
theorem homogeneousOffsetParityIncrement_eq_paperFormula
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hexcess : 0 < excessCapacity) (k : Category) :
    homogeneousOffsetParityIncrement
        tail arrival risk inspectionProbability excessCapacity k =
      allRequestParityRoot tail arrival risk inspectionProbability /
          excessCapacity *
        Real.sqrt
          (categoryTailRiskInspectionMass tail risk inspectionProbability k /
            categoryArrivalMass arrival k) := by
  let R := categoryTailRiskInspectionMass tail risk inspectionProbability k
  let L := categoryArrivalMass arrival k
  have hR : 0 < R := categoryTailRiskInspectionMass_pos
    htail hrisk hprobability k
  have hL : 0 < L := categoryArrivalMass_pos harrival k
  have hrootR : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hrootL : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  unfold homogeneousOffsetParityIncrement squareRootAllocationDelay
  change R * aggregateRootWeight
        (categoryTailRiskInspectionMass tail risk inspectionProbability)
        (categoryArrivalMass arrival) /
      (excessCapacity * Real.sqrt (R * L)) =
    allRequestParityRoot tail arrival risk inspectionProbability /
        excessCapacity * Real.sqrt (R / L)
  rw [aggregateRootWeight_parityMass_eq_allRequestParityRoot,
    Real.sqrt_mul hR.le, Real.sqrt_div hR.le]
  field_simp [hrootR, hrootL, hexcess.ne']
  rw [Real.sq_sqrt hR.le]
  ring

/-- Memo closed form for the common category burden `u_k`. -/
theorem homogeneousOffsetParityLevel_eq_paperFormula
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability : Category → Borough → ℝ}
    {offset : Category → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hexcess : 0 < excessCapacity) (k : Category) :
    homogeneousOffsetParityLevel tail arrival risk inspectionProbability
        offset excessCapacity k =
      offset k +
        allRequestParityRoot tail arrival risk inspectionProbability /
            excessCapacity *
          Real.sqrt
            (categoryTailRiskInspectionMass tail risk inspectionProbability k /
              categoryArrivalMass arrival k) := by
  unfold homogeneousOffsetParityLevel
  rw [homogeneousOffsetParityIncrement_eq_paperFormula
    htail harrival hrisk hprobability hexcess]

/--
The full parity efficiency tie-breaker is the fixed offset term plus
`B_all²/E`.
-/
theorem homogeneousOffsetParityLevel_objective_value
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability : Category → Borough → ℝ}
    {offset : Category → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hexcess : 0 < excessCapacity) :
    (∑ k, categoryArrivalMass arrival k *
        homogeneousOffsetParityLevel tail arrival risk inspectionProbability
          offset excessCapacity k) =
      (∑ k, categoryArrivalMass arrival k * offset k) +
        allRequestParityRoot tail arrival risk inspectionProbability ^ 2 /
          excessCapacity := by
  rw [← servedDelayEfficiency_homogeneousOffsetParityIncrement
    htail harrival hrisk hprobability hexcess]
  unfold homogeneousOffsetParityLevel servedDelayEfficiency
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/--
At the induced cell delays, the paper's full fixed-load efficiency objective
has value `∑_k Λ_k q_k + B_all²/E`.
-/
theorem finite_fixedLoadEfficiency_homogeneousOffsetParityEndpoint_value
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival admitted risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ}
    {offset : Category → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hadmitted : ∀ k b,
      admitted k b = inspectionProbability k b * arrival k b)
    (hexcess : 0 < excessCapacity) :
    (∑ k, ∑ b, fixedLoadEfficiencyCellCost
        (arrival k b) (admitted k b) (risk k b)
        (allRequestParityDelay
          (homogeneousOffsetParityLevel tail arrival risk inspectionProbability
            offset excessCapacity k)
          (risk k b) (inspectionProbability k b)
          (noninspectionPenalty k b))
        (noninspectionPenalty k b)) =
      (∑ k, categoryArrivalMass arrival k * offset k) +
        allRequestParityRoot tail arrival risk inspectionProbability ^ 2 /
          excessCapacity := by
  rw [finite_fixedLoadEfficiency_at_parity_eq_arrivalWeights
    arrival admitted risk inspectionProbability noninspectionPenalty
    (homogeneousOffsetParityLevel tail arrival risk inspectionProbability
      offset excessCapacity)
    hadmitted (fun k b ↦ (hrisk k b).ne')
    (fun k b ↦ (hprobability k b).ne')]
  exact homogeneousOffsetParityLevel_objective_value
    htail harrival hrisk hprobability hexcess

/--
Under the same homogeneous-offset identity, the Borough-separated efficient
endpoint has full value `∑_k Λ_k q_k + A²/E`.
-/
theorem finite_fixedLoadEfficiency_boroughSeparatedEndpoint_value
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival admitted risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ}
    {offset : Category → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmittedPos : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hadmitted : ∀ k b,
      admitted k b = inspectionProbability k b * arrival k b)
    (hoffset : ∀ k b,
      allRequestFixedOffset (risk k b) (inspectionProbability k b)
        (noninspectionPenalty k b) = offset k)
    (hexcess : 0 < excessCapacity) :
    (∑ k, ∑ b, fixedLoadEfficiencyCellCost
        (arrival k b) (admitted k b) (risk k b)
        (boroughSeparatedAllocationDelay
          tail admitted risk excessCapacity k b)
        (noninspectionPenalty k b)) =
      (∑ k, categoryArrivalMass arrival k * offset k) +
        boroughSeparatedRoot tail admitted risk ^ 2 /
          excessCapacity := by
  classical
  calc
    ∑ k, ∑ b, fixedLoadEfficiencyCellCost
        (arrival k b) (admitted k b) (risk k b)
        (boroughSeparatedAllocationDelay
          tail admitted risk excessCapacity k b)
        (noninspectionPenalty k b) =
        servedDelayEfficiency (boroughSeparatedWeight admitted risk)
            (fun i ↦ boroughSeparatedAllocationDelay
              tail admitted risk excessCapacity i.1 i.2) +
          ∑ k, categoryArrivalMass arrival k * offset k := by
      unfold fixedLoadEfficiencyCellCost servedDelayEfficiency
        boroughSeparatedWeight
      rw [Fintype.sum_prod_type]
      simp_rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _hk
      unfold categoryArrivalMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _hb
      rw [hadmitted]
      rw [← hoffset]
      all_goals (unfold allRequestFixedOffset; ring)
    _ = (∑ k, categoryArrivalMass arrival k * offset k) +
        boroughSeparatedRoot tail admitted risk ^ 2 /
          excessCapacity := by
      rw [servedDelayEfficiency_boroughSeparatedAllocationDelay
        htail hadmittedPos hrisk hexcess]
      ring

/-! ## Cellwise parity-capacity bridge -/

/--
With category-homogeneous offsets, cellwise parity substitution is exactly the
reduced category reciprocal-capacity expression.
-/
theorem finite_reciprocalCapacity_at_homogeneousParityLevel_eq_reduced
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (logTail risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ)
    (offset increment : Category → ℝ)
    (hoffset : ∀ k b,
      allRequestFixedOffset (risk k b) (inspectionProbability k b)
        (noninspectionPenalty k b) = offset k)
    (hrisk : ∀ k b, risk k b ≠ 0)
    (hprobability : ∀ k b, inspectionProbability k b ≠ 0)
    (hincrement : ∀ k, increment k ≠ 0) :
    (∑ k, ∑ b, logTail k b /
        allRequestParityDelay (offset k + increment k)
          (risk k b) (inspectionProbability k b)
          (noninspectionPenalty k b)) =
      reciprocalCapacityUse
        (fun k ↦ ∑ b, allRequestParityCapacityCoefficient
          (logTail k b) (risk k b) (inspectionProbability k b))
        increment := by
  rw [finite_reciprocalCapacity_at_parity_eq
    logTail risk inspectionProbability noninspectionPenalty
    (fun k ↦ offset k + increment k) hrisk hprobability]
  · unfold reciprocalCapacityUse
    apply Finset.sum_congr rfl
    intro k _hk
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [hoffset]
    ring
  · intro k b
    rw [hoffset]
    simpa using hincrement k

/--
The cellwise parity delays generated by the homogeneous-offset endpoint use
exactly all available excess capacity.
-/
theorem finite_reciprocalCapacity_homogeneousOffsetEndpoint_eq_excess
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ}
    {offset : Category → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hoffset : ∀ k b,
      allRequestFixedOffset (risk k b) (inspectionProbability k b)
        (noninspectionPenalty k b) = offset k)
    (hexcess : 0 < excessCapacity) :
    (∑ k, ∑ b, tail k /
        allRequestParityDelay
          (homogeneousOffsetParityLevel tail arrival risk inspectionProbability
            offset excessCapacity k)
          (risk k b) (inspectionProbability k b)
          (noninspectionPenalty k b)) = excessCapacity := by
  simp only [homogeneousOffsetParityLevel]
  rw [finite_reciprocalCapacity_at_homogeneousParityLevel_eq_reduced
    (fun k _b ↦ tail k) risk inspectionProbability noninspectionPenalty
    offset
    (homogeneousOffsetParityIncrement
      tail arrival risk inspectionProbability excessCapacity)
    hoffset (fun k b ↦ (hrisk k b).ne')
    (fun k b ↦ (hprobability k b).ne')
    (fun k ↦ (homogeneousOffsetParityIncrement_pos
      htail harrival hrisk hprobability hexcess k).ne')]
  change reciprocalCapacityUse
      (categoryTailRiskInspectionMass tail risk inspectionProbability)
      (homogeneousOffsetParityIncrement
        tail arrival risk inspectionProbability excessCapacity) = excessCapacity
  exact reciprocalCapacityUse_squareRootAllocationDelay
    (fun k ↦ categoryTailRiskInspectionMass_pos
      htail hrisk hprobability k)
    (fun k ↦ categoryArrivalMass_pos harrival k)
    hexcess

/-! ## `B_all ≥ A` and nonnegative aligned-offset price -/

/--
The Borough-separated efficiency root agrees with the transformed conditional
root in which inspection probability is absorbed into the tail coefficient.
-/
theorem boroughSeparatedRoot_eq_transformedConditionalEfficiencyRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → ℝ}
    {arrival admitted risk inspectionProbability : Category → Borough → ℝ}
    (hadmitted : ∀ k b,
      admitted k b = inspectionProbability k b * arrival k b) :
    boroughSeparatedRoot tail admitted risk =
      conditionalEfficiencyRootAggregate
        (fun k b ↦ tail k * inspectionProbability k b) arrival risk := by
  classical
  rw [conditionalEfficiencyRootAggregate_eq_nested]
  unfold boroughSeparatedRoot
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro b _hb
  rw [hadmitted]
  congr 1
  ring

/-- `B_all` is the corresponding transformed conditional parity root. -/
theorem allRequestParityRoot_eq_transformedConditionalEquityRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ)
    (arrival risk inspectionProbability : Category → Borough → ℝ) :
    allRequestParityRoot tail arrival risk inspectionProbability =
      conditionalEquityRootAggregate
        (fun k b ↦ tail k * inspectionProbability k b) arrival risk := by
  classical
  unfold allRequestParityRoot conditionalEquityRootAggregate
    aggregateRootWeight conditionalCategoryTailAggregate
    conditionalCategoryLoadAggregate categoryArrivalMass
    categoryTailRiskInspectionMass
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  · rw [mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro b _hb
    ring

/--
Categorywise Cauchy gives the memo's root ordering `A ≤ B_all`.
-/
theorem boroughSeparatedRoot_le_allRequestParityRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → ℝ}
    {arrival admitted risk inspectionProbability : Category → Borough → ℝ}
    (htail : ∀ k, 0 ≤ tail k)
    (harrival : ∀ k b, 0 ≤ arrival k b)
    (hrisk : ∀ k b, 0 ≤ risk k b)
    (hprobability : ∀ k b, 0 ≤ inspectionProbability k b)
    (hadmitted : ∀ k b,
      admitted k b = inspectionProbability k b * arrival k b) :
    boroughSeparatedRoot tail admitted risk ≤
      allRequestParityRoot tail arrival risk inspectionProbability := by
  rw [boroughSeparatedRoot_eq_transformedConditionalEfficiencyRoot hadmitted,
    allRequestParityRoot_eq_transformedConditionalEquityRoot]
  exact conditionalEfficiencyRootAggregate_le_conditionalEquityRootAggregate
    (fun k b ↦ mul_nonneg (htail k) (hprobability k b)) harrival hrisk

/-- The memo's aligned-offset price `(B_all²-A²)/E` is nonnegative. -/
theorem alignedOffsetAllRequestPrice_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → ℝ}
    {arrival admitted risk inspectionProbability : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 ≤ tail k)
    (harrival : ∀ k b, 0 ≤ arrival k b)
    (hrisk : ∀ k b, 0 ≤ risk k b)
    (hprobability : ∀ k b, 0 ≤ inspectionProbability k b)
    (hadmitted : ∀ k b,
      admitted k b = inspectionProbability k b * arrival k b)
    (hexcess : 0 < excessCapacity) :
    0 ≤ alignedOffsetAllRequestPrice
      (allRequestParityRoot tail arrival risk inspectionProbability)
      (boroughSeparatedRoot tail admitted risk) excessCapacity := by
  unfold alignedOffsetAllRequestPrice
  apply div_nonneg _ hexcess.le
  nlinarith [boroughSeparatedRoot_le_allRequestParityRoot
      htail harrival hrisk hprobability hadmitted,
    boroughSeparatedRoot_nonneg tail admitted risk,
    allRequestParityRoot_nonneg tail arrival risk inspectionProbability]

/--
Subtracting the efficient value `A²/E` from the homogeneous-offset parity
value gives exactly the memo's price formula.
-/
theorem homogeneousOffsetParityValue_sub_efficiencyValue_eq_price
    {parityRoot efficiencyRoot fixedOffset excessCapacity : ℝ}
    (hexcess : excessCapacity ≠ 0) :
    (fixedOffset + parityRoot ^ 2 / excessCapacity) -
        (fixedOffset + efficiencyRoot ^ 2 / excessCapacity) =
      alignedOffsetAllRequestPrice
        parityRoot efficiencyRoot excessCapacity := by
  unfold alignedOffsetAllRequestPrice
  field_simp [hexcess]
  ring

/--
Model-specific aligned-offset price formula: the full parity endpoint value
minus the full Borough-separated efficiency endpoint value is
`(B_all²-A²)/E`.
-/
theorem finite_alignedOffsetAllRequestPrice_formula
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival admitted risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ}
    {offset : Category → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hprobability : ∀ k b, 0 < inspectionProbability k b)
    (hadmitted : ∀ k b,
      admitted k b = inspectionProbability k b * arrival k b)
    (hoffset : ∀ k b,
      allRequestFixedOffset (risk k b) (inspectionProbability k b)
        (noninspectionPenalty k b) = offset k)
    (hexcess : 0 < excessCapacity) :
    (∑ k, ∑ b, fixedLoadEfficiencyCellCost
        (arrival k b) (admitted k b) (risk k b)
        (allRequestParityDelay
          (homogeneousOffsetParityLevel tail arrival risk inspectionProbability
            offset excessCapacity k)
          (risk k b) (inspectionProbability k b)
          (noninspectionPenalty k b))
        (noninspectionPenalty k b)) -
      (∑ k, ∑ b, fixedLoadEfficiencyCellCost
        (arrival k b) (admitted k b) (risk k b)
        (boroughSeparatedAllocationDelay
          tail admitted risk excessCapacity k b)
        (noninspectionPenalty k b)) =
      alignedOffsetAllRequestPrice
        (allRequestParityRoot tail arrival risk inspectionProbability)
        (boroughSeparatedRoot tail admitted risk) excessCapacity := by
  have hadmittedPos : ∀ k b, 0 < admitted k b := by
    intro k b
    rw [hadmitted]
    exact mul_pos (hprobability k b) (harrival k b)
  rw [finite_fixedLoadEfficiency_homogeneousOffsetParityEndpoint_value
      htail harrival hrisk hprobability hadmitted hexcess,
    finite_fixedLoadEfficiency_boroughSeparatedEndpoint_value
      htail hadmittedPos hrisk hadmitted hoffset hexcess]
  exact homogeneousOffsetParityValue_sub_efficiencyValue_eq_price hexcess.ne'

end

end LG24ServiceLevelAgreements
