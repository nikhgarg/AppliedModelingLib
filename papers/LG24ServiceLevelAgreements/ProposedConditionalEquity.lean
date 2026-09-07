import LG24ServiceLevelAgreements.ProposedOptimization
import AppliedModelingLib.Foundations.Optimization.Certificate
import Mathlib.Tactic

/-!
# Proposed theory: finite conditional-equity endpoint and prices

This file formalizes the finite conditional-SLA equity formulas proposed in
the July 2026 revision documents.  All category--Borough cells are assumed
active: tail parameters, admitted loads, and risk weights are strictly
positive.  Categories with zero admitted load are therefore deliberately
outside this endpoint and must be handled by the paper's non-inspection or
minimum-service diagnostics.

The main construction reduces risk-weighted parity in every category to the
generic reciprocal-allocation problem from `ProposedOptimization`.  It proves
the parity endpoint, its exact capacity use and served-delay value, the
nonnegative `B^2-A^2` price formula, the two relative-price identities, and
the exact algebraic comparison with the category-pooling gain.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Root aggregates -/

/-- The cell-level root aggregate `A` at a fixed admitted-load vector. -/
def conditionalEfficiencyRootAggregate
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail admitted risk : Category → Borough → ℝ) : ℝ :=
  aggregateRootWeight
    (fun i : Category × Borough ↦ tail i.1 i.2)
    (fun i : Category × Borough ↦ admitted i.1 i.2 * risk i.1 i.2)

/-- Cell-level efficiency endpoint used to define the `A^2 / E` benchmark. -/
def conditionalEfficiencyEndpoint
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail admitted risk : Category → Borough → ℝ) (excessCapacity : ℝ) :
    Category × Borough → ℝ :=
  squareRootAllocationDelay
    (fun i : Category × Borough ↦ tail i.1 i.2)
    (fun i : Category × Borough ↦ admitted i.1 i.2 * risk i.1 i.2)
    excessCapacity

/-- The category coefficient `R_k = ∑_b a_{k,b} r_{k,b}`. -/
def conditionalCategoryTailAggregate
    {Category Borough : Type*} [Fintype Borough]
    (tail risk : Category → Borough → ℝ) (k : Category) : ℝ :=
  ∑ b, tail k b * risk k b

/-- The category admitted load `S_k = ∑_b s_{k,b}`. -/
def conditionalCategoryLoadAggregate
    {Category Borough : Type*} [Fintype Borough]
    (admitted : Category → Borough → ℝ) (k : Category) : ℝ :=
  ∑ b, admitted k b

/-- The parity root aggregate `B = ∑_k √(R_k S_k)`. -/
def conditionalEquityRootAggregate
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail admitted risk : Category → Borough → ℝ) : ℝ :=
  aggregateRootWeight
    (conditionalCategoryTailAggregate tail risk)
    (conditionalCategoryLoadAggregate admitted)

/-- The product-indexed definition of `A` is the expected nested cell sum. -/
theorem conditionalEfficiencyRootAggregate_eq_nested
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail admitted risk : Category → Borough → ℝ) :
    conditionalEfficiencyRootAggregate tail admitted risk =
      ∑ k, ∑ b, Real.sqrt (tail k b * (admitted k b * risk k b)) := by
  classical
  simp only [conditionalEfficiencyRootAggregate, aggregateRootWeight,
    Fintype.sum_prod_type]

/-- The fixed-load efficient endpoint has served-delay value `A^2 / E`. -/
theorem conditionalEfficiencyEndpoint_servedValue
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    servedDelayEfficiency
        (fun i : Category × Borough ↦ admitted i.1 i.2 * risk i.1 i.2)
        (conditionalEfficiencyEndpoint tail admitted risk excessCapacity) =
      conditionalEfficiencyRootAggregate tail admitted risk ^ 2 /
        excessCapacity := by
  exact servedDelayEfficiency_squareRootAllocationDelay
    (fun i ↦ htail i.1 i.2)
    (fun i ↦ mul_pos (hadmitted i.1 i.2) (hrisk i.1 i.2))
    hexcess

/-- Positive active cells give positive category tail coefficients. -/
theorem conditionalCategoryTailAggregate_pos
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {tail risk : Category → Borough → ℝ}
    (htail : ∀ k b, 0 < tail k b) (hrisk : ∀ k b, 0 < risk k b) (k : Category) :
    0 < conditionalCategoryTailAggregate tail risk k := by
  classical
  unfold conditionalCategoryTailAggregate
  exact Finset.sum_pos
    (fun b _hb ↦ mul_pos (htail k b) (hrisk k b))
    Finset.univ_nonempty

/-- Positive active cells give positive category admitted loads. -/
theorem conditionalCategoryLoadAggregate_pos
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {admitted : Category → Borough → ℝ}
    (hadmitted : ∀ k b, 0 < admitted k b) (k : Category) :
    0 < conditionalCategoryLoadAggregate admitted k := by
  classical
  unfold conditionalCategoryLoadAggregate
  exact Finset.sum_pos (fun b _hb ↦ hadmitted k b) Finset.univ_nonempty

/-- Every square-root aggregate is nonnegative. -/
theorem aggregateRootWeight_nonneg
    {Cell : Type*} [Fintype Cell] (tail weight : Cell → ℝ) :
    0 ≤ aggregateRootWeight tail weight := by
  classical
  unfold aggregateRootWeight
  exact Finset.sum_nonneg fun i _hi ↦ Real.sqrt_nonneg _

/--
Categorywise Cauchy: the cell roots in one category are at most
`√((∑ a r)(∑ s))`.
-/
theorem conditionalEfficiencyCategoryRoot_le
    {Category Borough : Type*} [Fintype Borough]
    {tail admitted risk : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hadmitted : ∀ k b, 0 ≤ admitted k b)
    (hrisk : ∀ k b, 0 ≤ risk k b) (k : Category) :
    aggregateRootWeight (tail k) (fun b ↦ admitted k b * risk k b) ≤
      Real.sqrt
        (conditionalCategoryTailAggregate tail risk k *
          conditionalCategoryLoadAggregate admitted k) := by
  classical
  have hcs := aggregateRootWeight_sq_le_use_mul_efficiency
    (tail := fun b ↦ tail k b * risk k b)
    (weight := admitted k) (delay := fun _ ↦ (1 : ℝ))
    (fun b ↦ mul_nonneg (htail k b) (hrisk k b))
    (hadmitted k) (fun _ ↦ zero_lt_one)
  have hrootEq :
      aggregateRootWeight (fun b ↦ tail k b * risk k b) (admitted k) =
        aggregateRootWeight (tail k) (fun b ↦ admitted k b * risk k b) := by
    unfold aggregateRootWeight
    apply Finset.sum_congr rfl
    intro b _hb
    congr 1
    ring
  rw [hrootEq] at hcs
  simp only [reciprocalCapacityUse, servedDelayEfficiency, div_one, mul_one] at hcs
  change
    aggregateRootWeight (tail k) (fun b ↦ admitted k b * risk k b) ^ 2 ≤
      conditionalCategoryTailAggregate tail risk k *
        conditionalCategoryLoadAggregate admitted k at hcs
  have hR : 0 ≤ conditionalCategoryTailAggregate tail risk k := by
    unfold conditionalCategoryTailAggregate
    exact Finset.sum_nonneg fun b _hb ↦ mul_nonneg (htail k b) (hrisk k b)
  have hS : 0 ≤ conditionalCategoryLoadAggregate admitted k := by
    unfold conditionalCategoryLoadAggregate
    exact Finset.sum_nonneg fun b _hb ↦ hadmitted k b
  have hA :
      0 ≤ aggregateRootWeight (tail k) (fun b ↦ admitted k b * risk k b) :=
    aggregateRootWeight_nonneg _ _
  have hsqrt :
      Real.sqrt
          (conditionalCategoryTailAggregate tail risk k *
            conditionalCategoryLoadAggregate admitted k) ^ 2 =
        conditionalCategoryTailAggregate tail risk k *
          conditionalCategoryLoadAggregate admitted k :=
    Real.sq_sqrt (mul_nonneg hR hS)
  have hsqrtNonneg :
      0 ≤ Real.sqrt
        (conditionalCategoryTailAggregate tail risk k *
          conditionalCategoryLoadAggregate admitted k) := Real.sqrt_nonneg _
  nlinarith

/-- The conditional-parity root aggregate dominates the efficiency aggregate. -/
theorem conditionalEfficiencyRootAggregate_le_conditionalEquityRootAggregate
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail admitted risk : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hadmitted : ∀ k b, 0 ≤ admitted k b)
    (hrisk : ∀ k b, 0 ≤ risk k b) :
    conditionalEfficiencyRootAggregate tail admitted risk ≤
      conditionalEquityRootAggregate tail admitted risk := by
  classical
  rw [conditionalEfficiencyRootAggregate_eq_nested]
  unfold conditionalEquityRootAggregate aggregateRootWeight
  apply Finset.sum_le_sum
  intro k _hk
  simpa only [aggregateRootWeight] using
    conditionalEfficiencyCategoryRoot_le htail hadmitted hrisk k

/-! ## Conditional-equity parity endpoint -/

/-- The category parity level `u_k`, represented by the generic root allocation. -/
def conditionalCategoryParityLevel
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail admitted risk : Category → Borough → ℝ) (excessCapacity : ℝ) :
    Category → ℝ :=
  squareRootAllocationDelay
    (conditionalCategoryTailAggregate tail risk)
    (conditionalCategoryLoadAggregate admitted)
    excessCapacity

/-- Recover cell delays from category parity levels by dividing by risk. -/
def conditionalParityDelay
    {Category Borough : Type*}
    (risk : Category → Borough → ℝ) (level : Category → ℝ) :
    Category → Borough → ℝ :=
  fun k b ↦ level k / risk k b

/-- The full finite conditional-equity endpoint. -/
def conditionalEquityEndpoint
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail admitted risk : Category → Borough → ℝ) (excessCapacity : ℝ) :
    Category → Borough → ℝ :=
  conditionalParityDelay risk
    (conditionalCategoryParityLevel tail admitted risk excessCapacity)

/-- The reduced category-level endpoint is a certified global minimizer. -/
theorem conditionalCategoryParityLevel_isMinimizerOn
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (reciprocalCapacityFeasible
        (conditionalCategoryTailAggregate tail risk) excessCapacity)
      (servedDelayEfficiency (conditionalCategoryLoadAggregate admitted))
      (conditionalCategoryParityLevel tail admitted risk excessCapacity) := by
  exact squareRootAllocationDelay_isMinimizerOn
    (fun k ↦ conditionalCategoryTailAggregate_pos htail hrisk k)
    (fun k ↦ conditionalCategoryLoadAggregate_pos hadmitted k)
    hexcess

/-- Memo closed form for the category parity level. -/
theorem conditionalCategoryParityLevel_eq_paperFormula
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) (k : Category) :
    conditionalCategoryParityLevel tail admitted risk excessCapacity k =
      conditionalEquityRootAggregate tail admitted risk / excessCapacity *
        Real.sqrt
          (conditionalCategoryTailAggregate tail risk k /
            conditionalCategoryLoadAggregate admitted k) := by
  let R := conditionalCategoryTailAggregate tail risk k
  let S := conditionalCategoryLoadAggregate admitted k
  have hR : 0 < R := conditionalCategoryTailAggregate_pos htail hrisk k
  have hS : 0 < S := conditionalCategoryLoadAggregate_pos hadmitted k
  have hrootR : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hrootS : Real.sqrt S ≠ 0 := (Real.sqrt_pos.2 hS).ne'
  unfold conditionalCategoryParityLevel squareRootAllocationDelay
  change R * conditionalEquityRootAggregate tail admitted risk /
      (excessCapacity * Real.sqrt (R * S)) =
    conditionalEquityRootAggregate tail admitted risk / excessCapacity *
      Real.sqrt (R / S)
  rw [Real.sqrt_mul hR.le, Real.sqrt_div hR.le]
  field_simp [hrootR, hrootS, hexcess.ne']
  rw [Real.sq_sqrt hR.le]
  ring

/-- Memo closed form for every cell delay at the parity endpoint. -/
theorem conditionalEquityEndpoint_eq_paperFormula
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) (k : Category) (b : Borough) :
    conditionalEquityEndpoint tail admitted risk excessCapacity k b =
      conditionalEquityRootAggregate tail admitted risk / excessCapacity *
        (1 / risk k b) *
        Real.sqrt
          (conditionalCategoryTailAggregate tail risk k /
            conditionalCategoryLoadAggregate admitted k) := by
  unfold conditionalEquityEndpoint conditionalParityDelay
  rw [conditionalCategoryParityLevel_eq_paperFormula
    htail hadmitted hrisk hexcess k]
  field_simp [(hrisk k b).ne']

/-- Every recovered cell delay is strictly positive. -/
theorem conditionalEquityEndpoint_pos
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    ∀ k b, 0 < conditionalEquityEndpoint tail admitted risk excessCapacity k b := by
  intro k b
  unfold conditionalEquityEndpoint conditionalParityDelay
  exact div_pos
    (squareRootAllocationDelay_pos
      (fun j ↦ conditionalCategoryTailAggregate_pos htail hrisk j)
      (fun j ↦ conditionalCategoryLoadAggregate_pos hadmitted j)
      hexcess k)
    (hrisk k b)

/-- The endpoint equalizes risk-weighted conditional delay within category. -/
theorem conditionalEquityEndpoint_risk_mul_eq_level
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (hrisk : ∀ k b, risk k b ≠ 0) (k : Category) (b : Borough) :
    risk k b * conditionalEquityEndpoint tail admitted risk excessCapacity k b =
      conditionalCategoryParityLevel tail admitted risk excessCapacity k := by
  unfold conditionalEquityEndpoint conditionalParityDelay
  field_simp [hrisk k b]

/-- Substitution of parity delays reduces cell capacity use to category use. -/
theorem conditionalParityDelay_capacityUse_eq
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail risk : Category → Borough → ℝ) (level : Category → ℝ)
    (hrisk : ∀ k b, risk k b ≠ 0) (hlevel : ∀ k, level k ≠ 0) :
    (∑ k, ∑ b, tail k b / conditionalParityDelay risk level k b) =
      reciprocalCapacityUse (conditionalCategoryTailAggregate tail risk) level := by
  classical
  unfold conditionalParityDelay reciprocalCapacityUse
    conditionalCategoryTailAggregate
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    ∑ b, tail k b / (level k / risk k b) =
        ∑ b, (tail k b * risk k b) / level k := by
      apply Finset.sum_congr rfl
      intro b _hb
      field_simp [hrisk k b, hlevel k]
    _ = (∑ b, tail k b * risk k b) / level k := by
      rw [Finset.sum_div]

/-- The finite conditional-equity endpoint uses exactly all excess capacity. -/
theorem conditionalEquityEndpoint_capacityUse
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    (∑ k, ∑ b, tail k b /
      conditionalEquityEndpoint tail admitted risk excessCapacity k b) =
        excessCapacity := by
  unfold conditionalEquityEndpoint
  rw [conditionalParityDelay_capacityUse_eq tail risk
    (conditionalCategoryParityLevel tail admitted risk excessCapacity)
    (fun k b ↦ (hrisk k b).ne')]
  · exact reciprocalCapacityUse_squareRootAllocationDelay
      (fun k ↦ conditionalCategoryTailAggregate_pos htail hrisk k)
      (fun k ↦ conditionalCategoryLoadAggregate_pos hadmitted k)
      hexcess
  · intro k
    exact (squareRootAllocationDelay_pos
      (fun j ↦ conditionalCategoryTailAggregate_pos htail hrisk j)
      (fun j ↦ conditionalCategoryLoadAggregate_pos hadmitted j)
      hexcess k).ne'

/-- Cell served-delay efficiency reduces exactly to the category objective. -/
theorem conditionalParityDelay_servedEfficiency_eq
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (admitted risk : Category → Borough → ℝ) (level : Category → ℝ)
    (hrisk : ∀ k b, risk k b ≠ 0) :
    (∑ k, ∑ b,
      (admitted k b * risk k b) * conditionalParityDelay risk level k b) =
        servedDelayEfficiency (conditionalCategoryLoadAggregate admitted) level := by
  classical
  unfold conditionalParityDelay servedDelayEfficiency
    conditionalCategoryLoadAggregate
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    ∑ b, (admitted k b * risk k b) * (level k / risk k b) =
        ∑ b, admitted k b * level k := by
      apply Finset.sum_congr rfl
      intro b _hb
      field_simp [hrisk k b]
    _ = (∑ b, admitted k b) * level k := by
      rw [Finset.sum_mul]

/-- The conditional-equity endpoint attains served-delay value `B^2 / E`. -/
theorem conditionalEquityEndpoint_servedValue
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    (∑ k, ∑ b, (admitted k b * risk k b) *
      conditionalEquityEndpoint tail admitted risk excessCapacity k b) =
        conditionalEquityRootAggregate tail admitted risk ^ 2 / excessCapacity := by
  unfold conditionalEquityEndpoint
  rw [conditionalParityDelay_servedEfficiency_eq admitted risk
    (conditionalCategoryParityLevel tail admitted risk excessCapacity)
    (fun k b ↦ (hrisk k b).ne')]
  exact servedDelayEfficiency_squareRootAllocationDelay
    (fun k ↦ conditionalCategoryTailAggregate_pos htail hrisk k)
    (fun k ↦ conditionalCategoryLoadAggregate_pos hadmitted k)
    hexcess

/-- Sum of within-category risk-weighted conditional-delay ranges. -/
def finiteConditionalEquityRangeObjective
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (risk delay : Category → Borough → ℝ) : ℝ :=
  ∑ k, finiteBoroughRange (fun b ↦ risk k b * delay k b)

/-- Conditional equity ranges are nonnegative. -/
theorem finiteConditionalEquityRangeObjective_nonneg
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (risk delay : Category → Borough → ℝ) :
    0 ≤ finiteConditionalEquityRangeObjective risk delay := by
  unfold finiteConditionalEquityRangeObjective
  exact Finset.sum_nonneg fun k _hk ↦ finiteBoroughRange_nonneg _

/-- The endpoint has the minimum possible conditional range, namely zero. -/
theorem conditionalEquityEndpoint_range_eq_zero
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (hrisk : ∀ k b, risk k b ≠ 0) :
    finiteConditionalEquityRangeObjective risk
      (conditionalEquityEndpoint tail admitted risk excessCapacity) = 0 := by
  classical
  unfold finiteConditionalEquityRangeObjective
  apply Finset.sum_eq_zero
  intro k _hk
  apply finiteBoroughRange_eq_zero_of_constant _
    (conditionalCategoryParityLevel tail admitted risk excessCapacity k)
  intro b
  exact conditionalEquityEndpoint_risk_mul_eq_level hrisk k b

/-! ## Additive and relative prices -/

/-- Additive price of conditional equity in served-delay units. -/
def conditionalEquityAdditivePrice
    (efficiencyRoot equityRoot excessCapacity : ℝ) : ℝ :=
  (equityRoot ^ 2 - efficiencyRoot ^ 2) / excessCapacity

/-- The additive price is exactly equitable served value minus efficient value. -/
theorem conditionalEquityAdditivePrice_eq_value_sub
    {efficiencyRoot equityRoot excessCapacity : ℝ}
    (hexcess : excessCapacity ≠ 0) :
    conditionalEquityAdditivePrice efficiencyRoot equityRoot excessCapacity =
      equityRoot ^ 2 / excessCapacity -
        efficiencyRoot ^ 2 / excessCapacity := by
  unfold conditionalEquityAdditivePrice
  field_simp [hexcess]

/-- A fixed non-inspection term cancels from the full endpoint difference. -/
theorem conditionalEquityAdditivePrice_eq_fullValue_sub
    {efficiencyRoot equityRoot excessCapacity noninspectionCost : ℝ}
    (hexcess : excessCapacity ≠ 0) :
    conditionalEquityAdditivePrice efficiencyRoot equityRoot excessCapacity =
      (equityRoot ^ 2 / excessCapacity + noninspectionCost) -
        (efficiencyRoot ^ 2 / excessCapacity + noninspectionCost) := by
  rw [conditionalEquityAdditivePrice_eq_value_sub hexcess]
  ring

/-- `B ≥ A ≥ 0` and positive excess capacity make the price nonnegative. -/
theorem conditionalEquityAdditivePrice_nonneg
    {efficiencyRoot equityRoot excessCapacity : ℝ}
    (hA : 0 ≤ efficiencyRoot) (hAB : efficiencyRoot ≤ equityRoot)
    (hexcess : 0 < excessCapacity) :
    0 ≤ conditionalEquityAdditivePrice
      efficiencyRoot equityRoot excessCapacity := by
  unfold conditionalEquityAdditivePrice
  exact div_nonneg
    (sub_nonneg.mpr ((sq_le_sq₀ hA (hA.trans hAB)).2 hAB))
    hexcess.le

/-- The finite model's conditional-equity price is nonnegative. -/
theorem finiteConditionalEquityAdditivePrice_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hadmitted : ∀ k b, 0 ≤ admitted k b)
    (hrisk : ∀ k b, 0 ≤ risk k b)
    (hexcess : 0 < excessCapacity) :
    0 ≤ conditionalEquityAdditivePrice
      (conditionalEfficiencyRootAggregate tail admitted risk)
      (conditionalEquityRootAggregate tail admitted risk)
      excessCapacity := by
  apply conditionalEquityAdditivePrice_nonneg
    (aggregateRootWeight_nonneg _ _)
    (conditionalEfficiencyRootAggregate_le_conditionalEquityRootAggregate
      htail hadmitted hrisk)
    hexcess

/-- Served-load relative price: `1 - A^2 / B^2`. -/
theorem conditionalEquity_servedRelativePrice_eq
    {efficiencyRoot equityRoot excessCapacity : ℝ}
    (hB : equityRoot ≠ 0) (hE : excessCapacity ≠ 0) :
    (conditionalEquityAdditivePrice efficiencyRoot equityRoot excessCapacity) /
        (equityRoot ^ 2 / excessCapacity) =
      1 - efficiencyRoot ^ 2 / equityRoot ^ 2 := by
  unfold conditionalEquityAdditivePrice
  field_simp [hB, hE]

/-- Relative price when the common non-inspection term is in the denominator. -/
theorem conditionalEquity_fullRelativePrice_eq
    {efficiencyRoot equityRoot excessCapacity noninspectionCost : ℝ}
    (hE : excessCapacity ≠ 0)
    (hdenom : equityRoot ^ 2 + excessCapacity * noninspectionCost ≠ 0) :
    (conditionalEquityAdditivePrice efficiencyRoot equityRoot excessCapacity) /
        (equityRoot ^ 2 / excessCapacity + noninspectionCost) =
      (equityRoot ^ 2 - efficiencyRoot ^ 2) /
        (equityRoot ^ 2 + excessCapacity * noninspectionCost) := by
  unfold conditionalEquityAdditivePrice
  field_simp [hE, hdenom]

/-! ## Comparison with category pooling -/

/-- Served-load gain from replacing root `A` by a pooled root. -/
def categoryPoolingServedGain
    (efficiencyRoot pooledRoot excessCapacity : ℝ) : ℝ :=
  (efficiencyRoot ^ 2 - pooledRoot ^ 2) / excessCapacity

/-- Exact finite comparison condition; there is no universal ordering. -/
theorem conditionalEquityPrice_gt_categoryPoolingGain_iff
    {efficiencyRoot equityRoot pooledRoot excessCapacity : ℝ}
    (hexcess : 0 < excessCapacity) :
    conditionalEquityAdditivePrice efficiencyRoot equityRoot excessCapacity >
        categoryPoolingServedGain efficiencyRoot pooledRoot excessCapacity ↔
      2 * efficiencyRoot ^ 2 < equityRoot ^ 2 + pooledRoot ^ 2 := by
  unfold conditionalEquityAdditivePrice categoryPoolingServedGain
  constructor
  · intro h
    have h' := (div_lt_div_iff_of_pos_right hexcess).1 h
    nlinarith
  · intro h
    apply (div_lt_div_iff_of_pos_right hexcess).2
    nlinarith

/-- Weak comparison counterpart of the strict condition. -/
theorem conditionalEquityPrice_ge_categoryPoolingGain_iff
    {efficiencyRoot equityRoot pooledRoot excessCapacity : ℝ}
    (hexcess : 0 < excessCapacity) :
    categoryPoolingServedGain efficiencyRoot pooledRoot excessCapacity ≤
        conditionalEquityAdditivePrice efficiencyRoot equityRoot excessCapacity ↔
      2 * efficiencyRoot ^ 2 ≤ equityRoot ^ 2 + pooledRoot ^ 2 := by
  unfold conditionalEquityAdditivePrice categoryPoolingServedGain
  rw [div_le_div_iff_of_pos_right hexcess]
  ring_nf
  constructor <;> intro h <;> nlinarith

end

end LG24ServiceLevelAgreements
