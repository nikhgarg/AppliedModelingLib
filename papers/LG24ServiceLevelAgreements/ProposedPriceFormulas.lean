import LG24ServiceLevelAgreements.ProposedAllRequestParityOptimization
import LG24ServiceLevelAgreements.ProposedCentralization
import LG24ServiceLevelAgreements.EndogenousOneClass
import Mathlib.Tactic

/-!
# Proposed theory: exact endpoint disparity and primitive price formulas

This module verifies the remaining displayed formulas in the July 2026 GPT
revision snippets.  It connects the certified square-root efficiency endpoint
to the conditional and all-request burden expressions used inside the finite
max-minus-min objectives.  It then specializes the conditional price and the
category-pooling comparison to one category and two Boroughs, entirely in the
primitive parameters.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Cellwise burden formulas at the efficiency endpoint -/

/-- The displayed conditional burden at the square-root efficiency endpoint. -/
def conditionalBurdenAtEfficiency
    (root excessCapacity tail admitted risk : ℝ) : ℝ :=
  root / excessCapacity * Real.sqrt (tail * risk / admitted)

/--
The scalar square-root endpoint has exactly the paper's conditional burden
`(A/E) * sqrt (a*r/s)`.
-/
theorem risk_mul_fixedLoadEfficiencyDelay_eq_conditionalBurdenAtEfficiency
    {root excessCapacity tail admitted risk : ℝ}
    (htail : 0 < tail) (hadmitted : 0 < admitted) (hrisk : 0 < risk) :
    risk * fixedLoadEfficiencyDelay root excessCapacity tail admitted risk =
      conditionalBurdenAtEfficiency root excessCapacity tail admitted risk := by
  have htr : 0 < tail * risk := mul_pos htail hrisk
  have hsr : 0 < admitted * risk := mul_pos hadmitted hrisk
  have hsqrtTR : Real.sqrt (tail * risk) ≠ 0 := (Real.sqrt_pos.2 htr).ne'
  have hsqrtSR : Real.sqrt (admitted * risk) ≠ 0 := (Real.sqrt_pos.2 hsr).ne'
  have hsqrtS : Real.sqrt admitted ≠ 0 := (Real.sqrt_pos.2 hadmitted).ne'
  have hsqrtR : Real.sqrt risk ≠ 0 := (Real.sqrt_pos.2 hrisk).ne'
  have hinner :
      risk * Real.sqrt (tail / (admitted * risk)) =
        Real.sqrt (tail * risk / admitted) := by
    rw [Real.sqrt_div htail.le, Real.sqrt_div htr.le,
      Real.sqrt_mul hadmitted.le, Real.sqrt_mul htail.le]
    field_simp [hsqrtTR, hsqrtSR, hsqrtS, hsqrtR]
    nlinarith [Real.sq_sqrt hrisk.le]
  unfold fixedLoadEfficiencyDelay conditionalBurdenAtEfficiency
  calc
    risk * (root / excessCapacity * Real.sqrt (tail / (admitted * risk))) =
        root / excessCapacity *
          (risk * Real.sqrt (tail / (admitted * risk))) := by ring
    _ = root / excessCapacity * Real.sqrt (tail * risk / admitted) := by
      rw [hinner]

/-- The generic certified square-root allocation is the paper's cell formula. -/
theorem squareRootAllocationDelay_eq_fixedLoadEfficiencyDelay
    {Cell : Type*} [Fintype Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (i : Cell) :
    squareRootAllocationDelay tail weight excessCapacity i =
      fixedLoadEfficiencyDelay (aggregateRootWeight tail weight)
        excessCapacity (tail i) 1 (weight i) := by
  have htailSqrt : Real.sqrt (tail i) ≠ 0 :=
    (Real.sqrt_pos.2 (htail i)).ne'
  have hweightSqrt : Real.sqrt (weight i) ≠ 0 :=
    (Real.sqrt_pos.2 (hweight i)).ne'
  have hquot :
      tail i / Real.sqrt (tail i * weight i) =
        Real.sqrt (tail i / weight i) := by
    rw [Real.sqrt_mul (htail i).le, Real.sqrt_div (htail i).le]
    field_simp [htailSqrt, hweightSqrt]
    nlinarith [Real.sq_sqrt (htail i).le]
  unfold squareRootAllocationDelay fixedLoadEfficiencyDelay
  simp only [one_mul]
  calc
    tail i * aggregateRootWeight tail weight /
        (excessCapacity * Real.sqrt (tail i * weight i)) =
      aggregateRootWeight tail weight / excessCapacity *
        (tail i / Real.sqrt (tail i * weight i)) := by ring
    _ = aggregateRootWeight tail weight / excessCapacity *
        Real.sqrt (tail i / weight i) := by rw [hquot]

/-- The certified finite efficiency endpoint agrees cellwise with the paper formula. -/
theorem conditionalEfficiencyEndpoint_eq_fixedLoadEfficiencyDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b) (k : Category) (b : Borough) :
    conditionalEfficiencyEndpoint tail admitted risk excessCapacity (k, b) =
      fixedLoadEfficiencyDelay
        (conditionalEfficiencyRootAggregate tail admitted risk)
        excessCapacity (tail k b) (admitted k b) (risk k b) := by
  unfold conditionalEfficiencyEndpoint conditionalEfficiencyRootAggregate
  rw [squareRootAllocationDelay_eq_fixedLoadEfficiencyDelay
    (fun i ↦ htail i.1 i.2)
    (fun i ↦ mul_pos (hadmitted i.1 i.2) (hrisk i.1 i.2)) (k, b)]
  unfold fixedLoadEfficiencyDelay
  have hadmittedRisk : 0 < admitted k b * risk k b :=
    mul_pos (hadmitted k b) (hrisk k b)
  rw [Real.sqrt_div (htail k b).le]
  simp only [one_mul]
  rw [Real.sqrt_div (htail k b).le]

/-- The displayed all-request burden at the square-root efficiency endpoint. -/
def allRequestBurdenAtEfficiency
    (root excessCapacity tail arrival admitted risk penalty : ℝ) : ℝ :=
  allRequestFixedOffset risk (admitted / arrival) penalty +
    root / excessCapacity * Real.sqrt (tail * admitted * risk) / arrival

/--
The scalar all-request burden is the non-inspection offset plus the paper's
`(A/E) * sqrt (a*s*r) / lambda` term.
-/
theorem fixedLoadAllRequestBurden_efficiencyDelay_eq_allRequestBurdenAtEfficiency
    {root excessCapacity tail arrival admitted risk penalty : ℝ}
    (htail : 0 < tail) (hadmitted : 0 < admitted) (hrisk : 0 < risk) :
    fixedLoadAllRequestBurden arrival admitted risk
        (fixedLoadEfficiencyDelay root excessCapacity tail admitted risk) penalty =
      allRequestBurdenAtEfficiency root excessCapacity tail arrival admitted risk
        penalty := by
  rw [fixedLoadAllRequestBurden, allRequestBurden_eq_fixedOffset_add_slope_mul_delay]
  unfold fixedLoadInspectionProbability allRequestDelaySlope
    allRequestBurdenAtEfficiency
  rw [show risk * (admitted / arrival) *
      fixedLoadEfficiencyDelay root excessCapacity tail admitted risk =
      admitted / arrival *
        (risk * fixedLoadEfficiencyDelay root excessCapacity tail admitted risk) by ring,
    risk_mul_fixedLoadEfficiencyDelay_eq_conditionalBurdenAtEfficiency
      htail hadmitted hrisk]
  unfold conditionalBurdenAtEfficiency
  have htr : 0 ≤ tail * risk := (mul_pos htail hrisk).le
  have hs : 0 ≤ admitted := hadmitted.le
  rw [Real.sqrt_div htr]
  have hsqrtTriple : Real.sqrt (tail * admitted * risk) =
      Real.sqrt admitted * Real.sqrt (tail * risk) := by
    rw [show tail * admitted * risk = admitted * (tail * risk) by ring,
      Real.sqrt_mul hs]
  rw [hsqrtTriple]
  have hsqrtS : Real.sqrt admitted ≠ 0 := (Real.sqrt_pos.2 hadmitted).ne'
  have hadmitted_div_sqrt : admitted / Real.sqrt admitted = Real.sqrt admitted := by
    apply (div_eq_iff hsqrtS).2
    nlinarith [Real.sq_sqrt hadmitted.le]
  congr 1
  calc
    admitted / arrival *
        (root / excessCapacity * (Real.sqrt (tail * risk) / Real.sqrt admitted)) =
      root / excessCapacity * Real.sqrt (tail * risk) / arrival *
        (admitted / Real.sqrt admitted) := by ring
    _ = root / excessCapacity * Real.sqrt (tail * risk) / arrival *
        Real.sqrt admitted := by rw [hadmitted_div_sqrt]
    _ = root / excessCapacity *
        (Real.sqrt admitted * Real.sqrt (tail * risk)) / arrival := by ring

/-! ## Exact finite disparity-at-efficiency formulas -/

/-- The finite conditional disparity formula in Equation `price-efficiency-delta-cond`. -/
def finiteConditionalDisparityAtEfficiencyFormula
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (root excessCapacity : ℝ)
    (tail admitted risk : Category → Borough → ℝ) : ℝ :=
  ∑ k, finiteBoroughRange (fun b ↦
    conditionalBurdenAtEfficiency root excessCapacity
      (tail k b) (admitted k b) (risk k b))

/--
The conditional range of the explicit efficiency delays is exactly the finite
max-minus-min expression displayed in the revision snippet.
-/
theorem finiteConditionalEquityRangeObjective_efficiencyDelay_eq_formula
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {root excessCapacity : ℝ}
    {tail admitted risk : Category → Borough → ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b) :
    finiteConditionalEquityRangeObjective risk
        (fun k b ↦ fixedLoadEfficiencyDelay root excessCapacity
          (tail k b) (admitted k b) (risk k b)) =
      finiteConditionalDisparityAtEfficiencyFormula root excessCapacity
        tail admitted risk := by
  classical
  unfold finiteConditionalEquityRangeObjective
    finiteConditionalDisparityAtEfficiencyFormula
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  funext b
  exact risk_mul_fixedLoadEfficiencyDelay_eq_conditionalBurdenAtEfficiency
    (htail k b) (hadmitted k b) (hrisk k b)

/-- Equation `price-efficiency-delta-cond` for the certified finite endpoint. -/
theorem finiteConditionalEquityRangeObjective_conditionalEfficiencyEndpoint_eq_formula
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail admitted risk : Category → Borough → ℝ} {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b) :
    finiteConditionalEquityRangeObjective risk
        (fun k b ↦ conditionalEfficiencyEndpoint
          tail admitted risk excessCapacity (k, b)) =
      finiteConditionalDisparityAtEfficiencyFormula
        (conditionalEfficiencyRootAggregate tail admitted risk)
        excessCapacity tail admitted risk := by
  rw [show (fun k b ↦ conditionalEfficiencyEndpoint
      tail admitted risk excessCapacity (k, b)) =
      (fun k b ↦ fixedLoadEfficiencyDelay
        (conditionalEfficiencyRootAggregate tail admitted risk)
        excessCapacity (tail k b) (admitted k b) (risk k b)) by
    funext k b
    exact conditionalEfficiencyEndpoint_eq_fixedLoadEfficiencyDelay
      htail hadmitted hrisk k b]
  exact finiteConditionalEquityRangeObjective_efficiencyDelay_eq_formula
    htail hadmitted hrisk

/-- The finite all-request disparity formula in Equation `price-efficiency-delta-all`. -/
def finiteAllRequestDisparityAtEfficiencyFormula
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (root excessCapacity : ℝ)
    (tail arrival admitted risk penalty : Category → Borough → ℝ) : ℝ :=
  finiteAllRequestRangeObjective (fun k b ↦
    allRequestBurdenAtEfficiency root excessCapacity
      (tail k b) (arrival k b) (admitted k b) (risk k b) (penalty k b))

/--
The all-request range of the explicit efficiency delays is exactly the finite
offset-plus-square-root expression displayed in the revision snippet.
-/
theorem finiteAllRequestRangeObjective_efficiencyDelay_eq_formula
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {root excessCapacity : ℝ}
    {tail arrival admitted risk penalty : Category → Borough → ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b) :
    finiteAllRequestRangeObjective (fun k b ↦
        fixedLoadAllRequestBurden (arrival k b) (admitted k b) (risk k b)
          (fixedLoadEfficiencyDelay root excessCapacity
            (tail k b) (admitted k b) (risk k b)) (penalty k b)) =
      finiteAllRequestDisparityAtEfficiencyFormula root excessCapacity
        tail arrival admitted risk penalty := by
  classical
  unfold finiteAllRequestDisparityAtEfficiencyFormula
    finiteAllRequestRangeObjective
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  funext b
  exact fixedLoadAllRequestBurden_efficiencyDelay_eq_allRequestBurdenAtEfficiency
    (htail k b) (hadmitted k b) (hrisk k b)

/-- Equation `price-efficiency-delta-all` for the certified finite endpoint. -/
theorem finiteAllRequestRangeObjective_conditionalEfficiencyEndpoint_eq_formula
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival admitted risk penalty : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k b, 0 < tail k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b) :
    finiteAllRequestRangeObjective (fun k b ↦
        fixedLoadAllRequestBurden (arrival k b) (admitted k b) (risk k b)
          (conditionalEfficiencyEndpoint tail admitted risk excessCapacity (k, b))
          (penalty k b)) =
      finiteAllRequestDisparityAtEfficiencyFormula
        (conditionalEfficiencyRootAggregate tail admitted risk)
        excessCapacity tail arrival admitted risk penalty := by
  rw [show (fun k b ↦
      fixedLoadAllRequestBurden (arrival k b) (admitted k b) (risk k b)
        (conditionalEfficiencyEndpoint tail admitted risk excessCapacity (k, b))
        (penalty k b)) =
      (fun k b ↦
        fixedLoadAllRequestBurden (arrival k b) (admitted k b) (risk k b)
          (fixedLoadEfficiencyDelay
            (conditionalEfficiencyRootAggregate tail admitted risk)
            excessCapacity (tail k b) (admitted k b) (risk k b))
          (penalty k b)) by
    funext k b
    rw [conditionalEfficiencyEndpoint_eq_fixedLoadEfficiencyDelay
      htail hadmitted hrisk k b]]
  exact finiteAllRequestRangeObjective_efficiencyDelay_eq_formula
    htail hadmitted hrisk

/-! ## Two-Borough source shapes -/

/-- The arbitrary-finite range specializes to the ordinary two-point range on `Bool`. -/
theorem finiteBoroughRange_bool_eq_twoBoroughRange (x : Bool → ℝ) :
    finiteBoroughRange x = twoBoroughRange (x false) (x true) := by
  classical
  simp [finiteBoroughRange, twoBoroughRange, max_comm, min_comm]

/-- For two Boroughs, the conditional formula is a sum of absolute differences. -/
theorem finiteConditionalDisparityAtEfficiencyFormula_bool_eq_sum_abs
    {Category : Type*} [Fintype Category]
    (root excessCapacity : ℝ)
    (tail admitted risk : Category → Bool → ℝ) :
    finiteConditionalDisparityAtEfficiencyFormula root excessCapacity
        tail admitted risk =
      ∑ k, |conditionalBurdenAtEfficiency root excessCapacity
          (tail k false) (admitted k false) (risk k false) -
        conditionalBurdenAtEfficiency root excessCapacity
          (tail k true) (admitted k true) (risk k true)| := by
  classical
  unfold finiteConditionalDisparityAtEfficiencyFormula
  apply Finset.sum_congr rfl
  intro k _hk
  rw [finiteBoroughRange_bool_eq_twoBoroughRange, twoBoroughRange_eq_abs_sub]

/-- For two Boroughs, the all-request formula is a sum of absolute differences. -/
theorem finiteAllRequestDisparityAtEfficiencyFormula_bool_eq_sum_abs
    {Category : Type*} [Fintype Category]
    (root excessCapacity : ℝ)
    (tail arrival admitted risk penalty : Category → Bool → ℝ) :
    finiteAllRequestDisparityAtEfficiencyFormula root excessCapacity
        tail arrival admitted risk penalty =
      ∑ k, |allRequestBurdenAtEfficiency root excessCapacity
          (tail k false) (arrival k false) (admitted k false)
          (risk k false) (penalty k false) -
        allRequestBurdenAtEfficiency root excessCapacity
          (tail k true) (arrival k true) (admitted k true)
          (risk k true) (penalty k true)| := by
  classical
  unfold finiteAllRequestDisparityAtEfficiencyFormula
    finiteAllRequestRangeObjective
  apply Finset.sum_congr rfl
  intro k _hk
  rw [finiteBoroughRange_bool_eq_twoBoroughRange, twoBoroughRange_eq_abs_sub]

/-! ## One-category, two-Borough primitive price identity -/

/-- Cell root `sqrt (a*s*r)` specialized to the common-tail two-Borough model. -/
def twoBoroughPrimitiveEfficiencyRoot
    (tail admitted₁ admitted₂ risk₁ risk₂ : ℝ) : ℝ :=
  Real.sqrt (tail * admitted₁ * risk₁) +
    Real.sqrt (tail * admitted₂ * risk₂)

/-- Conditional-parity root `sqrt (a*(r₁+r₂)*(s₁+s₂))`. -/
def twoBoroughPrimitiveConditionalParityRoot
    (tail admitted₁ admitted₂ risk₁ risk₂ : ℝ) : ℝ :=
  Real.sqrt (tail * (risk₁ + risk₂) * (admitted₁ + admitted₂))

/-- Primitive specialization of the conditional additive price. -/
def twoBoroughPrimitiveConditionalPrice
    (tail excessCapacity admitted₁ admitted₂ risk₁ risk₂ : ℝ) : ℝ :=
  conditionalEquityAdditivePrice
    (twoBoroughPrimitiveEfficiencyRoot tail admitted₁ admitted₂ risk₁ risk₂)
    (twoBoroughPrimitiveConditionalParityRoot tail admitted₁ admitted₂ risk₁ risk₂)
    excessCapacity

/--
Exact primitive identity
`PoE = a/E * (sqrt (r₁*s₂) - sqrt (r₂*s₁))²`.
-/
theorem twoBoroughPrimitiveConditionalPrice_eq
    {tail excessCapacity admitted₁ admitted₂ risk₁ risk₂ : ℝ}
    (htail : 0 ≤ tail) (hadmitted₁ : 0 ≤ admitted₁)
    (hadmitted₂ : 0 ≤ admitted₂)
    (hrisk₁ : 0 ≤ risk₁) (hrisk₂ : 0 ≤ risk₂) :
    twoBoroughPrimitiveConditionalPrice tail excessCapacity
        admitted₁ admitted₂ risk₁ risk₂ =
      tail / excessCapacity *
        (Real.sqrt (risk₁ * admitted₂) -
          Real.sqrt (risk₂ * admitted₁)) ^ 2 := by
  unfold twoBoroughPrimitiveConditionalPrice conditionalEquityAdditivePrice
    twoBoroughPrimitiveEfficiencyRoot twoBoroughPrimitiveConditionalParityRoot
  have hsumR : 0 ≤ risk₁ + risk₂ := add_nonneg hrisk₁ hrisk₂
  have hsumS : 0 ≤ admitted₁ + admitted₂ :=
    add_nonneg hadmitted₁ hadmitted₂
  have h11 : 0 ≤ admitted₁ * risk₁ := mul_nonneg hadmitted₁ hrisk₁
  have h22 : 0 ≤ admitted₂ * risk₂ := mul_nonneg hadmitted₂ hrisk₂
  have h12 : 0 ≤ risk₁ * admitted₂ := mul_nonneg hrisk₁ hadmitted₂
  have h21 : 0 ≤ risk₂ * admitted₁ := mul_nonneg hrisk₂ hadmitted₁
  have hB : 0 ≤ tail * (risk₁ + risk₂) * (admitted₁ + admitted₂) :=
    mul_nonneg (mul_nonneg htail hsumR) hsumS
  have hA₁ : 0 ≤ tail * admitted₁ * risk₁ :=
    mul_nonneg (mul_nonneg htail hadmitted₁) hrisk₁
  have hA₂ : 0 ≤ tail * admitted₂ * risk₂ :=
    mul_nonneg (mul_nonneg htail hadmitted₂) hrisk₂
  have hcross :
      Real.sqrt (tail * admitted₁ * risk₁) *
          Real.sqrt (tail * admitted₂ * risk₂) =
        tail * (Real.sqrt (risk₁ * admitted₂) *
          Real.sqrt (risk₂ * admitted₁)) := by
    rw [← Real.sqrt_mul hA₁, ← Real.sqrt_mul h12]
    have harg :
        (tail * admitted₁ * risk₁) * (tail * admitted₂ * risk₂) =
          tail ^ 2 * ((risk₁ * admitted₂) * (risk₂ * admitted₁)) := by
      ring
    rw [harg, Real.sqrt_mul (sq_nonneg tail), Real.sqrt_sq htail,
      Real.sqrt_mul h12]
  have hAsq :
      (Real.sqrt (tail * admitted₁ * risk₁) +
          Real.sqrt (tail * admitted₂ * risk₂)) ^ 2 =
        tail * admitted₁ * risk₁ + tail * admitted₂ * risk₂ +
          2 * tail * (Real.sqrt (risk₁ * admitted₂) *
            Real.sqrt (risk₂ * admitted₁)) := by
    calc
      (Real.sqrt (tail * admitted₁ * risk₁) +
          Real.sqrt (tail * admitted₂ * risk₂)) ^ 2 =
          Real.sqrt (tail * admitted₁ * risk₁) ^ 2 +
            Real.sqrt (tail * admitted₂ * risk₂) ^ 2 +
            2 * (Real.sqrt (tail * admitted₁ * risk₁) *
              Real.sqrt (tail * admitted₂ * risk₂)) := by ring
      _ = tail * admitted₁ * risk₁ + tail * admitted₂ * risk₂ +
          2 * tail * (Real.sqrt (risk₁ * admitted₂) *
            Real.sqrt (risk₂ * admitted₁)) := by
        rw [Real.sq_sqrt hA₁, Real.sq_sqrt hA₂, hcross]
        ring
  have htargetSq :
      (Real.sqrt (risk₁ * admitted₂) -
          Real.sqrt (risk₂ * admitted₁)) ^ 2 =
        risk₁ * admitted₂ + risk₂ * admitted₁ -
          2 * (Real.sqrt (risk₁ * admitted₂) *
            Real.sqrt (risk₂ * admitted₁)) := by
    calc
      (Real.sqrt (risk₁ * admitted₂) -
          Real.sqrt (risk₂ * admitted₁)) ^ 2 =
          Real.sqrt (risk₁ * admitted₂) ^ 2 +
            Real.sqrt (risk₂ * admitted₁) ^ 2 -
            2 * (Real.sqrt (risk₁ * admitted₂) *
              Real.sqrt (risk₂ * admitted₁)) := by ring
      _ = risk₁ * admitted₂ + risk₂ * admitted₁ -
          2 * (Real.sqrt (risk₁ * admitted₂) *
            Real.sqrt (risk₂ * admitted₁)) := by
        rw [Real.sq_sqrt h12, Real.sq_sqrt h21]
  rw [Real.sq_sqrt hB, hAsq, htargetSq]
  ring

/-- Under positive primitives, the conditional price vanishes exactly at balance. -/
theorem twoBoroughPrimitiveConditionalPrice_eq_zero_iff
    {tail excessCapacity admitted₁ admitted₂ risk₁ risk₂ : ℝ}
    (htail : 0 < tail) (hexcess : 0 < excessCapacity)
    (hadmitted₁ : 0 < admitted₁) (hadmitted₂ : 0 < admitted₂)
    (hrisk₁ : 0 < risk₁) (hrisk₂ : 0 < risk₂) :
    twoBoroughPrimitiveConditionalPrice tail excessCapacity
        admitted₁ admitted₂ risk₁ risk₂ = 0 ↔
      risk₁ * admitted₂ = risk₂ * admitted₁ := by
  rw [twoBoroughPrimitiveConditionalPrice_eq htail.le
    hadmitted₁.le hadmitted₂.le hrisk₁.le hrisk₂.le]
  have hscale : tail / excessCapacity ≠ 0 := div_ne_zero htail.ne' hexcess.ne'
  constructor
  · intro h
    have hsq : (Real.sqrt (risk₁ * admitted₂) -
        Real.sqrt (risk₂ * admitted₁)) ^ 2 = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hscale
    have hsqrt : Real.sqrt (risk₁ * admitted₂) =
        Real.sqrt (risk₂ * admitted₁) := by nlinarith
    nlinarith [Real.sq_sqrt (mul_pos hrisk₁ hadmitted₂).le,
      Real.sq_sqrt (mul_pos hrisk₂ hadmitted₁).le]
  · intro hbalance
    rw [hbalance]
    ring

/-- The same balance condition in the ratio form stated in the prose. -/
theorem twoBoroughPrimitiveConditionalPrice_eq_zero_iff_ratio_eq
    {tail excessCapacity admitted₁ admitted₂ risk₁ risk₂ : ℝ}
    (htail : 0 < tail) (hexcess : 0 < excessCapacity)
    (hadmitted₁ : 0 < admitted₁) (hadmitted₂ : 0 < admitted₂)
    (hrisk₁ : 0 < risk₁) (hrisk₂ : 0 < risk₂) :
    twoBoroughPrimitiveConditionalPrice tail excessCapacity
        admitted₁ admitted₂ risk₁ risk₂ = 0 ↔
      risk₁ / admitted₁ = risk₂ / admitted₂ := by
  rw [twoBoroughPrimitiveConditionalPrice_eq_zero_iff htail hexcess
    hadmitted₁ hadmitted₂ hrisk₁ hrisk₂]
  field_simp [hadmitted₁.ne', hadmitted₂.ne']

/-! ## End-to-end primitive pooling threshold -/

/-- Two-Borough category-pooling gain in the common-tail primitive model. -/
def twoBoroughPrimitiveCategoryPoolingGain
    (tail excessCapacity admitted₁ admitted₂ risk₁ risk₂ : ℝ) : ℝ :=
  2 * tail * Real.sqrt (admitted₁ * risk₁ * admitted₂ * risk₂) /
    excessCapacity

/--
The price dominates the category-pooling gain exactly when the primitive
cross-ratio lies outside the squared threshold interval.
-/
theorem twoBoroughPrimitive_price_ge_pooling_iff_ratio_outside
    {tail excessCapacity admitted₁ admitted₂ risk₁ risk₂ : ℝ}
    (htail : 0 < tail) (hexcess : 0 < excessCapacity)
    (hadmitted₁ : 0 < admitted₁) (hadmitted₂ : 0 < admitted₂)
    (hrisk₁ : 0 < risk₁) (hrisk₂ : 0 < risk₂) :
    twoBoroughPrimitiveCategoryPoolingGain tail excessCapacity
        admitted₁ admitted₂ risk₁ risk₂ ≤
      twoBoroughPrimitiveConditionalPrice tail excessCapacity
        admitted₁ admitted₂ risk₁ risk₂ ↔
      risk₁ * admitted₂ / (risk₂ * admitted₁) ≤
          (2 - Real.sqrt 3) ^ 2 ∨
        (2 + Real.sqrt 3) ^ 2 ≤
          risk₁ * admitted₂ / (risk₂ * admitted₁) := by
  let x := risk₁ * admitted₂
  let y := risk₂ * admitted₁
  let q := Real.sqrt (x / y)
  have hx : 0 < x := mul_pos hrisk₁ hadmitted₂
  have hy : 0 < y := mul_pos hrisk₂ hadmitted₁
  have hxy : 0 < x * y := mul_pos hx hy
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hsqrtY : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hq_sq : q ^ 2 = x / y := by
    exact Real.sq_sqrt (div_nonneg hx.le hy.le)
  have hq_mul_sqrtY : q * Real.sqrt y = Real.sqrt x := by
    dsimp [q]
    rw [Real.sqrt_div hx.le]
    field_simp [hsqrtY]
  have hsqrtXY : Real.sqrt (x * y) = q * y := by
    rw [Real.sqrt_mul hx.le, ← hq_mul_sqrtY]
    nlinarith [Real.sq_sqrt hy.le]
  have hdiffSq :
      (Real.sqrt x - Real.sqrt y) ^ 2 = (q - 1) ^ 2 * y := by
    rw [← hq_mul_sqrtY]
    nlinarith [Real.sq_sqrt hy.le]
  have hprimitiveProduct :
      admitted₁ * risk₁ * admitted₂ * risk₂ = x * y := by
    dsimp [x, y]
    ring
  have hpool :
      twoBoroughPrimitiveCategoryPoolingGain tail excessCapacity
          admitted₁ admitted₂ risk₁ risk₂ =
        tail / excessCapacity * (2 * Real.sqrt (x * y)) := by
    unfold twoBoroughPrimitiveCategoryPoolingGain
    rw [hprimitiveProduct]
    ring
  have hscale : 0 < tail / excessCapacity := div_pos htail hexcess
  rw [hpool,
    twoBoroughPrimitiveConditionalPrice_eq htail.le
      hadmitted₁.le hadmitted₂.le hrisk₁.le hrisk₂.le,
    show risk₁ * admitted₂ = x by rfl,
    show risk₂ * admitted₁ = y by rfl,
    (mul_le_mul_iff_of_pos_left hscale)]
  rw [hsqrtXY, hdiffSq]
  have hnormalized :
      2 * (q * y) ≤ (q - 1) ^ 2 * y ↔ 2 * q ≤ (q - 1) ^ 2 := by
    constructor
    · intro h
      apply (mul_le_mul_iff_of_pos_right hy).1
      nlinarith [h]
    · intro h
      have h' := (mul_le_mul_iff_of_pos_right hy).2 h
      nlinarith [h']
  rw [hnormalized, twoBorough_categoryPooling_ratio_threshold]
  have hsqrt3_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hsqrt3_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hlow : 0 ≤ 2 - Real.sqrt (3 : ℝ) := by
    nlinarith
  have hupp : 0 ≤ 2 + Real.sqrt (3 : ℝ) := by positivity
  have hlowSq :
      q ≤ 2 - Real.sqrt (3 : ℝ) ↔
        q ^ 2 ≤ (2 - Real.sqrt 3) ^ 2 := by
    exact (sq_le_sq₀ hq hlow).symm
  have huppSq :
      2 + Real.sqrt (3 : ℝ) ≤ q ↔
        (2 + Real.sqrt 3) ^ 2 ≤ q ^ 2 := by
    exact (sq_le_sq₀ hupp hq).symm
  rw [hlowSq, huppSq, hq_sq]

end

end LG24ServiceLevelAgreements
