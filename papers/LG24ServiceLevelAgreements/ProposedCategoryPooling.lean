import LG24ServiceLevelAgreements.ProposedAlignment
import Mathlib.Tactic

/-!
# Proposed theory: finite category-pooling comparison

This file formalizes the general finite category-pooling benchmark introduced
in the July 2026 revision memo.  It distinguishes three square-root
aggregators:

* the Borough-separated efficiency root `A`;
* the category-pooled efficiency root `A_pool`; and
* the all-request parity root `B_all`.

The pooled root never exceeds the separated root under nonnegative primitives,
so its analytical fixed-load gain is nonnegative.  The constructive alignment
gap from `ProposedAlignment` gives a conservative certificate that pooling is
at least as valuable as exact all-request equity.  When exact endpoint value
identities are available, the comparison reduces to the memo's single
root-square inequality.

This analytical category-pooling benchmark is not identified with the dynamic
City-budget simulator.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## The three finite square-root aggregators -/

/-- Risk-weighted admitted load in one category after pooling Borough cells. -/
def categoryPooledWeight
    {Category Borough : Type*} [Fintype Borough]
    (admitted risk : Category → Borough → ℝ) (k : Category) : ℝ :=
  ∑ b, admitted k b * risk k b

/--
The Borough-separated root
`A = ∑_k ∑_b sqrt (a_k s_kb r_kb)`.
-/
def boroughSeparatedRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, Real.sqrt (tail k * (admitted k b * risk k b))

/--
The category-pooled root
`A_pool = ∑_k sqrt (a_k ∑_b s_kb r_kb)`.
-/
def categoryPooledRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ) : ℝ :=
  aggregateRootWeight tail (categoryPooledWeight admitted risk)

/-- Arrival mass in one category. -/
def categoryArrivalMass
    {Category Borough : Type*} [Fintype Borough]
    (arrival : Category → Borough → ℝ) (k : Category) : ℝ :=
  ∑ b, arrival k b

/-- Tail-risk-inspection mass `R_k^π = ∑_b a_k r_kb π_kb`. -/
def categoryTailRiskInspectionMass
    {Category Borough : Type*} [Fintype Borough]
    (tail : Category → ℝ) (risk inspectionProbability : Category → Borough → ℝ)
    (k : Category) : ℝ :=
  ∑ b, tail k * risk k b * inspectionProbability k b

/--
The all-request parity root
`B_all = ∑_k sqrt ((∑_b λ_kb) (∑_b a_k r_kb π_kb))`.
-/
def allRequestParityRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ)
    (arrival risk inspectionProbability : Category → Borough → ℝ) : ℝ :=
  ∑ k, Real.sqrt
    (categoryArrivalMass arrival k *
      categoryTailRiskInspectionMass tail risk inspectionProbability k)

/-- Analytical gain from pooling Borough cells within category. -/
def analyticalCategoryPoolingGain
    (separatedRoot pooledRoot excessCapacity : ℝ) : ℝ :=
  (separatedRoot ^ 2 - pooledRoot ^ 2) / excessCapacity

/-- The exact aligned-offset all-request price formula from the memo. -/
def alignedOffsetAllRequestPrice
    (parityRoot separatedRoot excessCapacity : ℝ) : ℝ :=
  (parityRoot ^ 2 - separatedRoot ^ 2) / excessCapacity

/-! ## Pooled endpoint and value -/

/-- Common category tail parameter flattened to category--Borough cells. -/
def boroughSeparatedTail
    {Category Borough : Type*} (tail : Category → ℝ) : Category × Borough → ℝ :=
  fun i ↦ tail i.1

/-- Risk-weighted admitted load flattened to category--Borough cells. -/
def boroughSeparatedWeight
    {Category Borough : Type*} (admitted risk : Category → Borough → ℝ) :
    Category × Borough → ℝ :=
  fun i ↦ admitted i.1 i.2 * risk i.1 i.2

/-- The square-root endpoint before pooling Borough cells within category. -/
def boroughSeparatedAllocationDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ)
    (excessCapacity : ℝ) : Category → Borough → ℝ :=
  fun k b ↦ squareRootAllocationDelay
    (boroughSeparatedTail (Borough := Borough) tail)
    (boroughSeparatedWeight admitted risk) excessCapacity (k, b)

/-- The explicit nested `A` equals the generic finite-cell aggregate root. -/
theorem boroughSeparatedRoot_eq_aggregateRootWeight
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ) :
    boroughSeparatedRoot tail admitted risk =
      aggregateRootWeight
        (boroughSeparatedTail (Borough := Borough) tail)
        (boroughSeparatedWeight admitted risk) := by
  classical
  unfold boroughSeparatedRoot aggregateRootWeight boroughSeparatedTail
    boroughSeparatedWeight
  rw [Fintype.sum_prod_type]

/-- The Borough-separated endpoint is reciprocal-capacity feasible. -/
theorem boroughSeparatedAllocationDelay_feasible
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    reciprocalCapacityFeasible
      (boroughSeparatedTail (Borough := Borough) tail) excessCapacity
      (fun i ↦ boroughSeparatedAllocationDelay
        tail admitted risk excessCapacity i.1 i.2) := by
  exact squareRootAllocationDelay_feasible
    (fun i ↦ htail i.1)
    (fun i ↦ mul_pos (hadmitted i.1 i.2) (hrisk i.1 i.2)) hexcess

/-- The Borough-separated endpoint minimizes separated served-delay efficiency. -/
theorem boroughSeparatedAllocationDelay_isMinimizerOn
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (reciprocalCapacityFeasible
        (boroughSeparatedTail (Borough := Borough) tail) excessCapacity)
      (servedDelayEfficiency (boroughSeparatedWeight admitted risk))
      (fun i ↦ boroughSeparatedAllocationDelay
        tail admitted risk excessCapacity i.1 i.2) := by
  exact squareRootAllocationDelay_isMinimizerOn
    (fun i ↦ htail i.1)
    (fun i ↦ mul_pos (hadmitted i.1 i.2) (hrisk i.1 i.2)) hexcess

/-- The Borough-separated endpoint value is `A² / E`. -/
theorem servedDelayEfficiency_boroughSeparatedAllocationDelay
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    servedDelayEfficiency (boroughSeparatedWeight admitted risk)
        (fun i ↦ boroughSeparatedAllocationDelay
          tail admitted risk excessCapacity i.1 i.2) =
      boroughSeparatedRoot tail admitted risk ^ 2 / excessCapacity := by
  rw [boroughSeparatedRoot_eq_aggregateRootWeight]
  exact servedDelayEfficiency_squareRootAllocationDelay
    (fun i ↦ htail i.1)
    (fun i ↦ mul_pos (hadmitted i.1 i.2) (hrisk i.1 i.2)) hexcess

/-- The memo's square-root SLA endpoint for the category-pooled benchmark. -/
def categoryPooledAllocationDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ)
    (excessCapacity : ℝ) : Category → ℝ :=
  squareRootAllocationDelay tail (categoryPooledWeight admitted risk) excessCapacity

/-- Positive cell loads make every pooled category weight positive. -/
theorem categoryPooledWeight_pos
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {admitted risk : Category → Borough → ℝ}
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b) :
    ∀ k, 0 < categoryPooledWeight admitted risk k := by
  intro k
  let b : Borough := Classical.choice (inferInstance : Nonempty Borough)
  have hterm : 0 < admitted k b * risk k b := mul_pos (hadmitted k b) (hrisk k b)
  have hle : admitted k b * risk k b ≤ ∑ j, admitted k j * risk k j := by
    exact Finset.single_le_sum
      (fun j _hj ↦ (mul_pos (hadmitted k j) (hrisk k j)).le)
      (Finset.mem_univ b)
  exact lt_of_lt_of_le hterm hle

/-- The pooled square-root endpoint is reciprocal-capacity feasible. -/
theorem categoryPooledAllocationDelay_feasible
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    reciprocalCapacityFeasible tail excessCapacity
      (categoryPooledAllocationDelay tail admitted risk excessCapacity) := by
  exact squareRootAllocationDelay_feasible htail
    (categoryPooledWeight_pos hadmitted hrisk) hexcess

/-- The pooled square-root endpoint minimizes pooled served-delay efficiency. -/
theorem categoryPooledAllocationDelay_isMinimizerOn
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (reciprocalCapacityFeasible tail excessCapacity)
      (servedDelayEfficiency (categoryPooledWeight admitted risk))
      (categoryPooledAllocationDelay tail admitted risk excessCapacity) := by
  exact squareRootAllocationDelay_isMinimizerOn htail
    (categoryPooledWeight_pos hadmitted hrisk) hexcess

/-- The pooled endpoint value is `A_pool² / E`. -/
theorem servedDelayEfficiency_categoryPooledAllocationDelay
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    servedDelayEfficiency (categoryPooledWeight admitted risk)
        (categoryPooledAllocationDelay tail admitted risk excessCapacity) =
      categoryPooledRoot tail admitted risk ^ 2 / excessCapacity := by
  exact servedDelayEfficiency_squareRootAllocationDelay htail
    (categoryPooledWeight_pos hadmitted hrisk) hexcess

/--
The difference between the two proved endpoint values is exactly the memo's
analytical category-pooling gain `(A² - A_pool²) / E`.
-/
theorem boroughSeparatedValue_sub_categoryPooledValue_eq_gain
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    servedDelayEfficiency (boroughSeparatedWeight admitted risk)
        (fun i ↦ boroughSeparatedAllocationDelay
          tail admitted risk excessCapacity i.1 i.2) -
      servedDelayEfficiency (categoryPooledWeight admitted risk)
        (categoryPooledAllocationDelay tail admitted risk excessCapacity) =
      analyticalCategoryPoolingGain
        (boroughSeparatedRoot tail admitted risk)
        (categoryPooledRoot tail admitted risk) excessCapacity := by
  rw [servedDelayEfficiency_boroughSeparatedAllocationDelay
      htail hadmitted hrisk hexcess,
    servedDelayEfficiency_categoryPooledAllocationDelay
      htail hadmitted hrisk hexcess]
  unfold analyticalCategoryPoolingGain
  ring

/-! ## Root ordering and nonnegative pooling gain -/

/-- Square root is subadditive on two nonnegative real inputs. -/
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))).2
  have hxy : 0 ≤ Real.sqrt x * Real.sqrt y :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  linarith

/-- Finite square-root subadditivity. -/
theorem sqrt_sum_le_sum_sqrt
    {Index : Type*} (s : Finset Index) (x : Index → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    Real.sqrt (∑ i ∈ s, x i) ≤ ∑ i ∈ s, Real.sqrt (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (sqrt_add_le_add_sqrt (hx i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))).trans
        (add_le_add (le_refl _)
          (ih (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))))

/-- Every one of the memo's three roots is nonnegative. -/
theorem boroughSeparatedRoot_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ) :
    0 ≤ boroughSeparatedRoot tail admitted risk := by
  exact Finset.sum_nonneg fun k _hk ↦
    Finset.sum_nonneg fun b _hb ↦ Real.sqrt_nonneg _

theorem categoryPooledRoot_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (admitted risk : Category → Borough → ℝ) :
    0 ≤ categoryPooledRoot tail admitted risk := by
  unfold categoryPooledRoot aggregateRootWeight
  exact Finset.sum_nonneg fun k _hk ↦ Real.sqrt_nonneg _

theorem allRequestParityRoot_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ)
    (arrival risk inspectionProbability : Category → Borough → ℝ) :
    0 ≤ allRequestParityRoot tail arrival risk inspectionProbability := by
  unfold allRequestParityRoot
  exact Finset.sum_nonneg fun k _hk ↦ Real.sqrt_nonneg _

/-- Pooling within category weakly lowers the finite square-root aggregator. -/
theorem categoryPooledRoot_le_boroughSeparatedRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    (htail : ∀ k, 0 ≤ tail k)
    (hadmitted : ∀ k b, 0 ≤ admitted k b)
    (hrisk : ∀ k b, 0 ≤ risk k b) :
    categoryPooledRoot tail admitted risk ≤
      boroughSeparatedRoot tail admitted risk := by
  classical
  unfold categoryPooledRoot aggregateRootWeight boroughSeparatedRoot
    categoryPooledWeight
  apply Finset.sum_le_sum
  intro k _hk
  rw [Finset.mul_sum]
  exact sqrt_sum_le_sum_sqrt Finset.univ
    (fun b ↦ tail k * (admitted k b * risk k b))
    (fun b _hb ↦ mul_nonneg (htail k)
      (mul_nonneg (hadmitted k b) (hrisk k b)))

/-- The analytical category-pooling gain is nonnegative. -/
theorem analyticalCategoryPoolingGain_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → ℝ} {admitted risk : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 ≤ tail k)
    (hadmitted : ∀ k b, 0 ≤ admitted k b)
    (hrisk : ∀ k b, 0 ≤ risk k b)
    (hexcess : 0 < excessCapacity) :
    0 ≤ analyticalCategoryPoolingGain
      (boroughSeparatedRoot tail admitted risk)
      (categoryPooledRoot tail admitted risk) excessCapacity := by
  unfold analyticalCategoryPoolingGain
  apply div_nonneg _ hexcess.le
  nlinarith [categoryPooledRoot_le_boroughSeparatedRoot
      htail hadmitted hrisk,
    boroughSeparatedRoot_nonneg tail admitted risk,
    categoryPooledRoot_nonneg tail admitted risk]

/-! ## Price-of-equity comparison certificates -/

/--
Any analytical pooling gain that covers the constructive alignment gap also
covers the true lexicographic price of all-request equity.
-/
theorem poolingGain_ge_price_of_equity_of_alignment_certificate
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival offset slope : Category → Borough → ℝ}
    {excessCapacity poolingGain : ℝ}
    {efficient equitable : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hslope : ∀ k b, 0 < slope k b)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) efficient)
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (affineDelayBurden offset slope z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) equitable)
    (hcertificate : finiteAlignmentGap arrival
      (affineDelayBurden offset slope efficient) ≤ poolingGain) :
    finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope equitable) -
      finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope efficient) ≤ poolingGain := by
  exact (finite_fixedLoadAlignment_price_le_gap htail hslope
    hefficient hequitable).2.trans hcertificate

/--
Under supplied exact endpoint formulas, the gain comparison is exactly the
memo's root-square condition.  This theorem deliberately separates the pure
algebra from the model-specific derivations of the two value identities.
-/
theorem categoryPoolingGain_ge_price_iff_rootSquares
    {price poolingGain separatedRoot pooledRoot parityRoot excessCapacity : ℝ}
    (hexcess : 0 < excessCapacity)
    (hprice : price = alignedOffsetAllRequestPrice
      parityRoot separatedRoot excessCapacity)
    (hpooling : poolingGain = analyticalCategoryPoolingGain
      separatedRoot pooledRoot excessCapacity) :
    poolingGain ≥ price ↔
      2 * separatedRoot ^ 2 ≥ parityRoot ^ 2 + pooledRoot ^ 2 := by
  rw [hprice, hpooling]
  unfold alignedOffsetAllRequestPrice analyticalCategoryPoolingGain
  change (parityRoot ^ 2 - separatedRoot ^ 2) / excessCapacity ≤
      (separatedRoot ^ 2 - pooledRoot ^ 2) / excessCapacity ↔
    parityRoot ^ 2 + pooledRoot ^ 2 ≤ 2 * separatedRoot ^ 2
  rw [div_le_div_iff_of_pos_right hexcess]
  constructor <;> intro h <;> linarith

/-! ## Direct arbitrary-Borough exact-symmetry composition -/

/-- Matrix and product-indexed forms of separated reciprocal feasibility agree. -/
theorem finiteMatrixReciprocalCapacityFeasible_categoryTail_iff
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    (tail : Category → ℝ) (excessCapacity : ℝ)
    (delay : Category → Borough → ℝ) :
    finiteMatrixReciprocalCapacityFeasible
        (fun k _b ↦ tail k) excessCapacity delay ↔
      reciprocalCapacityFeasible
        (boroughSeparatedTail (Borough := Borough) tail) excessCapacity
        (fun i ↦ delay i.1 i.2) := by
  classical
  unfold finiteMatrixReciprocalCapacityFeasible reciprocalCapacityFeasible
    reciprocalCapacityUse boroughSeparatedTail
  rw [Fintype.sum_prod_type]
  constructor
  · rintro ⟨hpos, hcap⟩
    exact ⟨fun i ↦ hpos i.1 i.2, hcap⟩
  · rintro ⟨hpos, hcap⟩
    exact ⟨fun k b ↦ hpos (k, b), hcap⟩

/--
Arrival-weighted all-request burden is the served-delay objective plus the
fixed noninspection term, in matrix notation.
-/
theorem finiteArrivalWeightedBurden_fixedLoad_eq_served_add_noninspection
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    (arrival admitted risk penalty delay : Category → Borough → ℝ)
    (harrival : ∀ k b, arrival k b ≠ 0) :
    finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty delay) =
      servedDelayEfficiency (boroughSeparatedWeight admitted risk)
        (fun i ↦ delay i.1 i.2) +
      fixedLoadNoninspectionCost
        (fun i : Category × Borough ↦ arrival i.1 i.2)
        (fun i ↦ admitted i.1 i.2)
        (fun i ↦ risk i.1 i.2)
        (fun i ↦ penalty i.1 i.2) := by
  classical
  have hadmittedIdentity : ∀ k b,
      admitted k b =
        fixedLoadInspectionProbability (arrival k b) (admitted k b) *
          arrival k b := by
    intro k b
    unfold fixedLoadInspectionProbability
    field_simp [harrival k b]
  calc
    finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty delay) =
        ∑ k, ∑ b, fixedLoadEfficiencyCellCost
          (arrival k b) (admitted k b) (risk k b)
          (delay k b) (penalty k b) := by
      unfold finiteArrivalWeightedBurden
        finiteFixedLoadAllRequestBurdenProfile
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro b _hb
      exact (fixedLoadEfficiencyCellCost_eq_arrival_mul_allRequestBurden
        (arrival k b) (admitted k b) (risk k b)
        (fixedLoadInspectionProbability (arrival k b) (admitted k b))
        (delay k b) (penalty k b) (hadmittedIdentity k b)).symm
    _ = servedDelayEfficiency (boroughSeparatedWeight admitted risk)
          (fun i ↦ delay i.1 i.2) +
        fixedLoadNoninspectionCost
          (fun i : Category × Borough ↦ arrival i.1 i.2)
          (fun i ↦ admitted i.1 i.2)
          (fun i ↦ risk i.1 i.2)
          (fun i ↦ penalty i.1 i.2) := by
      unfold fixedLoadEfficiencyCellCost servedDelayEfficiency
        boroughSeparatedWeight fixedLoadNoninspectionCost
      simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]

/--
The square-root endpoint is a concrete minimizer of the paper's full
arrival-weighted all-request efficiency objective; the noninspection term is
constant at fixed admitted load.
-/
theorem boroughSeparatedAllocationDelay_isMinimizerOn_allRequestBurden
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival admitted risk penalty : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity) :
    MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible
        (fun k _b ↦ tail k) excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z))
      (boroughSeparatedAllocationDelay tail admitted risk excessCapacity) := by
  have hflat := boroughSeparatedAllocationDelay_isMinimizerOn
    htail hadmitted hrisk hexcess
  constructor
  · exact (finiteMatrixReciprocalCapacityFeasible_categoryTail_iff
      tail excessCapacity
      (boroughSeparatedAllocationDelay tail admitted risk excessCapacity)).2
      hflat.1
  · intro delay hdelay
    have hflatDelay :=
      (finiteMatrixReciprocalCapacityFeasible_categoryTail_iff
        tail excessCapacity delay).1 hdelay
    have hle := hflat.2 (fun i ↦ delay i.1 i.2) hflatDelay
    change finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty
          (boroughSeparatedAllocationDelay tail admitted risk excessCapacity)) ≤
      finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty delay)
    rw [finiteArrivalWeightedBurden_fixedLoad_eq_served_add_noninspection
      arrival admitted risk penalty
      (boroughSeparatedAllocationDelay tail admitted risk excessCapacity)
      (fun k b ↦ (harrival k b).ne')]
    rw [finiteArrivalWeightedBurden_fixedLoad_eq_served_add_noninspection
      arrival admitted risk penalty delay
      (fun k b ↦ (harrival k b).ne')]
    simpa [add_comm] using add_le_add_right hle
      (fixedLoadNoninspectionCost
        (fun i : Category × Borough ↦ arrival i.1 i.2)
        (fun i ↦ admitted i.1 i.2)
        (fun i ↦ risk i.1 i.2)
        (fun i ↦ penalty i.1 i.2))

/--
When all primitives are constant across Boroughs within category, the actual
finite square-root efficiency endpoint has constant all-request burden within
each category.  This composes primitive symmetry with the endpoint formula,
rather than assuming equal delays as a separate premise.
-/
theorem exactSymmetry_boroughSeparatedEndpoint_zero_allRequestRange
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (tail : Category → ℝ)
    (arrival admitted risk penalty : Category → Borough → ℝ)
    (commonArrival commonAdmitted commonRisk commonPenalty : Category → ℝ)
    (excessCapacity : ℝ)
    (harrival : ∀ k b, arrival k b = commonArrival k)
    (hadmitted : ∀ k b, admitted k b = commonAdmitted k)
    (hrisk : ∀ k b, risk k b = commonRisk k)
    (hpenalty : ∀ k b, penalty k b = commonPenalty k) :
    finiteAllRequestRangeObjective
      (finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty
        (boroughSeparatedAllocationDelay
          tail admitted risk excessCapacity)) = 0 := by
  classical
  let b₀ : Borough := Classical.choice (inferInstance : Nonempty Borough)
  apply finiteAllRequestRangeObjective_eq_zero_of_constant
    (level := fun k ↦ fixedLoadAllRequestBurden
      (arrival k b₀) (admitted k b₀) (risk k b₀)
      (boroughSeparatedAllocationDelay tail admitted risk excessCapacity k b₀)
      (penalty k b₀))
  intro k b
  unfold finiteFixedLoadAllRequestBurdenProfile
  apply fixedLoadAllRequestBurden_eq_of_symmetric_inputs
  · exact (harrival k b).trans (harrival k b₀).symm
  · exact (hadmitted k b).trans (hadmitted k b₀).symm
  · exact (hrisk k b).trans (hrisk k b₀).symm
  · unfold boroughSeparatedAllocationDelay squareRootAllocationDelay
      boroughSeparatedTail boroughSeparatedWeight
    rw [hadmitted k b, hadmitted k b₀, hrisk k b, hrisk k b₀]
  · exact (hpenalty k b).trans (hpenalty k b₀).symm

/--
Consequently, whenever the square-root point and a lexicographic equity point
have their certified minimizer properties, exact primitive symmetry gives
zero additive all-request price of equity for arbitrary finite Borough sets.
-/
theorem exactSymmetry_boroughSeparatedEndpoint_zero_price
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (tail : Category → ℝ)
    (arrival admitted risk penalty : Category → Borough → ℝ)
    (commonArrival commonAdmitted commonRisk commonPenalty : Category → ℝ)
    (excessCapacity : ℝ)
    {equitable : Category → Borough → ℝ}
    (harrival : ∀ k b, arrival k b = commonArrival k)
    (hadmitted : ∀ k b, admitted k b = commonAdmitted k)
    (hrisk : ∀ k b, risk k b = commonRisk k)
    (hpenalty : ∀ k b, penalty k b = commonPenalty k)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible
        (fun k _b ↦ tail k) excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z))
      (boroughSeparatedAllocationDelay tail admitted risk excessCapacity))
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible
        (fun k _b ↦ tail k) excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z)) equitable) :
    finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty equitable) -
      finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty
          (boroughSeparatedAllocationDelay
            tail admitted risk excessCapacity)) = 0 := by
  apply zero_lexicographic_price_of_equity hefficient hequitable
  · intro z _hz
    exact finiteAllRequestRangeObjective_nonneg _
  · exact exactSymmetry_boroughSeparatedEndpoint_zero_allRequestRange
      tail arrival admitted risk penalty
      commonArrival commonAdmitted commonRisk commonPenalty excessCapacity
      harrival hadmitted hrisk hpenalty

/--
Fully source-shaped exact-symmetry result: positivity certifies that the actual
square-root point is the efficiency minimizer, so no efficiency certificate is
left as a premise.
-/
theorem exactSymmetry_boroughSeparatedEndpoint_zero_price_certified
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category] [Fintype Borough] [Nonempty Borough]
    {tail : Category → ℝ}
    {arrival admitted risk penalty : Category → Borough → ℝ}
    (commonArrival commonAdmitted commonRisk commonPenalty : Category → ℝ)
    {excessCapacity : ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : ∀ k, 0 < tail k)
    (harrival_pos : ∀ k b, 0 < arrival k b)
    (hadmitted_pos : ∀ k b, 0 < admitted k b)
    (hrisk_pos : ∀ k b, 0 < risk k b)
    (hexcess : 0 < excessCapacity)
    (harrival : ∀ k b, arrival k b = commonArrival k)
    (hadmitted : ∀ k b, admitted k b = commonAdmitted k)
    (hrisk : ∀ k b, risk k b = commonRisk k)
    (hpenalty : ∀ k b, penalty k b = commonPenalty k)
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible
        (fun k _b ↦ tail k) excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z)) equitable) :
    finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty equitable) -
      finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty
          (boroughSeparatedAllocationDelay
            tail admitted risk excessCapacity)) = 0 := by
  apply exactSymmetry_boroughSeparatedEndpoint_zero_price
    tail arrival admitted risk penalty
    commonArrival commonAdmitted commonRisk commonPenalty excessCapacity
    harrival hadmitted hrisk hpenalty
  · exact boroughSeparatedAllocationDelay_isMinimizerOn_allRequestBurden
      htail harrival_pos hadmitted_pos hrisk_pos hexcess
  · exact hequitable

end

end LG24ServiceLevelAgreements
