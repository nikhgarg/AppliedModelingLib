import LG24ServiceLevelAgreements.ProposedParityReduction
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Existence for the heterogeneous all-request parity reduction

The strict-domain reduced parity program has an optimizer under the natural
strict positivity assumptions.  The proof is elementary and finite
dimensional.  Positive coefficients and positive excess capacity first give
an explicit feasible common-level profile.  Every feasible profile is then
uniformly separated from every offset by `coefficient / excessCapacity`.
Intersecting feasibility with the objective sublevel of the explicit witness
therefore puts all relevant profiles in a closed coordinate box.  Continuity
on that box and the extreme-value theorem yield attainment.

The final theorem transports this reduced optimizer to the original delay
problem through the exact equivalence in `ProposedParityReduction`.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators
open Set

noncomputable section

/-! ## An explicit feasible parity profile -/

/-- Total reciprocal-capacity coefficient in the finite reduced problem. -/
def heterogeneousParityTotalCoefficient
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (coefficient : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, coefficient k b

/-- A common gap large enough to make the explicit maximum-offset profile
feasible. -/
def heterogeneousParityWitnessGap
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (coefficient : Category → Borough → ℝ) (excessCapacity : ℝ) : ℝ :=
  heterogeneousParityTotalCoefficient coefficient / excessCapacity

/-- Explicit feasible profile: every category maximum offset plus the same
capacity-calibrated positive gap. -/
def heterogeneousParityWitnessLevel
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Borough]
    (coefficient offset : Category → Borough → ℝ)
    (excessCapacity : ℝ) : Category → ℝ :=
  fun k ↦ finiteCategoryMaximum offset k +
    heterogeneousParityWitnessGap coefficient excessCapacity

/-- Strictly positive cell coefficients make their finite total positive. -/
theorem heterogeneousParityTotalCoefficient_pos
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {coefficient : Category → Borough → ℝ}
    (hcoefficient : ∀ k b, 0 < coefficient k b) :
    0 < heterogeneousParityTotalCoefficient coefficient := by
  classical
  unfold heterogeneousParityTotalCoefficient
  exact Finset.sum_pos (fun k _hk ↦
    Finset.sum_pos (fun b _hb ↦ hcoefficient k b) Finset.univ_nonempty)
    Finset.univ_nonempty

/-- The witness gap is strictly positive. -/
theorem heterogeneousParityWitnessGap_pos
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {coefficient : Category → Borough → ℝ} {excessCapacity : ℝ}
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (hcapacity : 0 < excessCapacity) :
    0 < heterogeneousParityWitnessGap coefficient excessCapacity := by
  exact div_pos (heterogeneousParityTotalCoefficient_pos hcoefficient) hcapacity

/-- The maximum-offset witness is feasible for every positive coefficient
array and positive excess capacity. -/
theorem heterogeneousParityWitnessLevel_feasible
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (coefficient offset : Category → Borough → ℝ)
    (excessCapacity : ℝ)
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (hcapacity : 0 < excessCapacity) :
    heterogeneousParityFeasible coefficient offset excessCapacity
      (heterogeneousParityWitnessLevel coefficient offset excessCapacity) := by
  classical
  let gap := heterogeneousParityWitnessGap coefficient excessCapacity
  have hgap : 0 < gap := heterogeneousParityWitnessGap_pos hcoefficient hcapacity
  constructor
  · intro k b
    dsimp [heterogeneousParityWitnessLevel]
    exact lt_of_le_of_lt (burden_le_finiteCategoryMaximum offset k b)
      (lt_add_of_pos_right _ hgap)
  · unfold heterogeneousParityCapacityUse
    calc
      ∑ k, ∑ b,
          coefficient k b /
            (heterogeneousParityWitnessLevel coefficient offset
              excessCapacity k - offset k b) ≤
          ∑ k, ∑ b, coefficient k b / gap := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro b _hb
        apply div_le_div_of_nonneg_left (hcoefficient k b).le hgap
        dsimp [heterogeneousParityWitnessLevel]
        have hmax := burden_le_finiteCategoryMaximum offset k b
        linarith
      _ = heterogeneousParityTotalCoefficient coefficient / gap := by
        unfold heterogeneousParityTotalCoefficient
        simp_rw [Finset.sum_div]
      _ = excessCapacity := by
        dsimp [gap, heterogeneousParityWitnessGap]
        field_simp [hcapacity.ne',
          (heterogeneousParityTotalCoefficient_pos hcoefficient).ne']

/-! ## Feasibility separates every denominator from zero -/

/-- A nonnegative summand is bounded by the full finite double sum. -/
theorem heterogeneousParity_cellTerm_le_capacityUse
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {level : Category → ℝ}
    (hcoefficient : ∀ k b, 0 ≤ coefficient k b)
    (hdomain : heterogeneousParityDomain offset level)
    (k : Category) (b : Borough) :
    coefficient k b / (level k - offset k b) ≤
      heterogeneousParityCapacityUse coefficient offset level := by
  classical
  unfold heterogeneousParityCapacityUse
  apply le_trans
    (Finset.single_le_sum
      (fun j (_hj : j ∈ (Finset.univ : Finset Borough)) ↦
        div_nonneg (hcoefficient k j)
          (heterogeneousParityDenominator_pos hdomain k j).le)
      (Finset.mem_univ b))
  exact Finset.single_le_sum
    (fun i (_hi : i ∈ (Finset.univ : Finset Category)) ↦
      Finset.sum_nonneg fun j _hj ↦
        div_nonneg (hcoefficient i j)
          (heterogeneousParityDenominator_pos hdomain i j).le)
    (Finset.mem_univ k)

/-- Every feasible level is separated from each cell offset by at least the
strictly positive amount `coefficient / excessCapacity`. -/
theorem heterogeneousParityFeasible_gap_le
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {excessCapacity : ℝ} {level : Category → ℝ}
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (hcapacity : 0 < excessCapacity)
    (hlevel : heterogeneousParityFeasible coefficient offset excessCapacity level)
    (k : Category) (b : Borough) :
    coefficient k b / excessCapacity ≤ level k - offset k b := by
  have hterm : coefficient k b / (level k - offset k b) ≤ excessCapacity :=
    le_trans (heterogeneousParity_cellTerm_le_capacityUse
      (fun i j ↦ (hcoefficient i j).le) hlevel.1 k b) hlevel.2
  have hden : 0 < level k - offset k b :=
    heterogeneousParityDenominator_pos hlevel.1 k b
  apply (div_le_iff₀ hcapacity).2
  apply (div_le_iff₀ hden).1 at hterm
  nlinarith

/-! ## Compact objective sublevel -/

/-- Closed coordinatewise lower bound forced by feasibility. -/
def heterogeneousParityLowerBound
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (coefficient offset : Category → Borough → ℝ)
    (excessCapacity : ℝ) : Category → ℝ :=
  fun k ↦ finiteCategoryMaximum
    (fun i b ↦ offset i b + coefficient i b / excessCapacity) k

/-- Every feasible profile lies above the closed lower-bound profile. -/
theorem heterogeneousParityLowerBound_le_of_feasible
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {coefficient offset : Category → Borough → ℝ}
    {excessCapacity : ℝ} {level : Category → ℝ}
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (hcapacity : 0 < excessCapacity)
    (hlevel : heterogeneousParityFeasible coefficient offset excessCapacity level) :
    heterogeneousParityLowerBound coefficient offset excessCapacity ≤ level := by
  classical
  intro k
  unfold heterogeneousParityLowerBound finiteCategoryMaximum
  apply Finset.sup'_le Finset.univ_nonempty
  intro b _hb
  have hgap := heterogeneousParityFeasible_gap_le
    hcoefficient hcapacity hlevel k b
  linarith

/-- Objective slack above the feasibility lower bound. -/
def heterogeneousParityWitnessObjectiveSlack
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (coefficient offset : Category → Borough → ℝ)
    (arrivalMass : Category → ℝ) (excessCapacity : ℝ) : ℝ :=
  heterogeneousParityObjective arrivalMass
      (heterogeneousParityWitnessLevel coefficient offset excessCapacity) -
    heterogeneousParityObjective arrivalMass
      (heterogeneousParityLowerBound coefficient offset excessCapacity)

/-- Coordinatewise upper bound for the witness objective sublevel. -/
def heterogeneousParityUpperBound
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (coefficient offset : Category → Borough → ℝ)
    (arrivalMass : Category → ℝ) (excessCapacity : ℝ) : Category → ℝ :=
  fun k ↦ heterogeneousParityLowerBound coefficient offset excessCapacity k +
    heterogeneousParityWitnessObjectiveSlack coefficient offset arrivalMass
      excessCapacity / arrivalMass k

/-- A feasible point in the witness objective sublevel lies below the explicit
upper-bound profile. -/
theorem heterogeneousParity_le_upperBound_of_objective_le_witness
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {coefficient offset : Category → Borough → ℝ}
    {arrivalMass : Category → ℝ} {excessCapacity : ℝ}
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (harrival : ∀ k, 0 < arrivalMass k)
    (hcapacity : 0 < excessCapacity)
    {level : Category → ℝ}
    (hlevel : heterogeneousParityFeasible coefficient offset excessCapacity level)
    (hobjective : heterogeneousParityObjective arrivalMass level ≤
      heterogeneousParityObjective arrivalMass
        (heterogeneousParityWitnessLevel coefficient offset excessCapacity)) :
    level ≤ heterogeneousParityUpperBound coefficient offset arrivalMass
      excessCapacity := by
  classical
  let lower := heterogeneousParityLowerBound coefficient offset excessCapacity
  have hlower : lower ≤ level :=
    heterogeneousParityLowerBound_le_of_feasible hcoefficient hcapacity hlevel
  intro k
  have hnonneg : ∀ j, 0 ≤ arrivalMass j * (level j - lower j) := by
    intro j
    exact mul_nonneg (harrival j).le (sub_nonneg.mpr (hlower j))
  have hterm : arrivalMass k * (level k - lower k) ≤
      ∑ j, arrivalMass j * (level j - lower j) :=
    Finset.single_le_sum (fun j (_hj : j ∈ (Finset.univ : Finset Category)) ↦
      hnonneg j) (Finset.mem_univ k)
  have hsum : (∑ j, arrivalMass j * (level j - lower j)) =
      heterogeneousParityObjective arrivalMass level -
        heterogeneousParityObjective arrivalMass lower := by
    unfold heterogeneousParityObjective
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hbudget : arrivalMass k * (level k - lower k) ≤
      heterogeneousParityWitnessObjectiveSlack coefficient offset arrivalMass
        excessCapacity := by
    rw [hsum] at hterm
    unfold heterogeneousParityWitnessObjectiveSlack
    exact hterm.trans (sub_le_sub_right hobjective _)
  unfold heterogeneousParityUpperBound
  dsimp only
  have hdiv : level k - lower k ≤
      heterogeneousParityWitnessObjectiveSlack coefficient offset arrivalMass
        excessCapacity / arrivalMass k := by
    apply (le_div_iff₀ (harrival k)).2
    simpa [mul_comm] using hbudget
  change level k ≤ lower k +
    heterogeneousParityWitnessObjectiveSlack coefficient offset arrivalMass
      excessCapacity / arrivalMass k
  linarith

/-! ## Continuity and attainment -/

/-- Capacity use is continuous on any box whose lower endpoint has all
denominators strictly above the offsets. -/
theorem continuousOn_heterogeneousParityCapacityUse_Icc
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {lower upper : Category → ℝ}
    (hlower : ∀ k b, offset k b < lower k) :
    ContinuousOn (heterogeneousParityCapacityUse coefficient offset)
      (Set.Icc lower upper) := by
  classical
  intro level hlevel
  unfold heterogeneousParityCapacityUse
  apply ContinuousAt.continuousWithinAt
  apply tendsto_finset_sum Finset.univ
  intro k _hk
  apply tendsto_finset_sum Finset.univ
  intro b _hb
  apply ContinuousAt.div continuousAt_const
    ((continuous_apply k).continuousAt.sub continuousAt_const)
  have hden : offset k b < level k :=
    lt_of_lt_of_le (hlower k b) (hlevel.1 k)
  exact (sub_pos.mpr hden).ne'

/-- The reduced linear objective is continuous. -/
theorem continuous_heterogeneousParityObjective
    {Category : Type*} [Fintype Category]
    (arrivalMass : Category → ℝ) :
    Continuous (heterogeneousParityObjective arrivalMass) := by
  classical
  unfold heterogeneousParityObjective
  fun_prop

/-- Under strict positive coefficients, arrival masses, and excess capacity,
the heterogeneous reduced parity problem attains its minimum. -/
theorem exists_heterogeneousParity_minimizer
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (coefficient offset : Category → Borough → ℝ)
    (arrivalMass : Category → ℝ) (excessCapacity : ℝ)
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (harrival : ∀ k, 0 < arrivalMass k)
    (hcapacity : 0 < excessCapacity) :
    ∃ level, MinimizesOn
      (heterogeneousParityFeasible coefficient offset excessCapacity)
      (heterogeneousParityObjective arrivalMass) level := by
  classical
  let witness := heterogeneousParityWitnessLevel coefficient offset excessCapacity
  let lower := heterogeneousParityLowerBound coefficient offset excessCapacity
  let upper := heterogeneousParityUpperBound coefficient offset arrivalMass excessCapacity
  let box : Set (Category → ℝ) := Set.Icc lower upper
  let capacitySublevel : Set (Category → ℝ) :=
    {level ∈ box |
      heterogeneousParityCapacityUse coefficient offset level ≤ excessCapacity}
  let compactSublevel : Set (Category → ℝ) :=
    {level ∈ capacitySublevel |
      heterogeneousParityObjective arrivalMass level ≤
        heterogeneousParityObjective arrivalMass witness}
  have hwitnessFeasible : heterogeneousParityFeasible coefficient offset
      excessCapacity witness :=
    heterogeneousParityWitnessLevel_feasible coefficient offset excessCapacity
      hcoefficient hcapacity
  have hlowerWitness : lower ≤ witness :=
    heterogeneousParityLowerBound_le_of_feasible hcoefficient hcapacity
      hwitnessFeasible
  have hupperWitness : witness ≤ upper :=
    heterogeneousParity_le_upperBound_of_objective_le_witness
      hcoefficient harrival hcapacity hwitnessFeasible le_rfl
  have hstrictLower : ∀ k b, offset k b < lower k := by
    intro k b
    have hcell : offset k b + coefficient k b / excessCapacity ≤ lower k :=
      burden_le_finiteCategoryMaximum
        (fun i j ↦ offset i j + coefficient i j / excessCapacity) k b
    have hgap : 0 < coefficient k b / excessCapacity :=
      div_pos (hcoefficient k b) hcapacity
    linarith
  have hcapacityContinuous : ContinuousOn
      (heterogeneousParityCapacityUse coefficient offset) box :=
    continuousOn_heterogeneousParityCapacityUse_Icc hstrictLower
  have hcapacityClosed : IsClosed capacitySublevel := by
    apply (isClosed_Icc : IsClosed box).isClosed_le hcapacityContinuous
      continuousOn_const
  have hobjectiveContinuous := continuous_heterogeneousParityObjective arrivalMass
  have hcompactClosed : IsClosed compactSublevel := by
    apply hcapacityClosed.isClosed_le
      (hobjectiveContinuous.continuousOn.mono (by intro x hx; exact hx.1))
      continuousOn_const
  have hcompact : IsCompact compactSublevel :=
    IsCompact.of_isClosed_subset isCompact_Icc hcompactClosed (by
      intro x hx
      exact hx.1.1)
  have hwitnessCompact : witness ∈ compactSublevel := by
    refine ⟨⟨⟨hlowerWitness, hupperWitness⟩, hwitnessFeasible.2⟩, le_rfl⟩
  rcases hcompact.exists_isMinOn ⟨witness, hwitnessCompact⟩
      hobjectiveContinuous.continuousOn with
    ⟨minLevel, hminCompact, hoptimalCompact⟩
  refine ⟨minLevel, ?_, ?_⟩
  · have hdomain : heterogeneousParityDomain offset minLevel := by
      intro k b
      exact lt_of_lt_of_le (hstrictLower k b) (hminCompact.1.1.1 k)
    exact ⟨hdomain, hminCompact.1.2⟩
  · intro level hlevel
    by_cases hobjective : heterogeneousParityObjective arrivalMass level ≤
        heterogeneousParityObjective arrivalMass witness
    · have hlowerLevel : lower ≤ level :=
        heterogeneousParityLowerBound_le_of_feasible hcoefficient hcapacity hlevel
      have hupperLevel : level ≤ upper :=
        heterogeneousParity_le_upperBound_of_objective_le_witness
          hcoefficient harrival hcapacity hlevel hobjective
      exact hoptimalCompact
        ⟨⟨⟨hlowerLevel, hupperLevel⟩, hlevel.2⟩, hobjective⟩
    · have hminLeWitness := hoptimalCompact hwitnessCompact
      exact hminLeWitness.trans (le_of_not_ge hobjective)

/-! ## Transport back to lexicographic delay minimization -/

/-- Strict primitive positivity yields existence of a lexicographic
zero-range delay minimizer through the exact reduced representation. -/
theorem exists_lexicographicDelay_minimizer_of_positive_primitives
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {logTail arrival risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (hslope : ∀ k b,
      0 < allRequestDelaySlope (risk k b) (inspectionProbability k b))
    (hcoefficient : ∀ k b, 0 < allRequestParityCapacityCoefficient
      (logTail k b) (risk k b) (inspectionProbability k b))
    (harrivalMass : ∀ k, 0 < heterogeneousParityArrivalMass arrival k)
    (hcapacity : 0 < excessCapacity) :
    ∃ level,
      MinimizesOn
        (heterogeneousParityFeasible
          (fun k b ↦ allRequestParityCapacityCoefficient
            (logTail k b) (risk k b) (inspectionProbability k b))
          (fun k b ↦ allRequestFixedOffset
            (risk k b) (inspectionProbability k b)
            (noninspectionPenalty k b))
          excessCapacity)
        (heterogeneousParityObjective
          (heterogeneousParityArrivalMass arrival)) level ∧
      LexicographicallyMinimizesEquityThenEfficiencyOn
        (finiteMatrixReciprocalCapacityFeasible logTail excessCapacity)
        (fun delay ↦ finiteAllRequestRangeObjective
          (finiteAllRequestDelayBurden risk inspectionProbability
            noninspectionPenalty delay))
        (finiteAllRequestArrivalWeightedEfficiency arrival risk
          inspectionProbability noninspectionPenalty)
        (finiteAllRequestParityDelay level risk inspectionProbability
          noninspectionPenalty) := by
  rcases exists_heterogeneousParity_minimizer
      (fun k b ↦ allRequestParityCapacityCoefficient
        (logTail k b) (risk k b) (inspectionProbability k b))
      (fun k b ↦ allRequestFixedOffset
        (risk k b) (inspectionProbability k b) (noninspectionPenalty k b))
      (heterogeneousParityArrivalMass arrival) excessCapacity
      hcoefficient harrivalMass hcapacity with ⟨level, hlevel⟩
  exact ⟨level, hlevel,
    (heterogeneousParity_minimizer_iff_lexicographicDelay_minimizer
      level hslope).1 hlevel⟩

end

end LG24ServiceLevelAgreements
