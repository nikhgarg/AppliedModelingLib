import LG24ServiceLevelAgreements.SLA2026CapacityScaling
import Mathlib.Tactic

/-!
# Relative price of equity for the active SLA source

The current source defines price of equity as the additive efficiency gap
normalized by the efficient all-request cost.  The prior additive proof is
retained as an internal numerator theorem; this module derives the printed
relative statements only after proving the efficient baseline is positive
from the source primitives.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-- The fixed noninspection component of all-request efficiency is
nonnegative under the source's rate, priority, and penalty conditions. -/
theorem sla2026FixedNoninspectionCost_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b) :
    0 ≤ sla2026FixedNoninspectionCost arrival admitted priority
      noninspectionPenalty := by
  classical
  unfold sla2026FixedNoninspectionCost
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg
    (mul_nonneg (sub_nonneg.mpr (hadmitted_le_arrival k b))
      (hpriority k b).le)
    (hnoninspectionPenalty k b)

/-- The current source's efficient all-request baseline is strictly positive.
This is derived from the positive served-delay component rather than added as
a denominator assumption. -/
theorem sla2026Efficiency_efficientDelay_pos
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
    0 < sla2026Efficiency arrival admitted priority noninspectionPenalty
      (sla2026EfficientDelay tail capacity admitted priority) := by
  rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
    arrival admitted priority noninspectionPenalty
    (sla2026EfficientDelay tail capacity admitted priority)
    (fun k b ↦ (harrival k b).ne')]
  apply add_pos_of_pos_of_nonneg
  · rw [sla2026_servedDelayCost_efficientDelay
      htail hadmitted hpriority hexcess]
    exact div_pos
      (sq_pos_of_pos (sla2026EffectiveLoad_pos htail hadmitted hpriority)) hexcess
  · exact sla2026FixedNoninspectionCost_nonneg hadmitted_le_arrival hpriority
      hnoninspectionPenalty

/-- The relative price is the preserved additive gap divided by the positive
efficient baseline. -/
theorem sla2026RelativePriceOfEquity_eq_additive_div
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable efficient : Category → Borough → ℝ}
    (hefficient : sla2026Efficiency arrival admitted priority noninspectionPenalty
      efficient ≠ 0) :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable efficient =
      sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable efficient /
        sla2026Efficiency arrival admitted priority noninspectionPenalty efficient := by
  unfold sla2026RelativePriceOfEquity sla2026PriceOfEquity
  field_simp [hefficient]

/-- The exact relative Pearson identity printed in the current source. -/
theorem sla2026_relativePriceOfEquity_chi_square
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          (sla2026ExcessCapacity capacity admitted *
            sla2026Efficiency arrival admitted priority noninspectionPenalty
              (sla2026EfficientDelay tail capacity admitted priority)) *
        sla2026PearsonChiSquare
          (sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority))
          (sla2026CapacityShare tail capacity admitted equitable) := by
  let efficient := sla2026EfficientDelay tail capacity admitted priority
  let baseline := sla2026Efficiency arrival admitted priority noninspectionPenalty
    efficient
  have hbaseline : 0 < baseline := by
    simpa [baseline, efficient] using
      (sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
        hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess)
  have hadditive := sla2026_price_of_equity_chi_square
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess hbest
  change sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
      equitable efficient = _
  rw [sla2026RelativePriceOfEquity_eq_additive_div hbaseline.ne', hadditive]
  field_simp [hexcess.ne', hbaseline.ne']
  ring

/-- The source-relative price of equity is nonnegative. -/
theorem sla2026_relativePriceOfEquity_nonneg
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    0 ≤ sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
      equitable (sla2026EfficientDelay tail capacity admitted priority) := by
  rw [sla2026_relativePriceOfEquity_chi_square
    htail harrival hadmitted hadmitted_le_arrival hpriority
    hnoninspectionPenalty hexcess hbest]
  apply mul_nonneg
  · exact div_nonneg (sq_nonneg _)
      (mul_nonneg hexcess.le
        (sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
          hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess).le)
  · exact sla2026PearsonChiSquare_nonneg
      (sla2026CapacityShare_pos htail hexcess hbest.1.1)

/-- Dividing by a nonzero efficient baseline preserves the zero set of the
additive numerator. -/
theorem sla2026RelativePriceOfEquity_eq_zero_iff_additive_eq_zero
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable efficient : Category → Borough → ℝ}
    (hefficient : sla2026Efficiency arrival admitted priority noninspectionPenalty
      efficient ≠ 0) :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable efficient = 0 ↔
      sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable efficient = 0 := by
  rw [sla2026RelativePriceOfEquity_eq_additive_div hefficient]
  constructor
  · intro hzero
    have hscaled := (div_eq_iff hefficient).mp hzero
    simpa using hscaled
  · intro hzero
    simp [hzero]

/-- The source-relative upper bound is the prior additive range bound divided
by the derived positive efficient baseline. -/
theorem sla2026_relativePriceOfEquity_le_efficient_cost_range
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) ≤
      (1 / sla2026Efficiency arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority)) *
        ∑ k, ∑ b, arrival k b *
          (finiteCategoryMaximum
            (sla2026Cost arrival admitted priority noninspectionPenalty
              (sla2026EfficientDelay tail capacity admitted priority)) k -
            sla2026Cost arrival admitted priority noninspectionPenalty
              (sla2026EfficientDelay tail capacity admitted priority) k b) := by
  let efficient := sla2026EfficientDelay tail capacity admitted priority
  let baseline := sla2026Efficiency arrival admitted priority noninspectionPenalty
    efficient
  let range : ℝ := ∑ k, ∑ b, arrival k b *
    (finiteCategoryMaximum
      (sla2026Cost arrival admitted priority noninspectionPenalty efficient) k -
      sla2026Cost arrival admitted priority noninspectionPenalty efficient k b)
  have hbaseline : 0 < baseline := by
    simpa [baseline, efficient] using
      (sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
        hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess)
  have hadditive := sla2026_price_of_equity_le_efficient_cost_range
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hadmitted_le_arrival hpriority
    hnoninspectionPenalty hexcess hbest
  change sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
      equitable efficient ≤ 1 / baseline * range
  rw [sla2026RelativePriceOfEquity_eq_additive_div hbaseline.ne']
  calc
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable efficient / baseline ≤ range / baseline :=
      div_le_div_of_nonneg_right hadditive hbaseline.le
    _ = 1 / baseline * range := by
      field_simp [hbaseline.ne']

/-- The zero characterization for the relative source quantity is unchanged:
it occurs exactly when the equitable and efficient capacity shares coincide. -/
theorem sla2026_relativePriceOfEquity_eq_zero_iff_capacityShare_eq
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) = 0 ↔
      sla2026CapacityShare tail capacity admitted equitable =
        sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority) := by
  have hbaseline : sla2026Efficiency arrival admitted priority noninspectionPenalty
      (sla2026EfficientDelay tail capacity admitted priority) ≠ 0 :=
    (sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
      hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess).ne'
  rw [sla2026RelativePriceOfEquity_eq_zero_iff_additive_eq_zero hbaseline]
  exact sla2026_price_of_equity_eq_zero_iff_capacityShare_eq
    htail harrival hadmitted hpriority hexcess hbest

/-- The relative source quantity is zero exactly when the efficient endpoint
already has categorywise constant all-request cost. -/
theorem sla2026_relativePriceOfEquity_eq_zero_iff_efficient_cost_constant
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) = 0 ↔
      ∃ level : Category → ℝ, ∀ k b,
        sla2026Cost arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority) k b = level k := by
  rw [sla2026_relativePriceOfEquity_eq_zero_iff_capacityShare_eq
    htail harrival hadmitted hadmitted_le_arrival hpriority
    hnoninspectionPenalty hexcess hbest]
  exact (sla2026_price_of_equity_eq_zero_iff_capacityShare_eq
      htail harrival hadmitted hpriority hexcess hbest).symm.trans
    (sla2026_price_of_equity_eq_zero_iff_efficient_cost_constant
      htail harrival hadmitted hadmitted_le_arrival hpriority
      hnoninspectionPenalty hexcess hbest)

/-- The current source's relative price of equity scales by both the excess
capacity ratio and the ratio of efficient all-request baselines.  The
additional baseline factor is derived here, rather than being absorbed into
the old additive scaling theorem. -/
theorem sla2026RelativePriceOfEquity_capacity_scale_of_efficiencyBestEquitable
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {offset : Category → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity')
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    {equitable equitable' : Category → Borough → ℝ}
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable)
    (hbest' : sla2026EfficiencyBestEquitable tail capacity' arrival admitted
      priority noninspectionPenalty equitable') :
    sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable' (sla2026EfficientDelay tail capacity' admitted priority) =
      (sla2026ExcessCapacity capacity admitted /
          sla2026ExcessCapacity capacity' admitted) *
        (sla2026Efficiency arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority) /
          sla2026Efficiency arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity' admitted priority)) *
        sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (sla2026EfficientDelay tail capacity admitted priority) := by
  have hexcess : 0 < sla2026ExcessCapacity capacity admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hexcess' : 0 < sla2026ExcessCapacity capacity' admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hbaseline : 0 < sla2026Efficiency arrival admitted priority
      noninspectionPenalty
      (sla2026EfficientDelay tail capacity admitted priority) :=
    sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
      hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess
  have hbaseline' : 0 < sla2026Efficiency arrival admitted priority
      noninspectionPenalty
      (sla2026EfficientDelay tail capacity' admitted priority) :=
    sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
      hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess'
  have hadditive := sla2026PriceOfEquity_capacity_scale_of_efficiencyBestEquitable
    (tail := tail) (capacity := capacity) (capacity' := capacity')
    (arrival := arrival) (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    hbaseCapacity hcapacityIncrease (fun k b ↦ (harrival k b).ne')
    hoffset hbest hbest'
  rw [sla2026RelativePriceOfEquity_eq_additive_div hbaseline'.ne',
    sla2026RelativePriceOfEquity_eq_additive_div hbaseline.ne', hadditive]
  field_simp [hexcess.ne', hexcess'.ne', hbaseline.ne', hbaseline'.ne']

/-- At the efficient endpoint, total all-request cost is the square-root
served-delay value plus the fixed noninspection component.  This is the
denominator identity used by the source's relative capacity comparison. -/
theorem sla2026Efficiency_efficientDelay_eq_effectiveLoad_sq_div_add_fixed
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    sla2026Efficiency arrival admitted priority noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority) =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
        sla2026ExcessCapacity capacity admitted +
          sla2026FixedNoninspectionCost arrival admitted priority
            noninspectionPenalty := by
  rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
      arrival admitted priority noninspectionPenalty
      (sla2026EfficientDelay tail capacity admitted priority)
      (fun k b ↦ (harrival k b).ne'),
    sla2026_servedDelayCost_efficientDelay htail hadmitted hpriority hexcess]

/-- The manuscript's relative capacity-scaling factor has a simple form once
the efficient endpoint's fixed component is made explicit. -/
theorem sla2026RelativePriceOfEquity_capacity_scaling_factor_eq
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity') :
    (sla2026ExcessCapacity capacity admitted /
        sla2026ExcessCapacity capacity' admitted) *
        (sla2026Efficiency arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority) /
          sla2026Efficiency arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity' admitted priority)) =
      (sla2026EffectiveLoad tail admitted priority ^ 2 +
          sla2026ExcessCapacity capacity admitted *
            sla2026FixedNoninspectionCost arrival admitted priority
              noninspectionPenalty) /
        (sla2026EffectiveLoad tail admitted priority ^ 2 +
          sla2026ExcessCapacity capacity' admitted *
            sla2026FixedNoninspectionCost arrival admitted priority
              noninspectionPenalty) := by
  have hexcess : 0 < sla2026ExcessCapacity capacity admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hexcess' : 0 < sla2026ExcessCapacity capacity' admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hbaseline : 0 < sla2026Efficiency arrival admitted priority
      noninspectionPenalty
      (sla2026EfficientDelay tail capacity admitted priority) :=
    sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
      hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess
  have hbaseline' : 0 < sla2026Efficiency arrival admitted priority
      noninspectionPenalty
      (sla2026EfficientDelay tail capacity' admitted priority) :=
    sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
      hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess'
  have hcost := sla2026Efficiency_efficientDelay_eq_effectiveLoad_sq_div_add_fixed
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess
  have hcost' := sla2026Efficiency_efficientDelay_eq_effectiveLoad_sq_div_add_fixed
    (tail := tail) (capacity := capacity') (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess'
  have hcostPos : 0 <
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted +
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty := by
    rw [← hcost]
    exact hbaseline
  have hcostPos' : 0 <
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity' admitted +
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty := by
    rw [← hcost']
    exact hbaseline'
  have hfixed : 0 ≤ sla2026FixedNoninspectionCost arrival admitted priority
      noninspectionPenalty :=
    sla2026FixedNoninspectionCost_nonneg hadmitted_le_arrival hpriority
      hnoninspectionPenalty
  have hloadSq : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 :=
    sq_pos_of_pos (sla2026EffectiveLoad_pos htail hadmitted hpriority)
  have hdenominator : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 +
      sla2026ExcessCapacity capacity' admitted *
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty :=
    add_pos_of_pos_of_nonneg hloadSq (mul_nonneg hexcess'.le hfixed)
  have hnumerator : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 +
      sla2026ExcessCapacity capacity admitted *
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty :=
    add_pos_of_pos_of_nonneg hloadSq (mul_nonneg hexcess.le hfixed)
  rw [hcost, hcost']
  field_simp [hexcess.ne', hexcess'.ne', hcostPos.ne', hcostPos'.ne',
    hnumerator.ne', hdenominator.ne']

/-- With a strictly positive fixed noninspection component, the source's
relative price-of-equity capacity-scaling factor is strictly below one. -/
theorem sla2026RelativePriceOfEquity_capacity_scaling_factor_lt_one
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity')
    (hfixedPositive : 0 < sla2026FixedNoninspectionCost arrival admitted priority
      noninspectionPenalty) :
    (sla2026ExcessCapacity capacity admitted /
        sla2026ExcessCapacity capacity' admitted) *
        (sla2026Efficiency arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority) /
          sla2026Efficiency arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity' admitted priority)) < 1 := by
  rw [sla2026RelativePriceOfEquity_capacity_scaling_factor_eq
    htail harrival hadmitted hadmitted_le_arrival hpriority hnoninspectionPenalty
    hbaseCapacity hcapacityIncrease]
  have hexcess : 0 < sla2026ExcessCapacity capacity admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hexcess' : 0 < sla2026ExcessCapacity capacity' admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hexcess_lt : sla2026ExcessCapacity capacity admitted <
      sla2026ExcessCapacity capacity' admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hloadSq : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 :=
    sq_pos_of_pos (sla2026EffectiveLoad_pos htail hadmitted hpriority)
  have hdenominator : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 +
      sla2026ExcessCapacity capacity' admitted *
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty :=
    add_pos_of_pos_of_nonneg hloadSq
      (mul_nonneg hexcess'.le hfixedPositive.le)
  apply (div_lt_one hdenominator).mpr
  have hproduct : sla2026ExcessCapacity capacity admitted *
      sla2026FixedNoninspectionCost arrival admitted priority noninspectionPenalty <
      sla2026ExcessCapacity capacity' admitted *
        sla2026FixedNoninspectionCost arrival admitted priority noninspectionPenalty :=
    mul_lt_mul_of_pos_right hexcess_lt hfixedPositive
  linarith

/-- If the fixed noninspection component vanishes, the source's relative
capacity-scaling factor is exactly one. -/
theorem sla2026RelativePriceOfEquity_capacity_scaling_factor_eq_one
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity')
    (hfixedZero : sla2026FixedNoninspectionCost arrival admitted priority
      noninspectionPenalty = 0) :
    (sla2026ExcessCapacity capacity admitted /
        sla2026ExcessCapacity capacity' admitted) *
        (sla2026Efficiency arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority) /
          sla2026Efficiency arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity' admitted priority)) = 1 := by
  rw [sla2026RelativePriceOfEquity_capacity_scaling_factor_eq
    htail harrival hadmitted hadmitted_le_arrival hpriority hnoninspectionPenalty
    hbaseCapacity hcapacityIncrease]
  have hloadSq : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 :=
    sq_pos_of_pos (sla2026EffectiveLoad_pos htail hadmitted hpriority)
  simp [hfixedZero, hloadSq.ne']

end

end LG24ServiceLevelAgreements
