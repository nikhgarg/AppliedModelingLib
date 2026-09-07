import LG24ServiceLevelAgreements.SLA2026PriceOfEquity
import Mathlib.Tactic

/-!
# Capacity scaling for the active 2026 SLA model

This file proves the capacity comparison used in Proposition 4 of the active
manuscript.  It works directly with the source feasible set and source
objectives.  The only structural condition needed to transport the equitable
endpoint is that the fixed noninspection burden is constant across Boroughs
within each Category.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-- Scale every conditional-delay coordinate by the same positive scalar. -/
def sla2026ScaleDelay
    {Category Borough : Type*} (scale : ℝ)
    (delay : Category → Borough → ℝ) : Category → Borough → ℝ :=
  fun k b ↦ scale * delay k b

/-! ## Feasible-set transport -/

/-- Reciprocal capacity use scales inversely when every delay is scaled. -/
theorem sla2026_reciprocalCapacityUse_scaleDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail scale : ℝ) (delay : Category → Borough → ℝ)
    (hscale : scale ≠ 0) (hdelay : ∀ k b, delay k b ≠ 0) :
    (∑ k, ∑ b, tail / sla2026ScaleDelay scale delay k b) =
      (∑ k, ∑ b, tail / delay k b) / scale := by
  classical
  calc
    (∑ k, ∑ b, tail / sla2026ScaleDelay scale delay k b) =
        ∑ k, ∑ b, (tail / delay k b) / scale := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro b _hb
      unfold sla2026ScaleDelay
      field_simp [hscale, hdelay k b]
    _ = (∑ k, ∑ b, tail / delay k b) / scale := by
      simp_rw [Finset.sum_div]

/-- Scaling delays transports the source feasible set when excess capacity
scales by the same factor. -/
theorem sla2026Feasible_scaleDelay_iff
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity capacity' scale : ℝ}
    {admitted delay : Category → Borough → ℝ}
    (hscale : 0 < scale)
    (hcapacity : scale * sla2026ExcessCapacity capacity' admitted =
      sla2026ExcessCapacity capacity admitted) :
    sla2026Feasible tail capacity admitted delay ↔
      sla2026Feasible tail capacity' admitted (sla2026ScaleDelay scale delay) := by
  constructor
  · rintro ⟨hpositive, hcapacityUse⟩
    refine ⟨?_, ?_⟩
    · intro k b
      exact mul_pos hscale (hpositive k b)
    · rw [sla2026_reciprocalCapacityUse_scaleDelay tail scale delay hscale.ne'
        (fun k b ↦ (hpositive k b).ne')]
      apply (div_le_iff₀ hscale).2
      nlinarith [hcapacityUse, hcapacity]
  · rintro ⟨hpositive, hcapacityUse⟩
    have hdelayPositive : ∀ k b, 0 < delay k b := by
      intro k b
      rcases (mul_pos_iff.mp (hpositive k b)) with h | h
      · exact h.2
      · linarith
    refine ⟨hdelayPositive, ?_⟩
    · have hscaledUse :
        (∑ k, ∑ b, tail / delay k b) / scale ≤
          sla2026ExcessCapacity capacity' admitted := by
        rw [sla2026_reciprocalCapacityUse_scaleDelay tail scale delay hscale.ne'
          (fun k b ↦ (hdelayPositive k b).ne')] at hcapacityUse
        exact hcapacityUse
      have huse : (∑ k, ∑ b, tail / delay k b) ≤
          scale * sla2026ExcessCapacity capacity' admitted := by
        simpa [mul_comm] using (div_le_iff₀ hscale).1 hscaledUse
      simpa [hcapacity] using huse

/-! ## Objective transport -/

/-- The manuscript's categorywise fixed-noninspection-burden condition. -/
def sla2026CategorywiseFixedNoninspection
    {Category Borough : Type*}
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ) : Prop :=
  ∃ offset : Category → ℝ, ∀ k b,
    allRequestFixedOffset (priority k b)
      (sla2026InspectionProbability arrival admitted k b)
      (noninspectionPenalty k b) = offset k

/-- Under categorywise fixed noninspection burdens, delay scaling is an
affine categorywise transformation of all-request cost. -/
theorem sla2026Cost_scaleDelay
    {Category Borough : Type*}
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ)
    {offset : Category → ℝ}
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    (scale : ℝ) (delay : Category → Borough → ℝ) (k : Category) (b : Borough) :
    sla2026Cost arrival admitted priority noninspectionPenalty
        (sla2026ScaleDelay scale delay) k b =
      scale * sla2026Cost arrival admitted priority noninspectionPenalty delay k b +
        (1 - scale) * offset k := by
  change allRequestBurden (priority k b)
      (sla2026InspectionProbability arrival admitted k b)
      (scale * delay k b) (noninspectionPenalty k b) =
    scale * allRequestBurden (priority k b)
      (sla2026InspectionProbability arrival admitted k b)
      (delay k b) (noninspectionPenalty k b) + (1 - scale) * offset k
  rw [allRequestBurden_eq_fixedOffset_add_slope_mul_delay
      (priority k b) (sla2026InspectionProbability arrival admitted k b)
      (scale * delay k b) (noninspectionPenalty k b),
    allRequestBurden_eq_fixedOffset_add_slope_mul_delay
      (priority k b) (sla2026InspectionProbability arrival admitted k b)
      (delay k b) (noninspectionPenalty k b),
    hoffset k b]
  ring

/-- Zero within-category disparity is invariant under positive delay scaling
when the fixed noninspection burden is categorywise constant. -/
theorem sla2026Equity_scaleDelay_eq_zero_iff
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ)
    {offset : Category → ℝ}
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    {scale : ℝ} (hscale : 0 < scale)
    (delay : Category → Borough → ℝ) :
    sla2026Equity arrival admitted priority noninspectionPenalty
        (sla2026ScaleDelay scale delay) = 0 ↔
      sla2026Equity arrival admitted priority noninspectionPenalty delay = 0 := by
  constructor
  · intro hzero
    have hlevels :=
      (finiteAllRequestRangeObjective_eq_zero_iff_exists_levels
        (sla2026Cost arrival admitted priority noninspectionPenalty
          (sla2026ScaleDelay scale delay))).1 (by
            simpa [sla2026Equity] using hzero)
    rcases hlevels with ⟨level, hlevel⟩
    have hsource : finiteAllRequestRangeObjective
        (sla2026Cost arrival admitted priority noninspectionPenalty delay) = 0 := by
      apply (finiteAllRequestRangeObjective_eq_zero_iff_exists_levels _).2
      refine ⟨fun k ↦ (level k - (1 - scale) * offset k) / scale, ?_⟩
      intro k b
      have h := hlevel k b
      rw [sla2026Cost_scaleDelay arrival admitted priority noninspectionPenalty
        hoffset scale delay k b] at h
      apply (eq_div_iff hscale.ne').2
      linarith
    simpa [sla2026Equity] using hsource
  · intro hzero
    have hlevels :=
      (finiteAllRequestRangeObjective_eq_zero_iff_exists_levels
        (sla2026Cost arrival admitted priority noninspectionPenalty delay)).1 (by
          simpa [sla2026Equity] using hzero)
    rcases hlevels with ⟨level, hlevel⟩
    have hscaled : finiteAllRequestRangeObjective
        (sla2026Cost arrival admitted priority noninspectionPenalty
          (sla2026ScaleDelay scale delay)) = 0 := by
      apply (finiteAllRequestRangeObjective_eq_zero_iff_exists_levels _).2
      refine ⟨fun k ↦ scale * level k + (1 - scale) * offset k, ?_⟩
      intro k b
      rw [sla2026Cost_scaleDelay arrival admitted priority noninspectionPenalty
        hoffset scale delay k b, hlevel k b]
    simpa [sla2026Equity] using hscaled

/-- The delay-dependent part of total all-request cost is homogeneous in
conditional delay. -/
theorem sla2026ServedDelayCost_scaleDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (admitted priority : Category → Borough → ℝ)
    (scale : ℝ) (delay : Category → Borough → ℝ) :
    sla2026ServedDelayCost admitted priority (sla2026ScaleDelay scale delay) =
      scale * sla2026ServedDelayCost admitted priority delay := by
  classical
  unfold sla2026ServedDelayCost sla2026ScaleDelay
  calc
    (∑ k, ∑ b, admitted k b * priority k b * (scale * delay k b)) =
        ∑ k, ∑ b, scale * (admitted k b * priority k b * delay k b) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = ∑ k, scale * (∑ b, admitted k b * priority k b * delay k b) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ = scale * (∑ k, ∑ b, admitted k b * priority k b * delay k b) := by
      rw [Finset.mul_sum]

/-- Total efficiency changes affinely under any uniform delay scaling. -/
theorem sla2026Efficiency_scaleDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ)
    (harrival : ∀ k b, arrival k b ≠ 0)
    (scale : ℝ) (delay : Category → Borough → ℝ) :
    sla2026Efficiency arrival admitted priority noninspectionPenalty
        (sla2026ScaleDelay scale delay) =
      scale * sla2026Efficiency arrival admitted priority noninspectionPenalty delay +
        (1 - scale) *
          sla2026FixedNoninspectionCost arrival admitted priority
            noninspectionPenalty := by
  rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
      arrival admitted priority noninspectionPenalty
      (sla2026ScaleDelay scale delay) harrival,
    sla2026Efficiency_eq_servedDelayCost_add_fixed
      arrival admitted priority noninspectionPenalty delay harrival,
    sla2026ServedDelayCost_scaleDelay]
  ring

/-! ## Source endpoint transport -/

/-- The displayed efficient delay scales inversely with the source excess
capacity. -/
theorem sla2026EfficientDelay_capacity_scale
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity capacity' : ℝ}
    {admitted priority : Category → Borough → ℝ}
    (hcapacity : 0 < sla2026ExcessCapacity capacity admitted)
    (hcapacity' : 0 < sla2026ExcessCapacity capacity' admitted) :
    sla2026EfficientDelay tail capacity' admitted priority =
      sla2026ScaleDelay
        (sla2026ExcessCapacity capacity admitted /
          sla2026ExcessCapacity capacity' admitted)
        (sla2026EfficientDelay tail capacity admitted priority) := by
  funext k b
  unfold sla2026EfficientDelay sla2026ScaleDelay
  field_simp [hcapacity.ne', hcapacity'.ne']

/-- Transport an efficiency-best zero-disparity endpoint across a proportional
increase in excess capacity. -/
theorem sla2026EfficiencyBestEquitable_scaleDelay
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail capacity capacity' scale : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {offset : Category → ℝ}
    (hscale : 0 < scale)
    (hcapacity : scale * sla2026ExcessCapacity capacity' admitted =
      sla2026ExcessCapacity capacity admitted)
    (harrival : ∀ k b, arrival k b ≠ 0)
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    {delay : Category → Borough → ℝ}
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty delay) :
    sla2026EfficiencyBestEquitable tail capacity' arrival admitted
      priority noninspectionPenalty (sla2026ScaleDelay scale delay) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (sla2026Feasible_scaleDelay_iff hscale hcapacity).1 hbest.1
  · exact (sla2026Equity_scaleDelay_eq_zero_iff
      arrival admitted priority noninspectionPenalty hoffset hscale delay).2 hbest.2.1
  · intro other hother hotherZero
    have hinverse : sla2026ScaleDelay scale
        (sla2026ScaleDelay (1 / scale) other) = other := by
      funext k b
      unfold sla2026ScaleDelay
      field_simp [hscale.ne']
    have hbackFeasible : sla2026Feasible tail capacity admitted
        (sla2026ScaleDelay (1 / scale) other) := by
      apply (sla2026Feasible_scaleDelay_iff hscale hcapacity).2
      rw [hinverse]
      exact hother
    have hbackZero : sla2026Equity arrival admitted priority
        noninspectionPenalty (sla2026ScaleDelay (1 / scale) other) = 0 := by
      apply (sla2026Equity_scaleDelay_eq_zero_iff
        arrival admitted priority noninspectionPenalty hoffset hscale
        (sla2026ScaleDelay (1 / scale) other)).1
      rw [hinverse]
      exact hotherZero
    have hmin := hbest.2.2 _ hbackFeasible hbackZero
    have hleft := sla2026Efficiency_scaleDelay arrival admitted priority
      noninspectionPenalty harrival scale delay
    have hright := sla2026Efficiency_scaleDelay arrival admitted priority
      noninspectionPenalty harrival scale (sla2026ScaleDelay (1 / scale) other)
    rw [hleft]
    rw [← hinverse]
    rw [hright]
    nlinarith [mul_le_mul_of_nonneg_left hmin hscale.le]

/-- Proposition 4's source-capacity condition gives the proportional
feasible-set transport factor. -/
theorem sla2026EfficiencyBestEquitable_capacity_scale
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {offset : Category → ℝ}
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity')
    (harrival : ∀ k b, arrival k b ≠ 0)
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    {delay : Category → Borough → ℝ}
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty delay) :
    sla2026EfficiencyBestEquitable tail capacity' arrival admitted
      priority noninspectionPenalty
        (sla2026ScaleDelay
          (sla2026ExcessCapacity capacity admitted /
            sla2026ExcessCapacity capacity' admitted) delay) := by
  have hexcess : 0 < sla2026ExcessCapacity capacity admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hexcess' : 0 < sla2026ExcessCapacity capacity' admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hscale : 0 < sla2026ExcessCapacity capacity admitted /
      sla2026ExcessCapacity capacity' admitted :=
    div_pos hexcess hexcess'
  have hcapacity :
      (sla2026ExcessCapacity capacity admitted /
        sla2026ExcessCapacity capacity' admitted) *
          sla2026ExcessCapacity capacity' admitted =
        sla2026ExcessCapacity capacity admitted := by
    field_simp [hexcess'.ne']
  exact sla2026EfficiencyBestEquitable_scaleDelay hscale hcapacity harrival
    hoffset hbest

/-- Proposition 4's price of equity scales by the source excess-capacity
ratio, while the efficient and equitable source endpoints both transport. -/
theorem sla2026PriceOfEquity_capacity_scale
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {offset : Category → ℝ}
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity')
    (harrival : ∀ k b, arrival k b ≠ 0)
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    {equitable : Category → Borough → ℝ}
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026EfficiencyBestEquitable tail capacity' arrival admitted
        priority noninspectionPenalty
        (sla2026ScaleDelay
          (sla2026ExcessCapacity capacity admitted /
            sla2026ExcessCapacity capacity' admitted) equitable) ∧
      sla2026EfficientDelay tail capacity' admitted priority =
        sla2026ScaleDelay
          (sla2026ExcessCapacity capacity admitted /
            sla2026ExcessCapacity capacity' admitted)
          (sla2026EfficientDelay tail capacity admitted priority) ∧
      sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
          (sla2026ScaleDelay
            (sla2026ExcessCapacity capacity admitted /
              sla2026ExcessCapacity capacity' admitted) equitable)
          (sla2026EfficientDelay tail capacity' admitted priority) =
        (sla2026ExcessCapacity capacity admitted /
          sla2026ExcessCapacity capacity' admitted) *
          sla2026PriceOfEquity arrival admitted priority noninspectionPenalty equitable
            (sla2026EfficientDelay tail capacity admitted priority) := by
  have hexcess : 0 < sla2026ExcessCapacity capacity admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hexcess' : 0 < sla2026ExcessCapacity capacity' admitted := by
    unfold sla2026ExcessCapacity
    linarith
  have hbest' := sla2026EfficiencyBestEquitable_capacity_scale
    hbaseCapacity hcapacityIncrease harrival hoffset hbest
  have hefficient := sla2026EfficientDelay_capacity_scale
    (tail := tail) (admitted := admitted) (priority := priority) hexcess hexcess'
  refine ⟨hbest', hefficient, ?_⟩
  unfold sla2026PriceOfEquity
  rw [hefficient,
    sla2026Efficiency_scaleDelay arrival admitted priority noninspectionPenalty
      harrival
      (sla2026ExcessCapacity capacity admitted /
        sla2026ExcessCapacity capacity' admitted) equitable,
    sla2026Efficiency_scaleDelay arrival admitted priority noninspectionPenalty
      harrival
      (sla2026ExcessCapacity capacity admitted /
        sla2026ExcessCapacity capacity' admitted)
      (sla2026EfficientDelay tail capacity admitted priority)]
  ring

/-- The capacity-scaling price formula holds for every efficiency-best
equitable endpoint at the larger capacity, not merely the transported
representative. -/
theorem sla2026PriceOfEquity_capacity_scale_of_efficiencyBestEquitable
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail capacity capacity' : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {offset : Category → ℝ}
    (hbaseCapacity : (∑ k, ∑ b, admitted k b) < capacity)
    (hcapacityIncrease : capacity < capacity')
    (harrival : ∀ k b, arrival k b ≠ 0)
    (hoffset : ∀ k b,
      allRequestFixedOffset (priority k b)
        (sla2026InspectionProbability arrival admitted k b)
        (noninspectionPenalty k b) = offset k)
    {equitable equitable' : Category → Borough → ℝ}
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable)
    (hbest' : sla2026EfficiencyBestEquitable tail capacity' arrival admitted
      priority noninspectionPenalty equitable') :
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable' (sla2026EfficientDelay tail capacity' admitted priority) =
      (sla2026ExcessCapacity capacity admitted /
          sla2026ExcessCapacity capacity' admitted) *
        sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (sla2026EfficientDelay tail capacity admitted priority) := by
  rcases sla2026PriceOfEquity_capacity_scale
      hbaseCapacity hcapacityIncrease harrival hoffset hbest with
    ⟨htransportedBest, _hefficient, hscale⟩
  calc
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable' (sla2026EfficientDelay tail capacity' admitted priority) =
      sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        (sla2026ScaleDelay
          (sla2026ExcessCapacity capacity admitted /
            sla2026ExcessCapacity capacity' admitted) equitable)
        (sla2026EfficientDelay tail capacity' admitted priority) :=
        sla2026PriceOfEquity_eq_of_efficiencyBestEquitable hbest'
          htransportedBest
    _ = (sla2026ExcessCapacity capacity admitted /
          sla2026ExcessCapacity capacity' admitted) *
        sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (sla2026EfficientDelay tail capacity admitted priority) := hscale

end

end LG24ServiceLevelAgreements
