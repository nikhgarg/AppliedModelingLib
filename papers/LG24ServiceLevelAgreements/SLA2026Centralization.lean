import LG24ServiceLevelAgreements.SLA2026EfficiencyEquity
import LG24ServiceLevelAgreements.CurrentDraftPrograms
import Mathlib.Tactic

/-!
# Active 2026 SLA centralization theorem

This module formalizes the active manuscript's city-budget benchmark.  The
source-facing definitions live in `SLA2026Model`; the older finite allocation
lemmas use a Borough-first helper orientation, so the first results below make
that change of notation explicit.  No city optimality or value identity is
assumed as a premise.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Source-formula bridges -/

/-- The source city index is the generic category-pooled square-root root. -/
theorem sla2026CityEffectiveLoad_eq_categoryPooledRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : ℝ) (admitted priority : Category → Borough → ℝ) :
    sla2026CityEffectiveLoad tail admitted priority =
      categoryPooledRoot (fun _ : Category ↦ tail) admitted priority := by
  rfl

/--
Factoring the common positive tail parameter out of the city root gives the
Borough-first normalizer used by the strict-centralization lemma.
-/
theorem sla2026CityEffectiveLoad_eq_sqrtTail_mul_finiteCityRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : ℝ) (admitted priority : Category → Borough → ℝ)
    (htail : 0 < tail) :
    sla2026CityEffectiveLoad tail admitted priority =
      Real.sqrt tail * finiteCityRootNormalizer
        (fun b k ↦ admitted k b * priority k b) := by
  classical
  unfold sla2026CityEffectiveLoad finiteCityRootNormalizer
  calc
    (∑ k, Real.sqrt (tail * ∑ b, admitted k b * priority k b)) =
        ∑ k, Real.sqrt tail * Real.sqrt
          (∑ b, admitted k b * priority k b) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.sqrt_mul htail.le]
    _ = Real.sqrt tail * ∑ k, Real.sqrt
          (∑ b, admitted k b * priority k b) := by
      rw [Finset.mul_sum]

/--
Factoring the common tail parameter out of the Borough-budget index gives the
older finite decentralized normalizer.
-/
theorem sla2026EffectiveLoad_eq_sqrtTail_mul_finiteDecentralizedRoot
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : ℝ) (admitted priority : Category → Borough → ℝ)
    (htail : 0 < tail) :
    sla2026EffectiveLoad tail admitted priority =
      Real.sqrt tail * finiteDecentralizedRootNormalizer
        (fun b k ↦ admitted k b * priority k b) := by
  classical
  unfold sla2026EffectiveLoad finiteDecentralizedRootNormalizer
  calc
    (∑ k, ∑ b, Real.sqrt (tail * admitted k b * priority k b)) =
        ∑ k, ∑ b, Real.sqrt tail * Real.sqrt
          (admitted k b * priority k b) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro b _
      rw [show tail * admitted k b * priority k b =
        tail * (admitted k b * priority k b) by ring,
        Real.sqrt_mul htail.le]
    _ = ∑ k, Real.sqrt tail * ∑ b, Real.sqrt
          (admitted k b * priority k b) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = Real.sqrt tail * ∑ k, ∑ b, Real.sqrt
          (admitted k b * priority k b) := by
      rw [Finset.mul_sum]

/-- The city source formula is the certified category-pooled allocation. -/
theorem sla2026CityEfficientDelay_eq_categoryPooledAllocationDelay
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail excessCapacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b) (k : Category) :
    sla2026CityEfficientDelay tail excessCapacity admitted priority k =
      categoryPooledAllocationDelay (fun _ : Category ↦ tail)
        admitted priority excessCapacity k := by
  unfold sla2026CityEfficientDelay categoryPooledAllocationDelay
  rw [squareRootAllocationDelay_eq_fixedLoadEfficiencyDelay
    (tail := fun _ : Category ↦ tail)
    (weight := categoryPooledWeight admitted priority)
    (fun _ ↦ htail)
    (categoryPooledWeight_pos hadmitted hpriority) k]
  rw [sla2026CityEffectiveLoad_eq_categoryPooledRoot]
  simp [fixedLoadEfficiencyDelay, categoryPooledRoot, categoryPooledWeight]

/-- The city objective is pooled served-delay cost plus its fixed offset. -/
theorem sla2026CityEfficiency_eq_categoryPooledServed_add_fixed
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty : Category → Borough → ℝ)
    (delay : Category → ℝ) :
    sla2026CityEfficiency arrival admitted priority noninspectionPenalty delay =
      servedDelayEfficiency (categoryPooledWeight admitted priority) delay +
        sla2026FixedNoninspectionCost arrival admitted priority
          noninspectionPenalty := by
  classical
  unfold sla2026CityEfficiency sla2026FixedNoninspectionCost
    servedDelayEfficiency categoryPooledWeight
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]

/-- The displayed city endpoint is a global minimizer of the city program. -/
theorem sla2026_city_extreme_efficiency
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
      (sla2026CityFeasible tail (sla2026ExcessCapacity capacity admitted))
      (sla2026CityEfficiency arrival admitted priority noninspectionPenalty)
      (sla2026CityEfficientDelay tail (sla2026ExcessCapacity capacity admitted)
        admitted priority) := by
  let endpoint := categoryPooledAllocationDelay (fun _ : Category ↦ tail)
    admitted priority (sla2026ExcessCapacity capacity admitted)
  have hendpoint := categoryPooledAllocationDelay_isMinimizerOn
    (tail := fun _ : Category ↦ tail) (admitted := admitted) (risk := priority)
    (excessCapacity := sla2026ExcessCapacity capacity admitted)
    (fun _ ↦ htail) hadmitted hpriority hexcess
  have hformula :
      sla2026CityEfficientDelay tail (sla2026ExcessCapacity capacity admitted)
          admitted priority = endpoint := by
    funext k
    exact sla2026CityEfficientDelay_eq_categoryPooledAllocationDelay
      htail hadmitted hpriority k
  constructor
  · change reciprocalCapacityFeasible (fun _ : Category ↦ tail)
      (sla2026ExcessCapacity capacity admitted) _
    rw [hformula]
    exact hendpoint.1
  · intro delay hdelay
    change reciprocalCapacityFeasible (fun _ : Category ↦ tail)
      (sla2026ExcessCapacity capacity admitted) delay at hdelay
    rw [sla2026CityEfficiency_eq_categoryPooledServed_add_fixed,
      sla2026CityEfficiency_eq_categoryPooledServed_add_fixed, hformula]
    have hminimum :
        servedDelayEfficiency (categoryPooledWeight admitted priority) endpoint ≤
          servedDelayEfficiency (categoryPooledWeight admitted priority) delay :=
      hendpoint.2 delay hdelay
    simpa [endpoint, add_comm] using add_le_add_right hminimum
      (sla2026FixedNoninspectionCost arrival admitted priority
        noninspectionPenalty)

/-! ## Strict city-SLA improvement -/

/--
The source city formula agrees with the existing finite city formula after
the explicit orientation bridge.
-/
theorem sla2026CityEfficientDelay_eq_finiteCityEfficiencyDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail excessCapacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail) (hexcess : 0 < excessCapacity)
    (k : Category) :
    sla2026CityEfficientDelay tail excessCapacity admitted priority k =
      finiteCityEfficiencyDelay tail excessCapacity
        (fun b j ↦ admitted j b * priority j b) k := by
  have hroot := sla2026CityEffectiveLoad_eq_sqrtTail_mul_finiteCityRoot
    tail admitted priority htail
  have hsq : Real.sqrt tail * Real.sqrt tail = tail := by
    nlinarith [Real.sq_sqrt htail.le]
  unfold sla2026CityEfficientDelay finiteCityEfficiencyDelay
  rw [hroot, Real.sqrt_div htail.le]
  calc
    (Real.sqrt tail * finiteCityRootNormalizer
        (fun b j ↦ admitted j b * priority j b) / excessCapacity) *
        (Real.sqrt tail / Real.sqrt (∑ b, admitted k b * priority k b)) =
      (Real.sqrt tail * Real.sqrt tail) *
          finiteCityRootNormalizer
            (fun b j ↦ admitted j b * priority j b) /
          excessCapacity /
            Real.sqrt (∑ b, admitted k b * priority k b) := by
        ring
    _ = tail / excessCapacity *
          finiteCityRootNormalizer
            (fun b j ↦ admitted j b * priority j b) /
          Real.sqrt (∑ b, admitted k b * priority k b) := by
        rw [hsq] <;> ring

/-- The Borough source formula agrees with the finite decentralized formula. -/
theorem sla2026EfficientDelay_eq_finiteDecentralizedEfficiencyDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (k : Category) (b : Borough) :
    sla2026EfficientDelay tail capacity admitted priority k b =
      finiteDecentralizedEfficiencyDelay tail
        (sla2026ExcessCapacity capacity admitted)
        (fun j i ↦ admitted i j * priority i j) b k := by
  have hroot := sla2026EffectiveLoad_eq_sqrtTail_mul_finiteDecentralizedRoot
    tail admitted priority htail
  have hsq : Real.sqrt tail * Real.sqrt tail = tail := by
    nlinarith [Real.sq_sqrt htail.le]
  unfold sla2026EfficientDelay finiteDecentralizedEfficiencyDelay
  rw [hroot, Real.sqrt_div htail.le]
  calc
    (Real.sqrt tail * finiteDecentralizedRootNormalizer
        (fun j i ↦ admitted i j * priority i j) /
        sla2026ExcessCapacity capacity admitted) *
        (Real.sqrt tail / Real.sqrt (admitted k b * priority k b)) =
      (Real.sqrt tail * Real.sqrt tail) *
          finiteDecentralizedRootNormalizer
            (fun j i ↦ admitted i j * priority i j) /
          sla2026ExcessCapacity capacity admitted /
            Real.sqrt (admitted k b * priority k b) := by
        ring
    _ = tail / sla2026ExcessCapacity capacity admitted *
          finiteDecentralizedRootNormalizer
            (fun j i ↦ admitted i j * priority i j) /
          Real.sqrt (admitted k b * priority k b) := by
        rw [hsq] <;> ring

/--
With at least two Boroughs and positive admitted risk-weighted load in every
cell, the source city endpoint strictly shortens every Borough SLA.
-/
theorem sla2026_city_sla_strictly_shorter
    {Category Borough : Type*}
    [Fintype Category] [Nonempty Category]
    [Fintype Borough] [Nontrivial Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (k : Category) (b : Borough) :
    sla2026CityEfficientDelay tail (sla2026ExcessCapacity capacity admitted)
        admitted priority k <
      sla2026EfficientDelay tail capacity admitted priority k b := by
  calc
    sla2026CityEfficientDelay tail (sla2026ExcessCapacity capacity admitted)
        admitted priority k =
        finiteCityEfficiencyDelay tail (sla2026ExcessCapacity capacity admitted)
          (fun j i ↦ admitted i j * priority i j) k :=
      sla2026CityEfficientDelay_eq_finiteCityEfficiencyDelay htail hexcess k
    _ < finiteDecentralizedEfficiencyDelay tail
          (sla2026ExcessCapacity capacity admitted)
          (fun j i ↦ admitted i j * priority i j) b k :=
      finiteCityEfficiencyDelay_lt_decentralized htail hexcess
        (fun j i ↦ mul_pos (hadmitted i j) (hpriority i j)) b k
    _ = sla2026EfficientDelay tail capacity admitted priority k b :=
      (sla2026EfficientDelay_eq_finiteDecentralizedEfficiencyDelay
        htail k b).symm

/-! ## Exact source value identity -/

/--
The gain from the Borough-efficient endpoint to the city-efficient endpoint
is exactly `(A_eff^2 - A_city^2) / E(s)` in the active manuscript notation.
-/
theorem sla2026_centralization_gain
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
        (sla2026EfficientDelay tail capacity admitted priority) -
      sla2026CityEfficiency arrival admitted priority noninspectionPenalty
        (sla2026CityEfficientDelay tail
          (sla2026ExcessCapacity capacity admitted) admitted priority) =
      (sla2026EffectiveLoad tail admitted priority ^ 2 -
        sla2026CityEffectiveLoad tail admitted priority ^ 2) /
        sla2026ExcessCapacity capacity admitted := by
  have hseparated :
      (fun i : Category × Borough ↦
        sla2026EfficientDelay tail capacity admitted priority i.1 i.2) =
        (fun i ↦ boroughSeparatedAllocationDelay
          (fun _ : Category ↦ tail) admitted priority
          (sla2026ExcessCapacity capacity admitted) i.1 i.2) := by
    funext i
    exact sla2026EfficientDelay_eq_boroughSeparatedAllocationDelay
      htail hadmitted hpriority i.1 i.2
  have hpooled :
      sla2026CityEfficientDelay tail
          (sla2026ExcessCapacity capacity admitted) admitted priority =
        categoryPooledAllocationDelay (fun _ : Category ↦ tail)
          admitted priority (sla2026ExcessCapacity capacity admitted) := by
    funext k
    exact sla2026CityEfficientDelay_eq_categoryPooledAllocationDelay
      htail hadmitted hpriority k
  calc
    sla2026Efficiency arrival admitted priority noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority) -
      sla2026CityEfficiency arrival admitted priority noninspectionPenalty
        (sla2026CityEfficientDelay tail
          (sla2026ExcessCapacity capacity admitted) admitted priority) =
        servedDelayEfficiency (boroughSeparatedWeight admitted priority)
          (fun i ↦ boroughSeparatedAllocationDelay
            (fun _ : Category ↦ tail) admitted priority
            (sla2026ExcessCapacity capacity admitted) i.1 i.2) -
          servedDelayEfficiency (categoryPooledWeight admitted priority)
            (categoryPooledAllocationDelay (fun _ : Category ↦ tail)
              admitted priority (sla2026ExcessCapacity capacity admitted)) := by
      rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
        arrival admitted priority noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority)
        (fun k b ↦ (harrival k b).ne'),
        sla2026CityEfficiency_eq_categoryPooledServed_add_fixed,
        sla2026ServedDelayCost_eq_boroughSeparated, hseparated, hpooled]
      ring
    _ = analyticalCategoryPoolingGain
          (boroughSeparatedRoot (fun _ : Category ↦ tail) admitted priority)
          (categoryPooledRoot (fun _ : Category ↦ tail) admitted priority)
          (sla2026ExcessCapacity capacity admitted) :=
      boroughSeparatedValue_sub_categoryPooledValue_eq_gain
        (tail := fun _ : Category ↦ tail) (admitted := admitted) (risk := priority)
        (excessCapacity := sla2026ExcessCapacity capacity admitted)
        (fun _ ↦ htail) hadmitted hpriority hexcess
    _ = (sla2026EffectiveLoad tail admitted priority ^ 2 -
          sla2026CityEffectiveLoad tail admitted priority ^ 2) /
          sla2026ExcessCapacity capacity admitted := by
      unfold analyticalCategoryPoolingGain
      rw [← sla2026EffectiveLoad_eq_boroughSeparatedRoot,
        ← sla2026CityEffectiveLoad_eq_categoryPooledRoot]

/--
Pure algebra used to compose the centralization value identity with a future
price-of-equity identity.  It deliberately takes the two proved values as
explicit equalities rather than treating either as an assumption about an
optimizer.
-/
theorem sla2026_centralization_gain_ge_price_iff
    {effectiveLoad cityLoad priceOfEquity excessCapacity : ℝ}
    (heffectiveLoad : 0 < effectiveLoad)
    (hexcess : 0 < excessCapacity) :
    (effectiveLoad ^ 2 - cityLoad ^ 2) / excessCapacity ≥ priceOfEquity ↔
      1 - cityLoad ^ 2 / effectiveLoad ^ 2 ≥
        priceOfEquity * excessCapacity / effectiveLoad ^ 2 := by
  have heffectiveLoadSq : 0 < effectiveLoad ^ 2 := sq_pos_of_pos heffectiveLoad
  have hratio :
      1 - cityLoad ^ 2 / effectiveLoad ^ 2 =
        (effectiveLoad ^ 2 - cityLoad ^ 2) / effectiveLoad ^ 2 := by
    field_simp [heffectiveLoadSq.ne']
  constructor
  · intro h
    have hscaled : priceOfEquity * excessCapacity ≤
        effectiveLoad ^ 2 - cityLoad ^ 2 :=
      (le_div_iff₀ hexcess).mp h
    rw [hratio]
    exact (div_le_div_iff_of_pos_right heffectiveLoadSq).2 hscaled
  · intro h
    apply (le_div_iff₀ hexcess).2
    rw [hratio] at h
    exact (div_le_div_iff_of_pos_right heffectiveLoadSq).1 h

end

end LG24ServiceLevelAgreements
