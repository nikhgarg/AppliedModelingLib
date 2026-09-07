import LG24ServiceLevelAgreements.SLA2026EfficiencyEquity
import LG24ServiceLevelAgreements.SLA2026Pearson
import LG24ServiceLevelAgreements.ProposedParityKKT
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Active 2026 SLA price of equity

This module proves the active manuscript's price-of-equity proposition from
the finite source model.  In particular, the binding of the equitable
endpoint is derived below; the Pearson identity does not take capacity
binding as an extra endpoint hypothesis.
-/

namespace LG24ServiceLevelAgreements

open Filter Topology
open scoped Topology
open scoped BigOperators

noncomputable section

/-! ## Binding in the positive reduced parity problem -/

private theorem continuousAt_heterogeneousParityCapacityUse_uniformLowering
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {level : Category → ℝ}
    (hdomain : heterogeneousParityDomain offset level) :
    ContinuousAt
      (fun amount : ℝ ↦ heterogeneousParityCapacityUse coefficient offset
        (fun k ↦ level k - amount)) 0 := by
  classical
  unfold heterogeneousParityCapacityUse
  apply tendsto_finset_sum Finset.univ
  intro k _hk
  apply tendsto_finset_sum Finset.univ
  intro b _hb
  apply ContinuousAt.div continuousAt_const
    ((continuousAt_const.sub continuousAt_id).sub continuousAt_const)
  simpa using (heterogeneousParityDenominator_pos hdomain k b).ne'

/--
With positive category masses, a minimizer of the reduced all-request parity
problem uses all available capacity.  The proof lowers every common burden by
a sufficiently small positive amount inside the strict feasible domain.
-/
theorem heterogeneousParityCapacity_binds_of_positive_primitives
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {coefficient offset : Category → Borough → ℝ}
    {arrivalMass : Category → ℝ} {excessCapacity : ℝ}
    {level : Category → ℝ}
    (hcoefficient : ∀ k b, 0 < coefficient k b)
    (harrivalMass : ∀ k, 0 < arrivalMass k)
    (hmin : MinimizesOn
      (heterogeneousParityFeasible coefficient offset excessCapacity)
      (heterogeneousParityObjective arrivalMass) level) :
    heterogeneousParityCapacityUse coefficient offset level = excessCapacity := by
  apply heterogeneousParityCapacity_binds_of_slack_improvable hmin
  intro hslack
  let lowering : ℝ → Category → ℝ := fun amount k ↦ level k - amount
  have hcontinuous : ContinuousAt
      (fun amount : ℝ ↦ heterogeneousParityCapacityUse coefficient offset
        (lowering amount)) 0 := by
    simpa [lowering] using
      continuousAt_heterogeneousParityCapacityUse_uniformLowering hmin.1.1
  have hcapacityNear : ∀ᶠ amount in 𝓝 (0 : ℝ),
      heterogeneousParityCapacityUse coefficient offset (lowering amount) <
        excessCapacity := by
    apply hcontinuous.eventually_lt continuousAt_const
    simpa [lowering] using hslack
  have hdomainNear : ∀ᶠ amount in 𝓝 (0 : ℝ),
      ∀ cell : Category × Borough,
        offset cell.1 cell.2 < lowering amount cell.1 := by
    rw [eventually_all]
    intro cell
    have hleft : ContinuousAt
        (fun _ : ℝ ↦ offset cell.1 cell.2) 0 := continuousAt_const
    have hright : ContinuousAt
        (fun amount : ℝ ↦ lowering amount cell.1) 0 := by
      simpa [lowering] using (continuousAt_const.sub continuousAt_id)
    apply hleft.eventually_lt hright
    simpa [lowering] using hmin.1.1 cell.1 cell.2
  rcases Metric.mem_nhds_iff.mp (hcapacityNear.and hdomainNear) with
    ⟨radius, hradius, hball⟩
  let amount : ℝ := radius / 2
  have hamount : 0 < amount := by
    dsimp [amount]
    linarith
  have hamountBall : amount ∈ Metric.ball (0 : ℝ) radius := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [sub_zero, abs_of_pos hamount]
    dsimp [amount]
    linarith
  have hnear := hball hamountBall
  refine ⟨lowering amount, ?_, ?_⟩
  · refine ⟨?_, hnear.1.le⟩
    intro k b
    exact hnear.2 (k, b)
  · have hmass : 0 < ∑ k, arrivalMass k :=
      Finset.sum_pos (fun k _hk ↦ harrivalMass k) Finset.univ_nonempty
    unfold heterogeneousParityObjective
    calc
      (∑ k, arrivalMass k * lowering amount k) =
          (∑ k, arrivalMass k * level k) -
            amount * (∑ k, arrivalMass k) := by
        calc
          (∑ k, arrivalMass k * lowering amount k) =
              ∑ k, (arrivalMass k * level k - amount * arrivalMass k) := by
            apply Finset.sum_congr rfl
            intro k _hk
            simp only [lowering]
            ring
          _ = (∑ k, arrivalMass k * level k) -
              ∑ k, amount * arrivalMass k := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ k, arrivalMass k * level k) -
              amount * (∑ k, arrivalMass k) := by
            rw [Finset.mul_sum]
      _ < ∑ k, arrivalMass k * level k := by
        nlinarith [mul_pos hamount hmass]

/-! ## Source endpoint transport -/

/-- A source-facing efficiency-best equitable point is a lexicographic
range-then-efficiency minimizer in the reduced all-request vocabulary. -/
theorem sla2026EfficiencyBestEquitable_is_lexicographic
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {delay : Category → Borough → ℝ}
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty delay) :
    LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible (fun _ _ ↦ tail)
        (sla2026ExcessCapacity capacity admitted))
      (fun z ↦ finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty z))
      (finiteAllRequestArrivalWeightedEfficiency arrival priority
        (sla2026InspectionProbability arrival admitted)
        noninspectionPenalty)
      delay := by
  let inspectionProbability := sla2026InspectionProbability arrival admitted
  have hzero : finiteAllRequestRangeObjective
      (finiteAllRequestDelayBurden priority inspectionProbability
        noninspectionPenalty delay) = 0 := by
    simpa [sla2026Equity, sla2026Cost, sla2026InspectionProbability,
      finiteAllRequestDelayBurden, inspectionProbability] using hbest.2.1
  refine ⟨?_, ?_, ?_⟩
  · simpa [sla2026Feasible, sla2026ExcessCapacity] using hbest.1
  · intro other hother
    have hzero' : finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty delay) = 0 := by
      simpa [inspectionProbability] using hzero
    change finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty delay) ≤
      finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty other)
    rw [hzero']
    exact finiteAllRequestRangeObjective_nonneg _
  · intro other hother heq
    have hotherZero : finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority inspectionProbability
          noninspectionPenalty other) = 0 := by
      have heq' : finiteAllRequestRangeObjective
          (finiteAllRequestDelayBurden priority inspectionProbability
            noninspectionPenalty other) =
          finiteAllRequestRangeObjective
            (finiteAllRequestDelayBurden priority inspectionProbability
              noninspectionPenalty delay) := by
        simpa [inspectionProbability] using heq
      rw [heq', hzero]
    have hsourceOther : sla2026Feasible tail capacity admitted other := by
      simpa [sla2026Feasible, sla2026ExcessCapacity] using hother
    have hsourceZero : sla2026Equity arrival admitted priority
        noninspectionPenalty other = 0 := by
      simpa [sla2026Equity, sla2026Cost, sla2026InspectionProbability,
        finiteAllRequestDelayBurden, inspectionProbability] using hotherZero
    have hoptimal := hbest.2.2 other hsourceOther hsourceZero
    simpa [sla2026Efficiency, sla2026Cost, sla2026InspectionProbability,
      finiteAllRequestArrivalWeightedEfficiency,
      finiteAllRequestDelayBurden, inspectionProbability] using hoptimal

/-- The price relative to the displayed efficient endpoint is independent of
which efficiency-minimizing zero-disparity endpoint is selected.  This makes
the source's printed price well-defined even when the equitable optimizer is
not unique as a delay profile. -/
theorem sla2026PriceOfEquity_eq_of_efficiencyBestEquitable
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {first second : Category → Borough → ℝ}
    (hfirst : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty first)
    (hsecond : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty second) :
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty first
        (sla2026EfficientDelay tail capacity admitted priority) =
      sla2026PriceOfEquity arrival admitted priority noninspectionPenalty second
        (sla2026EfficientDelay tail capacity admitted priority) := by
  have hefficiency : sla2026Efficiency arrival admitted priority
      noninspectionPenalty first =
      sla2026Efficiency arrival admitted priority noninspectionPenalty second := by
    apply le_antisymm
    · exact hfirst.2.2 second hsecond.1 hsecond.2.1
    · exact hsecond.2.2 first hfirst.1 hfirst.2.1
  unfold sla2026PriceOfEquity
  rw [hefficiency]

/-- The all-request equitable endpoint of the active source uses all source
reciprocal capacity. -/
theorem sla2026_equitable_capacity_binds
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {delay : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty delay) :
    (∑ k, ∑ b, tail / delay k b) =
      sla2026ExcessCapacity capacity admitted := by
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
  have hlex := sla2026EfficiencyBestEquitable_is_lexicographic hbest
  have hwitness : ∃ level,
      heterogeneousParityFeasible
        (fun k b ↦ allRequestParityCapacityCoefficient tail
          (priority k b) (inspectionProbability k b))
        (fun k b ↦ allRequestFixedOffset (priority k b)
          (inspectionProbability k b) (noninspectionPenalty k b))
        (sla2026ExcessCapacity capacity admitted) level := by
    refine ⟨heterogeneousParityWitnessLevel
      (fun k b ↦ allRequestParityCapacityCoefficient tail
        (priority k b) (inspectionProbability k b))
      (fun k b ↦ allRequestFixedOffset (priority k b)
        (inspectionProbability k b) (noninspectionPenalty k b))
      (sla2026ExcessCapacity capacity admitted), ?_⟩
    exact heterogeneousParityWitnessLevel_feasible _ _ _ hcoefficient hexcess
  rcases lexicographicDelay_minimizer_has_heterogeneousParity_representation
      (logTail := fun _ _ ↦ tail) (arrival := arrival) (risk := priority)
      (inspectionProbability := inspectionProbability)
      (noninspectionPenalty := noninspectionPenalty)
      (excessCapacity := sla2026ExcessCapacity capacity admitted)
      hslope hwitness hlex with ⟨level, hrepresentation, hmin⟩
  have hbind := heterogeneousParityCapacity_binds_of_positive_primitives
    hcoefficient harrivalMass hmin
  have hrisk : ∀ k b, priority k b ≠ 0 := fun k b ↦ (hpriority k b).ne'
  have hprobability : ∀ k b, inspectionProbability k b ≠ 0 :=
    fun k b ↦ (hinspect k b).ne'
  have hlevel : ∀ k b,
      level k - allRequestFixedOffset (priority k b)
        (inspectionProbability k b) (noninspectionPenalty k b) ≠ 0 :=
    fun k b ↦ (sub_pos.mpr (hmin.1.1 k b)).ne'
  calc
    (∑ k, ∑ b, tail / delay k b) =
        ∑ k, ∑ b, tail /
          allRequestParityDelay (level k) (priority k b)
            (inspectionProbability k b) (noninspectionPenalty k b) := by
          simpa [finiteAllRequestParityDelay] using
            congrArg (fun z : Category → Borough → ℝ ↦
              ∑ k, ∑ b, tail / z k b) hrepresentation
    _ = ∑ k, ∑ b,
          allRequestParityCapacityCoefficient tail (priority k b)
            (inspectionProbability k b) /
          (level k - allRequestFixedOffset (priority k b)
            (inspectionProbability k b) (noninspectionPenalty k b)) := by
          exact finite_reciprocalCapacity_at_parity_eq
            (fun _ _ ↦ tail) priority inspectionProbability
            noninspectionPenalty level hrisk hprobability hlevel
    _ = sla2026ExcessCapacity capacity admitted := by
          simpa [heterogeneousParityCapacityUse] using hbind

/-! ## Efficient-endpoint share algebra -/

/-- Strictly positive source primitives make the source effective load
strictly positive. -/
theorem sla2026EffectiveLoad_pos
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b) :
    0 < sla2026EffectiveLoad tail admitted priority := by
  classical
  unfold sla2026EffectiveLoad
  exact Finset.sum_pos
    (fun k _hk ↦ Finset.sum_pos
      (fun b _hb ↦ Real.sqrt_pos.2
        (mul_pos (mul_pos htail (hadmitted k b)) (hpriority k b)))
      Finset.univ_nonempty)
    Finset.univ_nonempty

/-- Every displayed source efficiency delay is strictly positive. -/
theorem sla2026EfficientDelay_pos
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    ∀ k b, 0 < sla2026EfficientDelay tail capacity admitted priority k b := by
  intro k b
  unfold sla2026EfficientDelay
  apply mul_pos
  · exact div_pos (sla2026EffectiveLoad_pos htail hadmitted hpriority) hexcess
  · apply Real.sqrt_pos.2
    exact div_pos htail (mul_pos (hadmitted k b) (hpriority k b))

/-- The displayed square-root source endpoint exhausts reciprocal capacity. -/
theorem sla2026_efficient_capacity_binds
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    (∑ k, ∑ b,
      tail / sla2026EfficientDelay tail capacity admitted priority k b) =
      sla2026ExcessCapacity capacity admitted := by
  have hformula : ∀ k b,
      sla2026EfficientDelay tail capacity admitted priority k b =
        boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
          admitted priority (sla2026ExcessCapacity capacity admitted) k b := by
    intro k b
    exact sla2026EfficientDelay_eq_boroughSeparatedAllocationDelay
      htail hadmitted hpriority k b
  calc
    (∑ k, ∑ b,
        tail / sla2026EfficientDelay tail capacity admitted priority k b) =
        ∑ k, ∑ b, tail /
          boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
            admitted priority (sla2026ExcessCapacity capacity admitted) k b := by
          simp_rw [hformula]
    _ = reciprocalCapacityUse
          (boroughSeparatedTail (Borough := Borough) (fun _ : Category ↦ tail))
          (fun i ↦ boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
            admitted priority (sla2026ExcessCapacity capacity admitted) i.1 i.2) := by
          unfold reciprocalCapacityUse boroughSeparatedTail
          rw [Fintype.sum_prod_type]
    _ = sla2026ExcessCapacity capacity admitted := by
          simpa [boroughSeparatedAllocationDelay] using
            (reciprocalCapacityUse_squareRootAllocationDelay
              (tail := boroughSeparatedTail (Borough := Borough)
                (fun _ : Category ↦ tail))
              (weight := boroughSeparatedWeight admitted priority)
              (fun i ↦ by simpa [boroughSeparatedTail] using htail)
              (fun i ↦ by
                simpa [boroughSeparatedWeight] using
                  mul_pos (hadmitted i.1 i.2) (hpriority i.1 i.2))
              hexcess)

/-- The served-delay value of the displayed efficiency endpoint is
`A_eff(s)^2 / E(s)`. -/
theorem sla2026_servedDelayCost_efficientDelay
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    sla2026ServedDelayCost admitted priority
      (sla2026EfficientDelay tail capacity admitted priority) =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
        sla2026ExcessCapacity capacity admitted := by
  have hformula :
      (fun i : Category × Borough ↦
        sla2026EfficientDelay tail capacity admitted priority i.1 i.2) =
      (fun i ↦ boroughSeparatedAllocationDelay (fun _ : Category ↦ tail)
        admitted priority (sla2026ExcessCapacity capacity admitted) i.1 i.2) := by
    funext i
    exact sla2026EfficientDelay_eq_boroughSeparatedAllocationDelay
      htail hadmitted hpriority i.1 i.2
  rw [sla2026ServedDelayCost_eq_boroughSeparated, hformula,
    servedDelayEfficiency_boroughSeparatedAllocationDelay
      (fun _ ↦ htail) hadmitted hpriority hexcess,
    ← sla2026EffectiveLoad_eq_boroughSeparatedRoot]

/-- At the square-root endpoint, each served-delay cell cost is the total
efficient value times that cell's source capacity share. -/
theorem sla2026_efficient_cell_cost_eq_capacityShare
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (k : Category) (b : Borough) :
    admitted k b * priority k b *
        sla2026EfficientDelay tail capacity admitted priority k b =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority) k b := by
  let load := admitted k b * priority k b
  let effective := sla2026EffectiveLoad tail admitted priority
  let excess := sla2026ExcessCapacity capacity admitted
  let root := Real.sqrt (tail / load)
  have hload : 0 < load := mul_pos (hadmitted k b) (hpriority k b)
  have heffective : 0 < effective :=
    sla2026EffectiveLoad_pos htail hadmitted hpriority
  have hroot : 0 < root := Real.sqrt_pos.2 (div_pos htail hload)
  change load * (effective / excess * root) =
    effective ^ 2 / excess * (tail / (excess * (effective / excess * root)))
  have hrootSq : root ^ 2 = tail / load := by
    dsimp [root]
    exact Real.sq_sqrt (div_nonneg htail.le hload.le)
  have hrootMul : load * root ^ 2 = tail := by
    rw [hrootSq]
    field_simp [hload.ne']
  field_simp [heffective.ne', hexcess.ne', hroot.ne']
  rw [hrootMul]

/-- Rewriting a cell at any positive delay through the efficient share. -/
theorem sla2026_cell_servedDelayCost_eq_share_square_div
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ} {admitted priority : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hequitable : ∀ k b, 0 < equitable k b)
    (k : Category) (b : Borough) :
    admitted k b * priority k b * equitable k b =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority) k b ^ 2 /
          sla2026CapacityShare tail capacity admitted equitable k b := by
  let efficient := sla2026EfficientDelay tail capacity admitted priority
  have hefficient : ∀ k b, 0 < efficient k b :=
    sla2026EfficientDelay_pos htail hadmitted hpriority hexcess
  have hcell := sla2026_efficient_cell_cost_eq_capacityShare
    htail hadmitted hpriority hexcess k b
  have hcell' : admitted k b * priority k b * efficient k b =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026CapacityShare tail capacity admitted efficient k b := by
    simpa [efficient] using hcell
  have hratio : admitted k b * priority k b * equitable k b =
      (admitted k b * priority k b * efficient k b) *
        (sla2026CapacityShare tail capacity admitted efficient k b /
          sla2026CapacityShare tail capacity admitted equitable k b) := by
    unfold sla2026CapacityShare
    field_simp [htail.ne', hexcess.ne', (hefficient k b).ne',
      (hequitable k b).ne']
  calc
    admitted k b * priority k b * equitable k b =
        (admitted k b * priority k b * efficient k b) *
          (sla2026CapacityShare tail capacity admitted efficient k b /
            sla2026CapacityShare tail capacity admitted equitable k b) := hratio
    _ = (sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026CapacityShare tail capacity admitted efficient k b) *
          (sla2026CapacityShare tail capacity admitted efficient k b /
            sla2026CapacityShare tail capacity admitted equitable k b) := by
          rw [hcell']
    _ = sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026CapacityShare tail capacity admitted efficient k b ^ 2 /
          sla2026CapacityShare tail capacity admitted equitable k b := by
          field_simp [hexcess.ne',
            (sla2026CapacityShare_pos htail hexcess hefficient k b).ne',
            (sla2026CapacityShare_pos htail hexcess hequitable k b).ne']

/-! ## Exact price identity -/

/--
The active source's price of equity is exactly its efficient served-delay
value times the Pearson chi-square divergence between the efficient and
equitable capacity-share vectors.
-/
theorem sla2026_price_of_equity_chi_square
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026PearsonChiSquare
          (sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority))
          (sla2026CapacityShare tail capacity admitted equitable) := by
  let efficient := sla2026EfficientDelay tail capacity admitted priority
  let efficientShare := sla2026CapacityShare tail capacity admitted efficient
  let equitableShare := sla2026CapacityShare tail capacity admitted equitable
  let effective := sla2026EffectiveLoad tail admitted priority
  let excess := sla2026ExcessCapacity capacity admitted
  change sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
      equitable efficient =
    effective ^ 2 / excess *
      sla2026PearsonChiSquare efficientShare equitableShare
  have hefficient : ∀ k b, 0 < efficient k b :=
    sla2026EfficientDelay_pos htail hadmitted hpriority hexcess
  have hequitable : ∀ k b, 0 < equitable k b := hbest.1.1
  have hefficientBind : (∑ k, ∑ b, tail / efficient k b) = excess := by
    simpa [efficient, excess] using
      (sla2026_efficient_capacity_binds htail hadmitted hpriority hexcess)
  have hequitableBind : (∑ k, ∑ b, tail / equitable k b) = excess := by
    simpa [excess] using
      (sla2026_equitable_capacity_binds htail harrival hadmitted hpriority
        hexcess hbest)
  have hefficientShareMass : sla2026VectorMass efficientShare = 1 := by
    simpa [efficientShare, excess] using
      (sla2026CapacityShare_mass_eq_one hexcess hefficientBind)
  have hequitableShareMass : sla2026VectorMass equitableShare = 1 := by
    simpa [equitableShare, excess] using
      (sla2026CapacityShare_mass_eq_one hexcess hequitableBind)
  have hequitableSharePos : ∀ k b, 0 < equitableShare k b := by
    simpa [equitableShare, excess] using
      (sla2026CapacityShare_pos htail hexcess hequitable)
  have hequitableValue : sla2026ServedDelayCost admitted priority equitable =
      effective ^ 2 / excess *
        (∑ k, ∑ b, efficientShare k b ^ 2 / equitableShare k b) := by
    calc
      sla2026ServedDelayCost admitted priority equitable =
          ∑ k, ∑ b, admitted k b * priority k b * equitable k b := rfl
      _ = ∑ k, ∑ b, (effective ^ 2 / excess) *
          (efficientShare k b ^ 2 / equitableShare k b) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro b _hb
          simpa [efficient, efficientShare, equitableShare, effective, excess,
            div_eq_mul_inv, mul_assoc]
            using (sla2026_cell_servedDelayCost_eq_share_square_div
              htail hadmitted hpriority hexcess hequitable k b)
      _ = effective ^ 2 / excess *
          (∑ k, ∑ b, efficientShare k b ^ 2 / equitableShare k b) := by
          calc
            (∑ k, ∑ b, effective ^ 2 / excess *
                (efficientShare k b ^ 2 / equitableShare k b)) =
                ∑ k, effective ^ 2 / excess *
                  (∑ b, efficientShare k b ^ 2 / equitableShare k b) := by
              apply Finset.sum_congr rfl
              intro k _hk
              exact (Finset.mul_sum Finset.univ
                (fun b ↦ efficientShare k b ^ 2 / equitableShare k b)
                (effective ^ 2 / excess)).symm
            _ = effective ^ 2 / excess *
                (∑ k, ∑ b, efficientShare k b ^ 2 / equitableShare k b) := by
              exact (Finset.mul_sum Finset.univ
                (fun k ↦ ∑ b, efficientShare k b ^ 2 / equitableShare k b)
                (effective ^ 2 / excess)).symm
  have hefficientValue : sla2026ServedDelayCost admitted priority efficient =
      effective ^ 2 / excess := by
    simpa [efficient, effective, excess] using
      (sla2026_servedDelayCost_efficientDelay htail hadmitted hpriority hexcess)
  have hpearson :
      (∑ k, ∑ b, efficientShare k b ^ 2 / equitableShare k b) =
        1 + sla2026PearsonChiSquare efficientShare equitableShare :=
    sla2026_square_div_eq_one_add_pearson
      hefficientShareMass hequitableShareMass hequitableSharePos
  calc
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable efficient =
        sla2026ServedDelayCost admitted priority equitable -
          sla2026ServedDelayCost admitted priority efficient := by
          unfold sla2026PriceOfEquity
          rw [sla2026Efficiency_eq_servedDelayCost_add_fixed
              arrival admitted priority noninspectionPenalty equitable
              (fun k b ↦ (harrival k b).ne'),
            sla2026Efficiency_eq_servedDelayCost_add_fixed
              arrival admitted priority noninspectionPenalty efficient
              (fun k b ↦ (harrival k b).ne')]
          ring
    _ = effective ^ 2 / excess *
          (∑ k, ∑ b, efficientShare k b ^ 2 / equitableShare k b) -
          effective ^ 2 / excess := by
          rw [hequitableValue, hefficientValue]
    _ = effective ^ 2 / excess *
          ((∑ k, ∑ b, efficientShare k b ^ 2 / equitableShare k b) - 1) := by
          ring
    _ = effective ^ 2 / excess *
          sla2026PearsonChiSquare efficientShare equitableShare := by
          rw [hpearson]
          ring

/-! ## Nonnegativity and the source zero characterizations -/

/-- Capacity shares determine positive delay profiles injectively. -/
theorem sla2026CapacityShare_eq_iff_delay_eq
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity : ℝ} {admitted x y : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hx : ∀ k b, 0 < x k b)
    (hy : ∀ k b, 0 < y k b) :
    sla2026CapacityShare tail capacity admitted x =
      sla2026CapacityShare tail capacity admitted y ↔ x = y := by
  constructor
  · intro hshare
    funext k b
    have hcell := congrFun (congrFun hshare k) b
    unfold sla2026CapacityShare at hcell
    have hxden : sla2026ExcessCapacity capacity admitted * x k b ≠ 0 :=
      mul_ne_zero hexcess.ne' (hx k b).ne'
    have hyden : sla2026ExcessCapacity capacity admitted * y k b ≠ 0 :=
      mul_ne_zero hexcess.ne' (hy k b).ne'
    have hmul := (div_eq_div_iff hxden hyden).1 hcell
    have hscaled : sla2026ExcessCapacity capacity admitted * y k b =
        sla2026ExcessCapacity capacity admitted * x k b :=
      mul_left_cancel₀ htail.ne' hmul
    exact (mul_left_cancel₀ hexcess.ne' hscaled).symm
  · intro hdelay
    rw [hdelay]

/-- The source price of equity is nonnegative. -/
theorem sla2026_price_of_equity_nonneg
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    0 ≤ sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
      equitable (sla2026EfficientDelay tail capacity admitted priority) := by
  rw [sla2026_price_of_equity_chi_square
    htail harrival hadmitted hpriority hexcess hbest]
  apply mul_nonneg
  · exact div_nonneg (sq_nonneg _) hexcess.le
  · exact sla2026PearsonChiSquare_nonneg
      (sla2026CapacityShare_pos htail hexcess hbest.1.1)

/--
The active source's constructive upper bound: the price is at most the
arrival-weighted cost of raising every cell to its category's maximum
efficient-endpoint cost.
-/
theorem sla2026_price_of_equity_le_efficient_cost_range
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
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) ≤
      ∑ k, ∑ b, arrival k b *
        (finiteCategoryMaximum
          (sla2026Cost arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity admitted priority)) k -
          sla2026Cost arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity admitted priority) k b) := by
  let efficient := sla2026EfficientDelay tail capacity admitted priority
  have hefficient := sla2026_extreme_efficiency
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hadmitted_le_arrival hpriority
    hnoninspectionPenalty hexcess
  have hlex := sla2026EfficiencyBestEquitable_is_lexicographic hbest
  have hefficient' : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible (fun _ _ ↦ tail)
        (sla2026ExcessCapacity capacity admitted))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted priority noninspectionPenalty z)) efficient := by
    simpa [efficient, sla2026Feasible, sla2026Efficiency, sla2026Cost,
      sla2026InspectionProbability,
      finiteFixedLoadAllRequestBurdenProfile, fixedLoadAllRequestBurden,
      fixedLoadInspectionProbability] using hefficient
  have hlex' : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible (fun _ _ ↦ tail)
        (sla2026ExcessCapacity capacity admitted))
      (fun z ↦ finiteAllRequestRangeObjective
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted priority noninspectionPenalty z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted priority noninspectionPenalty z))
      equitable := by
    simpa [sla2026InspectionProbability,
      finiteFixedLoadAllRequestBurdenProfile, fixedLoadAllRequestBurden,
      fixedLoadInspectionProbability, finiteAllRequestDelayBurden] using hlex
  have hbound := finite_fixedLoadAllRequest_price_bounds
    (tail := fun _ _ ↦ tail) (arrival := arrival) (admitted := admitted)
    (risk := priority) (penalty := noninspectionPenalty)
    (excessCapacity := sla2026ExcessCapacity capacity admitted)
    (efficient := efficient) (equitable := equitable)
    (fun _ _ ↦ htail.le) harrival hadmitted hpriority hefficient' hlex'
  change sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
      equitable efficient ≤
    finiteAlignmentGap arrival
      (sla2026Cost arrival admitted priority noninspectionPenalty efficient)
  simpa [sla2026PriceOfEquity, sla2026Efficiency, sla2026Cost,
    sla2026InspectionProbability,
    finiteFixedLoadAllRequestBurdenProfile, fixedLoadAllRequestBurden,
    fixedLoadInspectionProbability] using hbound.2.1

/-- The source price is zero exactly when the equitable and efficient capacity
shares coincide. -/
theorem sla2026_price_of_equity_eq_zero_iff_capacityShare_eq
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) = 0 ↔
      sla2026CapacityShare tail capacity admitted equitable =
        sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority) := by
  have heffective : 0 < sla2026EffectiveLoad tail admitted priority :=
    sla2026EffectiveLoad_pos htail hadmitted hpriority
  have hfactor : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 /
      sla2026ExcessCapacity capacity admitted :=
    div_pos (sq_pos_of_pos heffective) hexcess
  have hequitableShare : ∀ k b, 0 <
      sla2026CapacityShare tail capacity admitted equitable k b :=
    sla2026CapacityShare_pos htail hexcess hbest.1.1
  rw [sla2026_price_of_equity_chi_square
    htail harrival hadmitted hpriority hexcess hbest]
  constructor
  · intro hzero
    have hchi : sla2026PearsonChiSquare
        (sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority))
        (sla2026CapacityShare tail capacity admitted equitable) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hfactor.ne'
    exact (sla2026PearsonChiSquare_eq_zero_iff hequitableShare).1 hchi |>.symm
  · intro hshare
    have hchi : sla2026PearsonChiSquare
        (sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority))
        (sla2026CapacityShare tail capacity admitted equitable) = 0 :=
      (sla2026PearsonChiSquare_eq_zero_iff hequitableShare).2 hshare.symm
    rw [hchi, mul_zero]

/-- The source price is zero exactly when the displayed efficiency endpoint
already has within-category constant all-request costs. -/
theorem sla2026_price_of_equity_eq_zero_iff_efficient_cost_constant
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
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) = 0 ↔
      ∃ level : Category → ℝ, ∀ k b,
        sla2026Cost arrival admitted priority noninspectionPenalty
          (sla2026EfficientDelay tail capacity admitted priority) k b = level k := by
  let efficient := sla2026EfficientDelay tail capacity admitted priority
  constructor
  · intro hzero
    have hshare : sla2026CapacityShare tail capacity admitted equitable =
        sla2026CapacityShare tail capacity admitted efficient := by
      simpa [efficient] using
        (sla2026_price_of_equity_eq_zero_iff_capacityShare_eq
          htail harrival hadmitted hpriority hexcess hbest).1 hzero
    have hequitable : ∀ k b, 0 < equitable k b := hbest.1.1
    have hefficient : ∀ k b, 0 < efficient k b :=
      sla2026EfficientDelay_pos htail hadmitted hpriority hexcess
    have hdelay : equitable = efficient :=
      (sla2026CapacityShare_eq_iff_delay_eq
        htail hexcess hequitable hefficient).1 hshare
    have hequity : sla2026Equity arrival admitted priority
        noninspectionPenalty efficient = 0 := by
      rw [← hdelay]
      exact hbest.2.1
    have hequity' : finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty efficient) = 0 := by
      simpa [sla2026Equity, sla2026Cost, sla2026InspectionProbability,
        finiteAllRequestDelayBurden] using hequity
    rcases (finiteAllRequestRangeObjective_eq_zero_iff_exists_levels _).1
        hequity' with ⟨level, hlevel⟩
    refine ⟨level, ?_⟩
    intro k b
    simpa [sla2026Cost, sla2026InspectionProbability,
      finiteAllRequestDelayBurden] using hlevel k b
  · rintro ⟨level, hconstant⟩
    have hconstant' : ∀ k b, finiteAllRequestDelayBurden priority
        (sla2026InspectionProbability arrival admitted)
        noninspectionPenalty efficient k b = level k := by
      intro k b
      simpa [sla2026Cost, sla2026InspectionProbability,
        finiteAllRequestDelayBurden] using hconstant k b
    have hequity' : finiteAllRequestRangeObjective
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty efficient) = 0 :=
      finiteAllRequestRangeObjective_eq_zero_of_constant
        (finiteAllRequestDelayBurden priority
          (sla2026InspectionProbability arrival admitted)
          noninspectionPenalty efficient) level hconstant'
    have hequity : sla2026Equity arrival admitted priority
        noninspectionPenalty efficient = 0 := by
      simpa [sla2026Equity, sla2026Cost, sla2026InspectionProbability,
        finiteAllRequestDelayBurden] using hequity'
    have heff := sla2026_extreme_efficiency
      (tail := tail) (capacity := capacity) (arrival := arrival)
      (admitted := admitted) (priority := priority)
      (noninspectionPenalty := noninspectionPenalty)
      htail harrival hadmitted hadmitted_le_arrival hpriority
      hnoninspectionPenalty hexcess
    have hle : sla2026Efficiency arrival admitted priority noninspectionPenalty
        equitable ≤ sla2026Efficiency arrival admitted priority
          noninspectionPenalty efficient :=
      hbest.2.2 efficient heff.1 (by simpa [efficient] using hequity)
    have hge : sla2026Efficiency arrival admitted priority noninspectionPenalty
        efficient ≤ sla2026Efficiency arrival admitted priority
          noninspectionPenalty equitable := by
      simpa [efficient] using heff.2 equitable hbest.1
    change sla2026Efficiency arrival admitted priority noninspectionPenalty equitable -
      sla2026Efficiency arrival admitted priority noninspectionPenalty efficient = 0
    linarith

/--
The non-scaling clauses of active source Proposition `costofequity`, stated
directly over source primitives and the source's efficiency-best equitable
endpoint.  In particular, neither the chi-square identity nor the endpoint
description takes a capacity-binding certificate as a premise.
-/
theorem sla2026_price_of_equity_proposition_core
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
    sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) =
      sla2026EffectiveLoad tail admitted priority ^ 2 /
          sla2026ExcessCapacity capacity admitted *
        sla2026PearsonChiSquare
          (sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority))
          (sla2026CapacityShare tail capacity admitted equitable) ∧
      0 ≤ sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) ∧
      sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (sla2026EfficientDelay tail capacity admitted priority) ≤
        ∑ k, ∑ b, arrival k b *
          (finiteCategoryMaximum
            (sla2026Cost arrival admitted priority noninspectionPenalty
              (sla2026EfficientDelay tail capacity admitted priority)) k -
            sla2026Cost arrival admitted priority noninspectionPenalty
              (sla2026EfficientDelay tail capacity admitted priority) k b) ∧
      (sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (sla2026EfficientDelay tail capacity admitted priority) = 0 ↔
        sla2026CapacityShare tail capacity admitted equitable =
          sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority)) ∧
      (sla2026CapacityShare tail capacity admitted equitable =
          sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority) ↔
        ∃ level : Category → ℝ, ∀ k b,
          sla2026Cost arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity admitted priority) k b = level k) := by
  have hidentity := sla2026_price_of_equity_chi_square
    htail harrival hadmitted hpriority hexcess hbest
  have hnonneg := sla2026_price_of_equity_nonneg
    htail harrival hadmitted hpriority hexcess hbest
  have hbound := sla2026_price_of_equity_le_efficient_cost_range
    htail harrival hadmitted hadmitted_le_arrival hpriority
    hnoninspectionPenalty hexcess hbest
  have hzeroShare := sla2026_price_of_equity_eq_zero_iff_capacityShare_eq
    htail harrival hadmitted hpriority hexcess hbest
  have hzeroCost := sla2026_price_of_equity_eq_zero_iff_efficient_cost_constant
    htail harrival hadmitted hadmitted_le_arrival hpriority
    hnoninspectionPenalty hexcess hbest
  refine ⟨hidentity, hnonneg, hbound, hzeroShare, ?_⟩
  constructor
  · intro hshare
    exact hzeroCost.1 (hzeroShare.2 hshare)
  · intro hconstant
    exact hzeroShare.1 (hzeroCost.2 hconstant)

end

end LG24ServiceLevelAgreements
