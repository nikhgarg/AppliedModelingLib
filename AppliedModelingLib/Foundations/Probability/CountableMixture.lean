import AppliedModelingLib.Foundations.Probability.MeasureTransport

/-!
# Countable probability mixtures

This module packages a countably indexed weighted sum of probability laws and
the corresponding mixture of couplings. It is the reusable measure-theoretic
primitive needed to assemble shellwise transport plans without silently
replacing a countable partition by a finite one.

## Library provenance

The construction directly uses Mathlib's `Measure.sum_apply` from
[`MeasureTheory/Measure/MeasureSpace.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/MeasureSpace.lean),
and `Measure.map_sum` from
[`MeasureTheory/Measure/AEMeasurable.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/AEMeasurable.lean),
with `Measure.map_smul` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
while the one-residual/countable-family normalization directly uses
`ENNReal.tsum_sigma'` from
[`Topology/Algebra/InfiniteSum/ENNReal.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean),
and `ENNReal.inv_mul_cancel` / `ENNReal.mul_div_cancel` from
[`Data/ENNReal/Inv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Inv.lean),
and `lintegral_sum_measure` / `lintegral_smul_measure` from
[`MeasureTheory/Integral/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/

namespace AppliedModelingLib
namespace Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The underlying measure of a countable weighted mixture of probability laws. -/
noncomputable def countableMixtureMeasure {ι α : Type*} [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (law : ι → ProbabilityMeasure α) : Measure α :=
  Measure.sum fun i => weight i • (law i : Measure α)

/--
The index family for a mixture formed from one residual component and an
arbitrary indexed family of common components. `false` selects the singleton
residual branch, while `true` selects an index of the common family.
-/
def residualMixtureIndexFamily.{u} (ι : Type u) : Bool → Type u
  | false => ULift.{u} PUnit
  | true => ι

/--
Weights for one residual component followed by an indexed common family.
This representation avoids an artificial `Nat` reindexing when a measure
construction has one residual part plus countably many local parts.
-/
def residualMixtureWeight {ι : Type*} (residual : ℝ≥0∞) (weight : ι → ℝ≥0∞) :
    (Σ branch, residualMixtureIndexFamily ι branch) → ℝ≥0∞
  | ⟨false, _⟩ => residual
  | ⟨true, index⟩ => weight index

/--
If the common components have total mass at most one, adjoining a residual of
mass `1 - commonMass` gives a probability-weight family. This is the exact
mass bookkeeping primitive used by shellwise couplings with an excess-mass
residual component.
-/
theorem hasSum_residualMixtureWeight {ι : Type*}
    (weight : ι → ℝ≥0∞) (commonMass : ℝ≥0∞)
    (hweight : HasSum weight commonMass) (hcommon_le : commonMass ≤ 1) :
    HasSum (residualMixtureWeight (1 - commonMass) weight) 1 := by
  convert ENNReal.summable.hasSum
    (f := residualMixtureWeight (1 - commonMass) weight) using 1
  symm
  change ∑' z : Σ branch : Bool, residualMixtureIndexFamily ι branch,
    residualMixtureWeight (1 - commonMass) weight z = 1
  rw [ENNReal.tsum_sigma']
  simp [tsum_fintype, residualMixtureIndexFamily, residualMixtureWeight]
  rw [hweight.tsum_eq, add_comm]
  exact tsub_add_cancel_of_le hcommon_le

/-- Normalizing a nonzero finite-mass weight family gives probability weights. -/
theorem hasSum_div_normalizeWeight {ι : Type*}
    (weight : ι → ℝ≥0∞) (weightMass : ℝ≥0∞)
    (hweight : HasSum weight weightMass)
    (hweight_ne_zero : weightMass ≠ 0) (hweight_ne_top : weightMass ≠ ∞) :
    HasSum (fun index => weight index / weightMass) 1 := by
  convert ENNReal.summable.hasSum
    (f := fun index => weight index / weightMass) using 1
  symm
  rw [show (fun index => weight index / weightMass) =
      (fun index => weightMass⁻¹ * weight index) by
        funext index
        rw [div_eq_mul_inv, mul_comm], ENNReal.tsum_mul_left, hweight.tsum_eq,
    ENNReal.inv_mul_cancel hweight_ne_zero hweight_ne_top]

/--
Scaling the normalized countable mixture by its nonzero finite total mass
recovers the unnormalized weighted measure.
-/
theorem smul_countableMixtureMeasure_div_normalizeWeight {ι α : Type*}
    [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (weightMass : ℝ≥0∞)
    (hweight_ne_zero : weightMass ≠ 0) (hweight_ne_top : weightMass ≠ ∞)
    (law : ι → ProbabilityMeasure α) :
    weightMass • countableMixtureMeasure (fun index => weight index / weightMass) law =
      countableMixtureMeasure weight law := by
  ext s hs
  simp only [countableMixtureMeasure, Measure.smul_apply, Measure.sum_apply _ hs,
    smul_eq_mul]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro index
  rw [← mul_assoc, ENNReal.mul_div_cancel hweight_ne_zero hweight_ne_top]

/--
The law family for one residual probability law and an indexed common family.
-/
def residualMixtureLaw {ι α : Type*} [MeasurableSpace α]
    (residual : ProbabilityMeasure α) (law : ι → ProbabilityMeasure α) :
    (Σ branch, residualMixtureIndexFamily ι branch) → ProbabilityMeasure α
  | ⟨false, _⟩ => residual
  | ⟨true, index⟩ => law index

/--
The underlying measure of a residual-plus-common mixture is the residual
measure plus the common weighted measure.
-/
theorem countableMixtureMeasure_residualMixtureLaw {ι α : Type*}
    [MeasurableSpace α]
    (residualWeight : ℝ≥0∞) (commonWeight : ι → ℝ≥0∞)
    (residual : ProbabilityMeasure α) (common : ι → ProbabilityMeasure α) :
    countableMixtureMeasure (residualMixtureWeight residualWeight commonWeight)
      (residualMixtureLaw residual common) =
      residualWeight • (residual : Measure α) +
        countableMixtureMeasure commonWeight common := by
  ext s hs
  simp only [countableMixtureMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul,
    Measure.add_apply]
  rw [ENNReal.tsum_sigma']
  simp [tsum_fintype, residualMixtureIndexFamily, residualMixtureWeight,
    residualMixtureLaw, add_comm]

/-- A countable weighted mixture of probability laws. -/
noncomputable def countableMixtureProbability {ι α : Type*} [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (law : ι → ProbabilityMeasure α)
    (hweight : HasSum weight 1) : ProbabilityMeasure α :=
  ⟨countableMixtureMeasure weight law, ⟨by
    change Measure.sum (fun i => weight i • (law i : Measure α)) Set.univ = 1
    simp only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    exact hweight.tsum_eq⟩⟩

/-- A countable mixture evaluates a measurable set by the weighted countable sum. -/
theorem countableMixtureProbability_apply {ι α : Type*} [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (law : ι → ProbabilityMeasure α)
    (hweight : HasSum weight 1) (s : Set α) (hs : MeasurableSet s) :
    (countableMixtureProbability weight law hweight : Measure α) s =
      ∑' i, weight i * (law i : Measure α) s := by
  change Measure.sum (fun i => weight i • (law i : Measure α)) s = _
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

/-- A measurable pushforward commutes with a countable probability mixture. -/
theorem measure_map_countableMixtureProbability {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (weight : ι → ℝ≥0∞) (law : ι → ProbabilityMeasure α)
    (hweight : HasSum weight 1) (f : α → β) (hf : Measurable f) :
    Measure.map f (countableMixtureProbability weight law hweight : Measure α) =
      countableMixtureMeasure weight (fun i => (law i).map hf.aemeasurable) := by
  change Measure.map f (Measure.sum fun i => weight i • (law i : Measure α)) = _
  rw [Measure.map_sum hf.aemeasurable]
  simp only [Measure.map_smul]
  rfl

/-- A measurable pushforward of a countable mixture is the mixture of pushforwards. -/
theorem countableMixtureProbability_map {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (weight : ι → ℝ≥0∞) (law : ι → ProbabilityMeasure α)
    (hweight : HasSum weight 1) (f : α → β) (hf : Measurable f) :
    (countableMixtureProbability weight law hweight).map hf.aemeasurable =
      countableMixtureProbability weight (fun i => (law i).map hf.aemeasurable) hweight := by
  apply Subtype.ext
  exact measure_map_countableMixtureProbability weight law hweight f hf

/-- A common weighted mixture of couplings couples the respective law mixtures. -/
noncomputable def countableMixtureCoupling {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (weight : ι → ℝ≥0∞) (hweight : HasSum weight 1)
    (mu : ι → ProbabilityMeasure α) (nu : ι → ProbabilityMeasure β)
    (coupling : ∀ i, ProbabilityCoupling (mu i) (nu i)) :
    ProbabilityCoupling (countableMixtureProbability weight mu hweight)
      (countableMixtureProbability weight nu hweight) where
  joint := countableMixtureProbability weight (fun i => (coupling i).joint) hweight
  map_fst := by
    rw [countableMixtureProbability_map weight (fun i => (coupling i).joint) hweight
      Prod.fst measurable_fst]
    exact congrArg (fun law : ι → ProbabilityMeasure α =>
      countableMixtureProbability weight law hweight) (funext fun i => (coupling i).map_fst)
  map_snd := by
    rw [countableMixtureProbability_map weight (fun i => (coupling i).joint) hweight
      Prod.snd measurable_snd]
    exact congrArg (fun law : ι → ProbabilityMeasure β =>
      countableMixtureProbability weight law hweight) (funext fun i => (coupling i).map_snd)

/--
One residual coupling together with an indexed family of local couplings gives
a coupling of the corresponding residual-plus-common mixtures.
-/
noncomputable def residualMixtureCoupling {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (commonWeight : ι → ℝ≥0∞) (commonMass : ℝ≥0∞)
    (hweight : HasSum (residualMixtureWeight (1 - commonMass) commonWeight) 1)
    (residualMu : ProbabilityMeasure α) (residualNu : ProbabilityMeasure β)
    (commonMu : ι → ProbabilityMeasure α) (commonNu : ι → ProbabilityMeasure β)
    (residualCoupling : ProbabilityCoupling residualMu residualNu)
    (commonCoupling : ∀ index, ProbabilityCoupling (commonMu index) (commonNu index)) :
    ProbabilityCoupling
      (countableMixtureProbability
        (residualMixtureWeight (1 - commonMass) commonWeight)
        (residualMixtureLaw residualMu commonMu) hweight)
      (countableMixtureProbability
        (residualMixtureWeight (1 - commonMass) commonWeight)
        (residualMixtureLaw residualNu commonNu) hweight) :=
  countableMixtureCoupling _ hweight _ _ fun
    | ⟨false, _⟩ => residualCoupling
    | ⟨true, index⟩ => commonCoupling index

/--
The nonnegative cost of a countable mixture coupling is the corresponding
weighted countable sum of local costs.
-/
theorem countableMixtureCoupling_cost {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (weight : ι → ℝ≥0∞) (hweight : HasSum weight 1)
    (mu : ι → ProbabilityMeasure α) (nu : ι → ProbabilityMeasure β)
    (coupling : ∀ i, ProbabilityCoupling (mu i) (nu i))
    (cost : α × β → ℝ≥0∞) :
    (countableMixtureCoupling weight hweight mu nu coupling).cost cost =
      ∑' i, weight i * (coupling i).cost cost := by
  unfold ProbabilityCoupling.cost countableMixtureCoupling
  change ∫⁻ z, cost z ∂countableMixtureMeasure weight (fun i => (coupling i).joint) = _
  unfold countableMixtureMeasure
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

/--
For finitely many independently selectable nonnegative costs, the infimum of
the weighted total is the weighted total of the individual infima.  This is
the finite-selection form needed when an empirical law occupies only finitely
many mixture components; it does not assume that any component infimum is
attained.

Library provenance: this packages Mathlib's `ENNReal.iInf_sum` from
[`Data/ENNReal/BigOperators.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/BigOperators.lean)
and `ENNReal.mul_iInf` from
[`Data/ENNReal/Inv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Inv.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/
theorem iInf_fintype_weighted_sum
    {ι : Type*} [Fintype ι] (F : ι → Type*)
    [∀ i, Nonempty (F i)]
    (weight : ι → ℝ≥0∞) (hweight : ∀ i, weight i ≠ ∞)
    (cost : ∀ i, F i → ℝ≥0∞) :
    (⨅ choice : ∀ i, F i, ∑ i, weight i * cost i (choice i)) =
      ∑ i, weight i * ⨅ value : F i, cost i value := by
  classical
  let chooseMin : (∀ i, F i) → (∀ i, F i) → ∀ i, F i := fun left right i =>
    if h : cost i (left i) ≤ cost i (right i) then left i else right i
  have hdirected : ∀ (t : Finset ι) (left right : ∀ i, F i), ∃ selected : ∀ i, F i,
      ∀ i ∈ t,
        weight i * cost i (selected i) ≤ weight i * cost i (left i) ∧
        weight i * cost i (selected i) ≤ weight i * cost i (right i) := by
    intro t left right
    refine ⟨chooseMin left right, ?_⟩
    intro i hi
    dsimp [chooseMin]
    split_ifs with h
    · exact ⟨le_rfl, by gcongr⟩
    · exact ⟨by gcongr; exact le_of_not_ge h, le_rfl⟩
  rw [ENNReal.iInf_sum (s := Finset.univ) hdirected]
  apply Finset.sum_congr rfl
  intro i hi
  apply le_antisymm
  · let default : ∀ j, F j := fun j => Classical.choice (inferInstance : Nonempty (F j))
    let update : F i → ∀ j, F j := fun value j =>
      if h : j = i then _root_.cast (congrArg F h.symm) value else default j
    calc
      (⨅ choice : ∀ i, F i, weight i * cost i (choice i)) ≤
          ⨅ value : F i, weight i * cost i value := by
        refine le_iInf fun value => ?_
        exact iInf_le_of_le (update value) (by simp [update])
      _ = weight i * ⨅ value : F i, cost i value :=
        (ENNReal.mul_iInf (a := weight i) (f := fun value : F i => cost i value)
          (fun htop _ => (hweight i htop).elim)).symm
  · refine le_iInf fun choice => ?_
    calc
      weight i * ⨅ value : F i, cost i value =
          ⨅ value : F i, weight i * cost i value :=
        ENNReal.mul_iInf (a := weight i) (f := fun value : F i => cost i value)
          (fun htop _ => (hweight i htop).elim)
      _ ≤ weight i * cost i (choice i) :=
        iInf_le (fun value : F i => weight i * cost i value) (choice i)

/--
The nonnegative integral of a countable weighted mixture is the countable sum
of the weighted component integrals.

Library provenance: this packages Mathlib's `lintegral_sum_measure` and
`lintegral_smul_measure` from
[`MeasureTheory/Integral/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.  No source text is copied or
ported.
-/
theorem lintegral_countableMixtureMeasure {ι α : Type*} [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (law : ι → ProbabilityMeasure α) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂countableMixtureMeasure weight law) =
      ∑' i, weight i * ∫⁻ x, f x ∂(law i : Measure α) := by
  unfold countableMixtureMeasure
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

/--
The cost of a residual-plus-common mixture coupling is its residual cost plus
the countable sum of its common-component costs, weighted by their masses.
-/
theorem residualMixtureCoupling_cost {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (commonWeight : ι → ℝ≥0∞) (commonMass : ℝ≥0∞)
    (hweight : HasSum (residualMixtureWeight (1 - commonMass) commonWeight) 1)
    (residualMu : ProbabilityMeasure α) (residualNu : ProbabilityMeasure β)
    (commonMu : ι → ProbabilityMeasure α) (commonNu : ι → ProbabilityMeasure β)
    (residualCoupling : ProbabilityCoupling residualMu residualNu)
    (commonCoupling : ∀ index, ProbabilityCoupling (commonMu index) (commonNu index))
    (cost : α × β → ℝ≥0∞) :
    (residualMixtureCoupling commonWeight commonMass hweight residualMu residualNu
      commonMu commonNu residualCoupling commonCoupling).cost cost =
      (1 - commonMass) * residualCoupling.cost cost +
        ∑' index, commonWeight index * (commonCoupling index).cost cost := by
  rw [show residualMixtureCoupling commonWeight commonMass hweight residualMu residualNu
      commonMu commonNu residualCoupling commonCoupling =
    countableMixtureCoupling _ hweight _ _ fun
      | ⟨false, _⟩ => residualCoupling
      | ⟨true, index⟩ => commonCoupling index by rfl,
    countableMixtureCoupling_cost]
  rw [ENNReal.tsum_sigma']
  simp [tsum_fintype, residualMixtureIndexFamily, residualMixtureWeight, add_comm]
  rfl

end
end Probability
end AppliedModelingLib
