import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.ExtendedExpectation
import AppliedModelingLib.Foundations.Optimization.ScalarStrongDuality
import Mathlib.Data.Real.Pointwise
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace AppliedModelingLib

/-!
# Couplings of probability measures

This module provides the small general-measure transport interface needed by
distribution-shift arguments.  It deliberately keeps costs nonnegative and
extended-real valued: finiteness and real-valued moment hypotheses belong at
the theorem that needs them.
-/

/-- A joint probability law with prescribed first and second marginals. -/
structure ProbabilityCoupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) where
  joint : ProbabilityMeasure (α × β)
  map_fst : joint.map measurable_fst.aemeasurable = μ
  map_snd : joint.map measurable_snd.aemeasurable = ν

namespace ProbabilityCoupling

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : ProbabilityMeasure α} {ν : ProbabilityMeasure β}

/--
The deterministic coupling of two Dirac probability laws.  This is useful for
paper models whose induced outcome is a deterministic response, while keeping
the marginal facts in the reusable general-measure transport API.
-/
noncomputable def dirac (first : α) (second : β) :
    ProbabilityCoupling (diracProba first) (diracProba second) where
  joint := diracProba (first, second)
  map_fst := by
    apply Subtype.ext
    change Measure.map Prod.fst (Measure.dirac (first, second)) = Measure.dirac first
    rw [Measure.map_dirac' measurable_fst]
  map_snd := by
    apply Subtype.ext
    change Measure.map Prod.snd (Measure.dirac (first, second)) = Measure.dirac second
    rw [Measure.map_dirac' measurable_snd]

/-- The independent product law is a coupling of any two probability laws. -/
noncomputable def independent (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    ProbabilityCoupling μ ν where
  joint := μ.prod ν
  map_fst := ProbabilityMeasure.map_fst_prod μ ν
  map_snd := ProbabilityMeasure.map_snd_prod μ ν

/-- A convex combination of two probability measures, represented at the underlying-measure level. -/
noncomputable def ProbabilityMeasure.convexCombination
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first second : ProbabilityMeasure α) : ProbabilityMeasure α :=
  ⟨ENNReal.ofReal weight • (first : Measure α) +
    ENNReal.ofReal (1 - weight) • (second : Measure α), ⟨by
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add hweight_nonneg (sub_nonneg.mpr hweight_le_one)]
      simp⟩⟩

/-- Mixing a probability measure with itself leaves it unchanged. -/
theorem ProbabilityMeasure.convexCombination_self
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (law : ProbabilityMeasure α) :
    ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one law law = law := by
  apply ProbabilityMeasure.toMeasure_injective
  change ENNReal.ofReal weight • (law : Measure α) +
      ENNReal.ofReal (1 - weight) • (law : Measure α) = (law : Measure α)
  rw [← add_smul]
  have hsum : ENNReal.ofReal weight + ENNReal.ofReal (1 - weight) = 1 := by
    rw [← ENNReal.ofReal_add hweight_nonneg (sub_nonneg.mpr hweight_le_one)]
    simp
  rw [hsum, one_smul]

/-- Integration through a probability-measure convex combination is affine. -/
theorem integral_probabilityMeasure_convexCombination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first second : ProbabilityMeasure α) (f : α → E)
    (hfirst : Integrable f (first : Measure α))
    (hsecond : Integrable f (second : Measure α)) :
    (∫ x, f x ∂(ProbabilityMeasure.convexCombination
      weight hweight_nonneg hweight_le_one first second : Measure α)) =
      weight • (∫ x, f x ∂(first : Measure α)) +
        (1 - weight) • (∫ x, f x ∂(second : Measure α)) := by
  change (∫ x, f x ∂(ENNReal.ofReal weight • (first : Measure α) +
    ENNReal.ofReal (1 - weight) • (second : Measure α))) = _
  rw [integral_add_measure (hfirst.smul_measure (by simp))
    (hsecond.smul_measure (by simp)), integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hweight_nonneg,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hweight_le_one)]

/--
Mix two couplings with the same real coefficient.  Their marginals are mixed
with that coefficient, and the joint law is the corresponding mixture of
their joint laws.

Library provenance: the marginal calculation uses Mathlib's unchanged
`Measure.map_add`/`Measure.map_smul`; the probability-mass and integral
identities use the pinned Apache-2.0 Mathlib measure and Bochner APIs.  The
coupling construction is local and no external proof text is copied.
-/
noncomputable def convexCombination
    {μ₁ μ₂ : ProbabilityMeasure α} {ν₁ ν₂ : ProbabilityMeasure β}
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first : ProbabilityCoupling μ₁ ν₁) (second : ProbabilityCoupling μ₂ ν₂) :
    ProbabilityCoupling
      (ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one μ₁ μ₂)
      (ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one ν₁ ν₂) where
  joint := ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one
    first.joint second.joint
  map_fst := by
    apply Subtype.ext
    change Measure.map Prod.fst
        (ENNReal.ofReal weight • (first.joint : Measure (α × β)) +
          ENNReal.ofReal (1 - weight) • (second.joint : Measure (α × β))) =
      ENNReal.ofReal weight • (μ₁ : Measure α) +
        ENNReal.ofReal (1 - weight) • (μ₂ : Measure α)
    have hfirst : Measure.map Prod.fst (first.joint : Measure (α × β)) = (μ₁ : Measure α) :=
      congrArg ProbabilityMeasure.toMeasure first.map_fst
    have hsecond : Measure.map Prod.fst (second.joint : Measure (α × β)) = (μ₂ : Measure α) :=
      congrArg ProbabilityMeasure.toMeasure second.map_fst
    rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hfirst, hsecond]
  map_snd := by
    apply Subtype.ext
    change Measure.map Prod.snd
        (ENNReal.ofReal weight • (first.joint : Measure (α × β)) +
          ENNReal.ofReal (1 - weight) • (second.joint : Measure (α × β))) =
      ENNReal.ofReal weight • (ν₁ : Measure β) +
        ENNReal.ofReal (1 - weight) • (ν₂ : Measure β)
    have hfirst : Measure.map Prod.snd (first.joint : Measure (α × β)) = (ν₁ : Measure β) :=
      congrArg ProbabilityMeasure.toMeasure first.map_snd
    have hsecond : Measure.map Prod.snd (second.joint : Measure (α × β)) = (ν₂ : Measure β) :=
      congrArg ProbabilityMeasure.toMeasure second.map_snd
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, hfirst, hsecond]

/--
The deterministic graph coupling of a probability law and its measurable
pushforward.  This is the transport interface used by truncation and shell
maps in empirical-Wasserstein arguments: its cost is exactly the expected
pointwise movement of the map.

Library provenance: this uses Mathlib's `ProbabilityMeasure.map` and
`ProbabilityMeasure.toMeasure_map` from
[`MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean),
and `Measure.map_map` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.  No source text is copied or
ported.
-/
noncomputable def graph (μ : ProbabilityMeasure α) (T : α → α)
    (hT : Measurable T) : ProbabilityCoupling μ (μ.map hT.aemeasurable) where
  joint := μ.map (measurable_id.prodMk hT).aemeasurable
  map_fst := by
    apply Subtype.ext
    change Measure.map Prod.fst (Measure.map (fun x : α => (x, T x)) (μ : Measure α)) =
      (μ : Measure α)
    have hgraph : Measurable (fun x : α => (x, T x)) := measurable_id.prodMk hT
    rw [Measure.map_map measurable_fst hgraph]
    change Measure.map id (μ : Measure α) = (μ : Measure α)
    rw [Measure.map_id]
  map_snd := by
    apply Subtype.ext
    change Measure.map Prod.snd (Measure.map (fun x : α => (x, T x)) (μ : Measure α)) =
      Measure.map T (μ : Measure α)
    have hgraph : Measurable (fun x : α => (x, T x)) := measurable_id.prodMk hT
    rw [Measure.map_map measurable_snd hgraph]
    rfl

/-- The diagonal coupling of a probability law with itself. -/
noncomputable def refl (μ : ProbabilityMeasure α) : ProbabilityCoupling μ μ where
  joint := μ.map (measurable_id.prodMk measurable_id).aemeasurable
  map_fst := by
    apply Subtype.ext
    change Measure.map Prod.fst
      (Measure.map (fun x : α => (x, x)) (μ : Measure α)) = (μ : Measure α)
    have hdiag : Measurable (fun x : α => (x, x)) :=
      measurable_id.prodMk measurable_id
    rw [Measure.map_map measurable_fst hdiag]
    simp [Function.comp_def]
  map_snd := by
    apply Subtype.ext
    change Measure.map Prod.snd
      (Measure.map (fun x : α => (x, x)) (μ : Measure α)) = (μ : Measure α)
    have hdiag : Measurable (fun x : α => (x, x)) :=
      measurable_id.prodMk measurable_id
    rw [Measure.map_map measurable_snd hdiag]
    simp [Function.comp_def]

/--
Reverse the coordinates of a probability coupling.  This is the general-law
counterpart of `FiniteCoupling.swap`: it is needed when an adversarial law is
constructed as the pushforward of a nominal law, while a transport statement
uses the adversarial law as its first marginal.

Library provenance: this uses Mathlib's `Measure.map_map` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean)
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.  No source text is copied or
ported.
-/
noncomputable def swap (π : ProbabilityCoupling μ ν) : ProbabilityCoupling ν μ where
  joint := π.joint.map (measurable_snd.prodMk measurable_fst).aemeasurable
  map_fst := by
    apply Subtype.ext
    change Measure.map Prod.fst
        (Measure.map (fun pair : α × β => (pair.2, pair.1)) (π.joint : Measure (α × β))) =
      (ν : Measure β)
    rw [Measure.map_map measurable_fst (measurable_snd.prodMk measurable_fst)]
    simpa using congrArg ProbabilityMeasure.toMeasure π.map_snd
  map_snd := by
    apply Subtype.ext
    change Measure.map Prod.snd
        (Measure.map (fun pair : α × β => (pair.2, pair.1)) (π.joint : Measure (α × β))) =
      (μ : Measure α)
    rw [Measure.map_map measurable_snd (measurable_snd.prodMk measurable_fst)]
    simpa using congrArg ProbabilityMeasure.toMeasure π.map_fst

/--
Integrating through a reversed coupling is the same as integrating the
coordinate-reversed observable through the original coupling.

Library provenance: this is Mathlib's `integral_map` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`; the coupling statement and
coordinate-reversal bridge are local, and no source text is copied or ported.
-/
theorem integral_swap (π : ProbabilityCoupling μ ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : β × α → E)
    (hf : AEStronglyMeasurable f (π.swap.joint : Measure (β × α))) :
    (∫ z, f z ∂(π.swap.joint : Measure (β × α))) =
      ∫ z, f (z.2, z.1) ∂(π.joint : Measure (α × β)) := by
  change (∫ z, f z ∂Measure.map (fun pair : α × β => (pair.2, pair.1))
    (π.joint : Measure (α × β))) = _
  exact integral_map (measurable_snd.prodMk measurable_fst).aemeasurable hf

/-- Integrability through a reversed coupling is exactly integrability of the
coordinate-reversed observable through the original coupling. -/
theorem integrable_swap_iff (π : ProbabilityCoupling μ ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : β × α → E)
    (hf : AEStronglyMeasurable f (π.swap.joint : Measure (β × α))) :
    Integrable f (π.swap.joint : Measure (β × α)) ↔
      Integrable (fun z : α × β => f (z.2, z.1)) (π.joint : Measure (α × β)) := by
  change Integrable f (Measure.map (fun pair : α × β => (pair.2, pair.1))
    (π.joint : Measure (α × β))) ↔ _
  simpa [Function.comp_def] using
    (integrable_map_measure hf (measurable_snd.prodMk measurable_fst).aemeasurable)

/-- The reversed graph coupling is the pushforward of its base law by the
map `x ↦ (T x, x)`. -/
theorem graph_swap_joint (μ : ProbabilityMeasure α) (T : α → α)
    (hT : Measurable T) :
    ((graph μ T hT).swap.joint : Measure (α × α)) =
      Measure.map (fun x : α => (T x, x)) (μ : Measure α) := by
  change Measure.map (fun pair : α × α => (pair.2, pair.1))
      (Measure.map (fun x : α => (x, T x)) (μ : Measure α)) = _
  have hswap : Measurable (fun pair : α × α => (pair.2, pair.1)) :=
    measurable_snd.prodMk measurable_fst
  have hgraph : Measurable (fun x : α => (x, T x)) :=
    measurable_id.prodMk hT
  rw [Measure.map_map hswap hgraph]
  rfl

/-- Integrate an observable of an induced state and its nominal antecedent
through the reversed graph coupling. -/
theorem integral_graph_swap (μ : ProbabilityMeasure α) (T : α → α)
    (hT : Measurable T) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α × α → E)
    (hf : AEStronglyMeasurable f ((graph μ T hT).swap.joint : Measure (α × α))) :
    (∫ z, f z ∂((graph μ T hT).swap.joint : Measure (α × α))) =
      ∫ x, f (T x, x) ∂(μ : Measure α) := by
  rw [graph_swap_joint] at hf ⊢
  have hpair : Measurable (fun x : α => (T x, x)) :=
    hT.prodMk measurable_id
  rw [integral_map hpair.aemeasurable hf]

/-- The corresponding integrability transfer for a reversed graph coupling. -/
theorem integrable_graph_swap_iff (μ : ProbabilityMeasure α) (T : α → α)
    (hT : Measurable T) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α × α → E)
    (hf : AEStronglyMeasurable f ((graph μ T hT).swap.joint : Measure (α × α))) :
    Integrable f ((graph μ T hT).swap.joint : Measure (α × α)) ↔
      Integrable (fun x => f (T x, x)) (μ : Measure α) := by
  rw [graph_swap_joint] at hf ⊢
  have hpair : Measurable (fun x : α => (T x, x)) :=
    hT.prodMk measurable_id
  simpa [Function.comp_def] using (integrable_map_measure hf hpair.aemeasurable)

/--
An explicitly measurable selector turns a pointwise payoff bound into the
corresponding bound for its reversed graph coupling.  This isolates the exact
selection obligation in general-law transport-duality arguments: the theorem
does not assume that such a selector exists.
-/
theorem integral_le_integral_graph_swap_of_forall_le
    (μ : ProbabilityMeasure α) (T : α → α) (hT : Measurable T)
    {f : α → ℝ} {g : α × α → ℝ}
    (hf : Integrable f (μ : Measure α))
    (hg : Integrable (fun x => g (T x, x)) (μ : Measure α))
    (hg_measurable : Measurable g)
    (hdom : ∀ x, f x ≤ g (T x, x)) :
    (∫ x, f x ∂(μ : Measure α)) ≤
      ∫ z, g z ∂((graph μ T hT).swap.joint : Measure (α × α)) := by
  calc
    (∫ x, f x ∂(μ : Measure α)) ≤ ∫ x, g (T x, x) ∂(μ : Measure α) :=
      integral_mono hf hg hdom
    _ = ∫ z, g z ∂((graph μ T hT).swap.joint : Measure (α × α)) :=
      (integral_graph_swap μ T hT g hg_measurable.aestronglyMeasurable).symm

/--
Under the independent coupling, integrable first moments make the metric
distance integrable.  This is the basic finite-first-moment bridge needed to
interpret real-valued Wasserstein-1 costs.
-/
theorem integrable_dist_independent
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ ν : ProbabilityMeasure E)
    (hμ : Integrable (fun x : E => ‖x‖) (μ : Measure E))
    (hν : Integrable (fun x : E => ‖x‖) (ν : Measure E)) :
    Integrable (fun z : E × E => dist z.1 z.2)
      ((independent μ ν).joint : Measure (E × E)) := by
  change Integrable (fun z : E × E => dist z.1 z.2)
    ((μ : Measure E).prod (ν : Measure E))
  have hsum : Integrable (fun z : E × E => ‖z.1‖ + ‖z.2‖)
      ((μ : Measure E).prod (ν : Measure E)) :=
    (hμ.comp_fst (ν : Measure E)).add (hν.comp_snd (μ : Measure E))
  refine hsum.mono measurable_dist.aestronglyMeasurable ?_
  filter_upwards with z
  have htriangle : dist z.1 z.2 ≤ dist z.1 0 + dist 0 z.2 :=
    dist_triangle z.1 0 z.2
  have hsum_nonneg : 0 ≤ ‖z.1‖ + ‖z.2‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, abs_of_nonneg hsum_nonneg,
    dist_zero_right, dist_zero_left] using htriangle

/-- The nonnegative expected cost of a coupling. -/
noncomputable def cost (π : ProbabilityCoupling μ ν) (c : α × β → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z, c z ∂(π.joint : Measure (α × β))

/-- Integrating a measurable nonnegative function through the first marginal. -/
theorem lintegral_fst (π : ProbabilityCoupling μ ν) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂(μ : Measure α)) = ∫⁻ z, f z.1 ∂(π.joint : Measure (α × β)) := by
  have hmap : Measure.map Prod.fst (π.joint : Measure (α × β)) = (μ : Measure α) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_fst
  calc
    (∫⁻ x, f x ∂(μ : Measure α)) =
        ∫⁻ x, f x ∂Measure.map Prod.fst (π.joint : Measure (α × β)) := by rw [hmap]
    _ = ∫⁻ z, f z.1 ∂(π.joint : Measure (α × β)) :=
      lintegral_map hf measurable_fst

/-- Integrating a measurable nonnegative function through the second marginal. -/
theorem lintegral_snd (π : ProbabilityCoupling μ ν) {f : β → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ y, f y ∂(ν : Measure β)) = ∫⁻ z, f z.2 ∂(π.joint : Measure (α × β)) := by
  have hmap : Measure.map Prod.snd (π.joint : Measure (α × β)) = (ν : Measure β) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_snd
  calc
    (∫⁻ y, f y ∂(ν : Measure β)) =
        ∫⁻ y, f y ∂Measure.map Prod.snd (π.joint : Measure (α × β)) := by rw [hmap]
    _ = ∫⁻ z, f z.2 ∂(π.joint : Measure (α × β)) :=
      lintegral_map hf measurable_snd

/--
The cost of the independent coupling is bounded by the sum of the two radial
first moments.  This is the reusable product-residual estimate used when a
countable transport construction leaves unmatched mass.

Library provenance: the splitting of the nonnegative integral uses Mathlib's
`lintegral_add_left` from
[`MeasureTheory/Integral/Lebesgue/Add.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.  The marginal integration lemmas
used below are local `ProbabilityCoupling` results.  No source text is copied
or ported.
-/
theorem independent_cost_edist_le_lintegral_edist_zero_add
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ ν : ProbabilityMeasure E) :
    (independent μ ν).cost (fun z => edist z.1 z.2) ≤
      (∫⁻ x, edist x 0 ∂(μ : Measure E)) +
        ∫⁻ y, edist 0 y ∂(ν : Measure E) := by
  calc
    (independent μ ν).cost (fun z => edist z.1 z.2) =
        ∫⁻ z, edist z.1 z.2 ∂((independent μ ν).joint : Measure (E × E)) := rfl
    _ ≤ ∫⁻ z, edist z.1 0 + edist 0 z.2 ∂
        ((independent μ ν).joint : Measure (E × E)) := by
      apply lintegral_mono
      intro z
      exact edist_triangle z.1 0 z.2
    _ = (∫⁻ z, edist z.1 0 ∂
        ((independent μ ν).joint : Measure (E × E))) +
      ∫⁻ z, edist 0 z.2 ∂((independent μ ν).joint : Measure (E × E)) := by
      rw [lintegral_add_left]
      exact measurable_fst.edist measurable_const
    _ = (∫⁻ x, edist x 0 ∂(μ : Measure E)) +
      ∫⁻ y, edist 0 y ∂(ν : Measure E) := by
      rw [← (independent μ ν).lintegral_fst
        (f := fun x : E => edist x 0) (measurable_id.edist measurable_const),
        ← (independent μ ν).lintegral_snd
          (f := fun y : E => edist 0 y) (measurable_const.edist measurable_id)]

/-- Integrating an a.e. strongly measurable function through the first marginal. -/
theorem integral_fst (π : ProbabilityCoupling μ ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E}
    (hf : AEStronglyMeasurable f (μ : Measure α)) :
    (∫ x, f x ∂(μ : Measure α)) = ∫ z, f z.1 ∂(π.joint : Measure (α × β)) := by
  have hmap : Measure.map Prod.fst (π.joint : Measure (α × β)) = (μ : Measure α) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_fst
  have hf_map : AEStronglyMeasurable f (Measure.map Prod.fst (π.joint : Measure (α × β))) := by
    simpa only [hmap] using hf
  calc
    (∫ x, f x ∂(μ : Measure α)) =
        ∫ x, f x ∂Measure.map Prod.fst (π.joint : Measure (α × β)) := by rw [hmap]
    _ = ∫ z, f z.1 ∂(π.joint : Measure (α × β)) :=
      integral_map measurable_fst.aemeasurable hf_map

/-- Integrating an a.e. strongly measurable function through the second marginal. -/
theorem integral_snd (π : ProbabilityCoupling μ ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : β → E}
    (hf : AEStronglyMeasurable f (ν : Measure β)) :
    (∫ y, f y ∂(ν : Measure β)) = ∫ z, f z.2 ∂(π.joint : Measure (α × β)) := by
  have hmap : Measure.map Prod.snd (π.joint : Measure (α × β)) = (ν : Measure β) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_snd
  have hf_map : AEStronglyMeasurable f (Measure.map Prod.snd (π.joint : Measure (α × β))) := by
    simpa only [hmap] using hf
  calc
    (∫ y, f y ∂(ν : Measure β)) =
        ∫ y, f y ∂Measure.map Prod.snd (π.joint : Measure (α × β)) := by rw [hmap]
    _ = ∫ z, f z.2 ∂(π.joint : Measure (α × β)) :=
      integral_map measurable_snd.aemeasurable hf_map

/-- Integrability of a first-marginal observable transfers to a coupling. -/
theorem integrable_fst (π : ProbabilityCoupling μ ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E}
    (hf : Integrable f (μ : Measure α)) :
    Integrable (fun z : α × β => f z.1) (π.joint : Measure (α × β)) := by
  have hmap : Measure.map Prod.fst (π.joint : Measure (α × β)) = (μ : Measure α) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_fst
  have hf_map : Integrable f (Measure.map Prod.fst (π.joint : Measure (α × β))) := by
    simpa only [hmap] using hf
  simpa only [Function.comp_apply] using hf_map.comp_measurable measurable_fst

/-- Integrability of a second-marginal observable transfers to a coupling. -/
theorem integrable_snd (π : ProbabilityCoupling μ ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : β → E}
    (hf : Integrable f (ν : Measure β)) :
    Integrable (fun z : α × β => f z.2) (π.joint : Measure (α × β)) := by
  have hmap : Measure.map Prod.snd (π.joint : Measure (α × β)) = (ν : Measure β) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_snd
  have hf_map : Integrable f (Measure.map Prod.snd (π.joint : Measure (α × β))) := by
    simpa only [hmap] using hf
  simpa only [Function.comp_apply] using hf_map.comp_measurable measurable_snd

/--
A pointwise real transport domination bounds the first-marginal expectation by
the second-marginal expectation plus a penalized expected coupling cost.
The result is deliberately at the level of one coupling witness: it neither
assumes that an optimal coupling exists nor identifies an infimum transport
cost with a minimum.
-/
theorem integral_fst_le_integral_snd_add_penalty_cost
    (π : ProbabilityCoupling μ ν) {f : α → ℝ} {g : β → ℝ}
    {c : α × β → ℝ} (penalty : ℝ)
    (hf : Integrable f (μ : Measure α))
    (hg : Integrable g (ν : Measure β))
    (hc : Integrable c (π.joint : Measure (α × β)))
    (hdom : ∀ z : α × β, f z.1 ≤ g z.2 + penalty * c z) :
    (∫ x, f x ∂(μ : Measure α)) ≤
      (∫ y, g y ∂(ν : Measure β)) + penalty * ∫ z, c z ∂(π.joint : Measure (α × β)) := by
  have hfst : Integrable (fun z : α × β => f z.1) (π.joint : Measure (α × β)) :=
    π.integrable_fst hf
  have hsnd : Integrable (fun z : α × β => g z.2) (π.joint : Measure (α × β)) :=
    π.integrable_snd hg
  have hpenalty_cost : Integrable (fun z : α × β => penalty * c z)
      (π.joint : Measure (α × β)) := hc.const_mul penalty
  calc
    (∫ x, f x ∂(μ : Measure α)) = ∫ z, f z.1 ∂(π.joint : Measure (α × β)) :=
      π.integral_fst hf.aestronglyMeasurable
    _ ≤ ∫ z, g z.2 + penalty * c z ∂(π.joint : Measure (α × β)) :=
      integral_mono hfst (hsnd.add hpenalty_cost) hdom
    _ = (∫ z, g z.2 ∂(π.joint : Measure (α × β)) +
          penalty * ∫ z, c z ∂(π.joint : Measure (α × β))) := by
      rw [integral_add hsnd hpenalty_cost, integral_const_mul]
    _ = (∫ y, g y ∂(ν : Measure β)) +
          penalty * ∫ z, c z ∂(π.joint : Measure (α × β)) := by
      rw [← π.integral_snd hg.aestronglyMeasurable]

/--
A real-cost transport-ball witness. This is intentionally an existential
coupling predicate, rather than an infimum constraint: it is the right
interface for a direct weak-duality certificate even when optimal couplings
need not exist.
-/
def HasRealExpectedCostAtMost (c : α × β → ℝ) (radius : ℝ)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : Prop :=
  ∃ π : ProbabilityCoupling μ ν,
    Integrable c (π.joint : Measure (α × β)) ∧
      (∫ z, c z ∂(π.joint : Measure (α × β)) ≤ radius)

/--
The preceding penalized expectation bound applied to any explicit
real-cost transport-ball witness.
-/
theorem integral_fst_le_integral_snd_add_penalty_of_realExpectedCostAtMost
    {f : α → ℝ} {g : β → ℝ} {c : α × β → ℝ} (penalty radius : ℝ)
    (hf : Integrable f (μ : Measure α))
    (hg : Integrable g (ν : Measure β))
    (hpenalty : 0 ≤ penalty)
    (htransport : HasRealExpectedCostAtMost c radius μ ν)
    (hdom : ∀ z : α × β, f z.1 ≤ g z.2 + penalty * c z) :
    (∫ x, f x ∂(μ : Measure α)) ≤
      (∫ y, g y ∂(ν : Measure β)) + penalty * radius := by
  obtain ⟨π, hcost_integrable, hcost_le⟩ := htransport
  calc
    (∫ x, f x ∂(μ : Measure α)) ≤
        (∫ y, g y ∂(ν : Measure β)) +
          penalty * ∫ z, c z ∂(π.joint : Measure (α × β)) :=
      π.integral_fst_le_integral_snd_add_penalty_cost penalty hf hg hcost_integrable hdom
    _ ≤ (∫ y, g y ∂(ν : Measure β)) + penalty * radius :=
      by linarith [mul_le_mul_of_nonneg_left hcost_le hpenalty]

/-- A coupling together with the finite real expected-cost certificate it carries. -/
abbrev FiniteRealCostCoupling (c : α × β → ℝ)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : Type _ :=
  { π : ProbabilityCoupling μ ν // Integrable c (π.joint : Measure (α × β)) }

/--
A finite-real-cost coupling with a fixed target marginal and an arbitrary
source marginal.  This is the natural primal domain for a penalized transport
problem: the source law is part of the candidate, while the nominal target law
is fixed.
-/
structure FiniteRealCostCouplingTo (c : α × β → ℝ) (ν : ProbabilityMeasure β) where
  source : ProbabilityMeasure α
  coupling : ProbabilityCoupling source ν
  cost_integrable : Integrable c (coupling.joint : Measure (α × β))

/--
Mix two finite-real-cost couplings to the same nominal law.  The mixed source
law is the corresponding convex combination.  Finiteness of the real cost is
preserved because integrability is closed under finite positive mixtures.
-/
noncomputable def FiniteRealCostCouplingTo.convexCombination
    (c : α × β → ℝ) (ν : ProbabilityMeasure β)
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first second : FiniteRealCostCouplingTo c ν) : FiniteRealCostCouplingTo c ν where
  source := ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one
    first.source second.source
  coupling := {
    joint := ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one
      first.coupling.joint second.coupling.joint
    map_fst := by
      apply Subtype.ext
      change Measure.map Prod.fst
          (ENNReal.ofReal weight • (first.coupling.joint : Measure (α × β)) +
            ENNReal.ofReal (1 - weight) • (second.coupling.joint : Measure (α × β))) =
        ENNReal.ofReal weight • (first.source : Measure α) +
          ENNReal.ofReal (1 - weight) • (second.source : Measure α)
      have hfirst : Measure.map Prod.fst (first.coupling.joint : Measure (α × β)) =
          (first.source : Measure α) := congrArg ProbabilityMeasure.toMeasure first.coupling.map_fst
      have hsecond : Measure.map Prod.fst (second.coupling.joint : Measure (α × β)) =
          (second.source : Measure α) := congrArg ProbabilityMeasure.toMeasure second.coupling.map_fst
      rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hfirst, hsecond]
    map_snd := by
      apply Subtype.ext
      change Measure.map Prod.snd
          (ENNReal.ofReal weight • (first.coupling.joint : Measure (α × β)) +
            ENNReal.ofReal (1 - weight) • (second.coupling.joint : Measure (α × β))) =
        (ν : Measure β)
      have hfirst : Measure.map Prod.snd (first.coupling.joint : Measure (α × β)) =
          (ν : Measure β) := congrArg ProbabilityMeasure.toMeasure first.coupling.map_snd
      have hsecond : Measure.map Prod.snd (second.coupling.joint : Measure (α × β)) =
          (ν : Measure β) := congrArg ProbabilityMeasure.toMeasure second.coupling.map_snd
      rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, hfirst, hsecond]
      exact congrArg ProbabilityMeasure.toMeasure
        (ProbabilityMeasure.convexCombination_self weight hweight_nonneg hweight_le_one ν) }
  cost_integrable := by
    change Integrable c (ENNReal.ofReal weight • (first.coupling.joint : Measure (α × β)) +
      ENNReal.ofReal (1 - weight) • (second.coupling.joint : Measure (α × β)))
    exact (first.cost_integrable.smul_measure (by simp)).add_measure
      (second.cost_integrable.smul_measure (by simp))

/-- The expected real cost of a finite coupling convex combination is affine. -/
theorem FiniteRealCostCouplingTo.integral_cost_convexCombination
    (c : α × β → ℝ) (ν : ProbabilityMeasure β)
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first second : FiniteRealCostCouplingTo c ν) :
    ∫ pair, c pair ∂
      ((FiniteRealCostCouplingTo.convexCombination c ν weight hweight_nonneg hweight_le_one
        first second).coupling.joint : Measure (α × β)) =
      weight * ∫ pair, c pair ∂(first.coupling.joint : Measure (α × β)) +
        (1 - weight) * ∫ pair, c pair ∂(second.coupling.joint : Measure (α × β)) := by
  simpa only [FiniteRealCostCouplingTo.convexCombination, smul_eq_mul] using
    (integral_probabilityMeasure_convexCombination weight hweight_nonneg hweight_le_one
      first.coupling.joint second.coupling.joint c first.cost_integrable second.cost_integrable)

/-- The expected source payoff of a finite coupling convex combination is affine. -/
theorem FiniteRealCostCouplingTo.integral_source_convexCombination
    (c : α × β → ℝ) (ν : ProbabilityMeasure β)
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first second : FiniteRealCostCouplingTo c ν) (loss : α → ℝ)
    (hfirst : Integrable loss (first.source : Measure α))
    (hsecond : Integrable loss (second.source : Measure α)) :
    ∫ x, loss x ∂
      ((FiniteRealCostCouplingTo.convexCombination c ν weight hweight_nonneg hweight_le_one
        first second).source : Measure α) =
      weight * ∫ x, loss x ∂(first.source : Measure α) +
        (1 - weight) * ∫ x, loss x ∂(second.source : Measure α) := by
  simpa only [FiniteRealCostCouplingTo.convexCombination, smul_eq_mul] using
    (integral_probabilityMeasure_convexCombination weight hweight_nonneg hweight_le_one
      first.source second.source loss hfirst hsecond)

/--
The unrestricted expected-loss value over all probability laws.  This is the
zero-transport-penalty domain: no finite transport moment is imposed when the
transport term is absent.
-/
noncomputable def unpenalizedValue (loss : α → ℝ) : ℝ :=
  sSup (Set.range fun source : ProbabilityMeasure α =>
    ∫ x, loss x ∂(source : Measure α))

/--
The unrestricted zero-transport-penalty value with the extended maximization
convention from `upperExpectation`.

Unlike `unpenalizedValue`, this value does not turn a nonintegrable reward
into the default Bochner integral `0`.  It is therefore the source-compatible
zero-multiplier endpoint when every probability law is admissible and the
absent transport term imposes no moment restriction.  The real-valued
`unpenalizedValue` remains useful for finite/integrable transport arguments.
-/
noncomputable def extendedUnpenalizedValue (loss : α → ℝ) : EReal :=
  sSup (Set.range fun source : ProbabilityMeasure α =>
    upperExpectation loss (source : Measure α))

/-- Every admissible source law supplies a lower bound on the unrestricted
extended zero-penalty value. -/
theorem upperExpectation_le_extendedUnpenalizedValue
    (loss : α → ℝ) (source : ProbabilityMeasure α) :
    upperExpectation loss (source : Measure α) ≤ extendedUnpenalizedValue loss := by
  unfold extendedUnpenalizedValue
  exact le_sSup (Set.mem_range_self source)

/--
Each measurable point payoff is attained by its Dirac adversarial law in the
unrestricted extended zero-penalty value.
-/
theorem coe_loss_le_extendedUnpenalizedValue_of_measurable
    (loss : α → ℝ) (hloss : Measurable loss) (point : α) :
    (loss point : EReal) ≤ extendedUnpenalizedValue loss := by
  rw [← upperExpectation_dirac loss hloss point]
  change upperExpectation loss (diracProba point : Measure α) ≤ _
  exact upperExpectation_le_extendedUnpenalizedValue loss (diracProba point)

/--
An unpenalized expected-loss supremum equals the pointwise loss supremum when
the loss is integrable under every probability law.  In particular, this
recovers the `gamma = 0` branch of a transport-penalized objective under the
standard convention that its absent transport term does not restrict the
adversarial law.

This uses Mathlib's
[`integral_dirac'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html#MeasureTheory.integral_dirac')
and the conditional-complete order API from
[`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
and
[`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean),
at the repository-pinned Apache-2.0 Mathlib revision.  The upstream APIs are
used unchanged; this local coupling-value argument copies no proof text.
-/
theorem unpenalizedValue_eq_sSup_range [Nonempty α] (loss : α → ℝ)
    (hloss_strongly_measurable : StronglyMeasurable loss)
    (hloss_integrable : ∀ source : ProbabilityMeasure α,
      Integrable loss (source : Measure α))
    (hloss_bddAbove : BddAbove (Set.range loss)) :
    unpenalizedValue loss = sSup (Set.range loss) := by
  have hintegral_range_nonempty : (Set.range fun source : ProbabilityMeasure α =>
      ∫ x, loss x ∂(source : Measure α)).Nonempty := by
    let point : α := Classical.choice inferInstance
    exact ⟨_, ⟨diracProba point, rfl⟩⟩
  have hintegral_le : ∀ source : ProbabilityMeasure α,
      (∫ x, loss x ∂(source : Measure α)) ≤ sSup (Set.range loss) := by
    intro source
    calc
      (∫ x, loss x ∂(source : Measure α)) ≤
          ∫ _ : α, sSup (Set.range loss) ∂(source : Measure α) := by
        apply integral_mono (hloss_integrable source) (integrable_const _)
        intro x
        exact le_csSup hloss_bddAbove (Set.mem_range_self x)
      _ = sSup (Set.range loss) := by simp
  have hintegral_bddAbove : BddAbove (Set.range fun source : ProbabilityMeasure α =>
      ∫ x, loss x ∂(source : Measure α)) := by
    refine ⟨sSup (Set.range loss), ?_⟩
    rintro value ⟨source, rfl⟩
    exact hintegral_le source
  apply le_antisymm
  · unfold unpenalizedValue
    refine csSup_le hintegral_range_nonempty ?_
    rintro value ⟨source, rfl⟩
    exact hintegral_le source
  · refine csSup_le (Set.range_nonempty loss) ?_
    rintro value ⟨x, rfl⟩
    rw [← integral_dirac' loss x hloss_strongly_measurable]
    unfold unpenalizedValue
    exact le_csSup hintegral_bddAbove (Set.mem_range_self (diracProba x))

/-- The primal penalized value over every finite-real-cost coupling whose
second marginal is the fixed nominal law. -/
noncomputable def penalizedCouplingValue
    (loss : α → ℝ) (c : α × β → ℝ) (penalty : ℝ) (ν : ProbabilityMeasure β) : ℝ :=
  sSup (Set.range fun candidate : FiniteRealCostCouplingTo c ν =>
    (∫ x, loss x ∂(candidate.source : Measure α)) -
      penalty * ∫ z, c z ∂(candidate.coupling.joint : Measure (α × β)))

/--
Every finite-cost coupling is upper-bounded by an integrable pointwise
envelope, so their penalized supremum is as well.  The source-loss
integrability is deliberately a premise for every varying source marginal.
-/
theorem penalizedCouplingValue_le_integral_envelope
    (loss : α → ℝ) (c : α × β → ℝ) (penalty : ℝ) (ν : ProbabilityMeasure β)
    (envelope : β → ℝ)
    (hfinite : Nonempty (FiniteRealCostCouplingTo c ν))
    (hloss_integrable : ∀ candidate : FiniteRealCostCouplingTo c ν,
      Integrable loss (candidate.source : Measure α))
    (henvelope_integrable : Integrable envelope (ν : Measure β))
    (hdom : ∀ pair : α × β,
      loss pair.1 - penalty * c pair ≤ envelope pair.2) :
    penalizedCouplingValue loss c penalty ν ≤ ∫ y, envelope y ∂(ν : Measure β) := by
  unfold penalizedCouplingValue
  apply csSup_le
  · obtain ⟨candidate⟩ := hfinite
    exact ⟨_, ⟨candidate, rfl⟩⟩
  · rintro value ⟨candidate, rfl⟩
    have hdom' : ∀ pair : α × β,
        loss pair.1 ≤ envelope pair.2 + penalty * c pair := by
      intro pair
      linarith [hdom pair]
    have hcertificate := candidate.coupling.integral_fst_le_integral_snd_add_penalty_cost
      penalty (hloss_integrable candidate) henvelope_integrable candidate.cost_integrable hdom'
    linarith

/--
If measurable near-maximizers give a finite-cost coupling within every
positive error of an integrable envelope, then the full penalized transport
supremum equals that envelope integral.  This is the selector half of a
general transport-duality proof; it does not prove the measurable-selection
premise or constrained-problem strong duality.
-/
theorem penalizedCouplingValue_eq_integral_envelope_of_exists_near
    (loss : α → ℝ) (c : α × β → ℝ) (penalty : ℝ) (ν : ProbabilityMeasure β)
    (envelope : β → ℝ)
    (hfinite : Nonempty (FiniteRealCostCouplingTo c ν))
    (hloss_integrable : ∀ candidate : FiniteRealCostCouplingTo c ν,
      Integrable loss (candidate.source : Measure α))
    (henvelope_integrable : Integrable envelope (ν : Measure β))
    (hdom : ∀ pair : α × β,
      loss pair.1 - penalty * c pair ≤ envelope pair.2)
    (hnear : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ candidate : FiniteRealCostCouplingTo c ν,
        (∫ y, envelope y ∂(ν : Measure β)) ≤
          ((∫ x, loss x ∂(candidate.source : Measure α)) -
            penalty * ∫ z, c z ∂(candidate.coupling.joint : Measure (α × β))) + epsilon) :
    penalizedCouplingValue loss c penalty ν = ∫ y, envelope y ∂(ν : Measure β) := by
  apply le_antisymm
  · exact penalizedCouplingValue_le_integral_envelope loss c penalty ν envelope hfinite
      hloss_integrable henvelope_integrable hdom
  · apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    obtain ⟨candidate, hcandidate⟩ := hnear epsilon hepsilon
    have hupper : ∀ candidate : FiniteRealCostCouplingTo c ν,
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ z, c z ∂(candidate.coupling.joint : Measure (α × β)) ≤
          ∫ y, envelope y ∂(ν : Measure β) := by
      intro candidate
      have hdom' : ∀ pair : α × β,
          loss pair.1 ≤ envelope pair.2 + penalty * c pair := by
        intro pair
        linarith [hdom pair]
      have hcertificate := candidate.coupling.integral_fst_le_integral_snd_add_penalty_cost
        penalty (hloss_integrable candidate) henvelope_integrable candidate.cost_integrable hdom'
      linarith
    have hbounded : BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c ν =>
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ z, c z ∂(candidate.coupling.joint : Measure (α × β))) := by
      refine ⟨∫ y, envelope y ∂(ν : Measure β), ?_⟩
      rintro value ⟨candidate, rfl⟩
      exact hupper candidate
    calc
      (∫ y, envelope y ∂(ν : Measure β)) ≤
          ((∫ x, loss x ∂(candidate.source : Measure α)) -
            penalty * ∫ z, c z ∂(candidate.coupling.joint : Measure (α × β))) + epsilon :=
        hcandidate
      _ ≤ penalizedCouplingValue loss c penalty ν + epsilon := by
        apply add_le_add
        · exact le_csSup hbounded (Set.mem_range_self candidate)
        · exact le_refl epsilon

/--
The infimum of finite real expected costs.  Its nonempty-domain condition is
kept in theorems, rather than encoded in the definition, so that applications
state exactly which finite-cost witness their model supplies.
-/
noncomputable def realTransportCost (c : α × β → ℝ)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : ℝ :=
  sInf (Set.range fun π : FiniteRealCostCoupling c μ ν =>
    ∫ z, c z ∂(π.1.joint : Measure (α × β)))

/--
Every finite-cost coupling upper-bounds the infimum real transport cost when
the pointwise cost is nonnegative.  The nonnegativity condition supplies the
lower bound required by the real `sInf` API; no optimal coupling is assumed.
-/
theorem realTransportCost_le_expectedCost
    (c : α × β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (coupling : FiniteRealCostCoupling c μ ν) :
    realTransportCost c μ ν ≤
      ∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)) := by
  unfold realTransportCost
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro value ⟨candidate, rfl⟩
    exact integral_nonneg hcost_nonneg
  · exact Set.mem_range_self coupling

/-- A nonnegative real cost has nonnegative infimum transport cost on a nonempty finite-cost domain. -/
theorem realTransportCost_nonneg
    (c : α × β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
    (hfinite : Nonempty (FiniteRealCostCoupling c μ ν))
    (hcost_nonneg : ∀ pair, 0 ≤ c pair) :
    0 ≤ realTransportCost c μ ν := by
  unfold realTransportCost
  apply le_csInf
  · obtain ⟨coupling⟩ := hfinite
    exact ⟨_, ⟨coupling, rfl⟩⟩
  · rintro value ⟨coupling, rfl⟩
    exact integral_nonneg hcost_nonneg

/--
An infimum strictly below a threshold admits a finite-cost coupling strictly
below that threshold.  This is the epsilon-optimal transport bridge; no
optimal coupling is assumed.
-/
theorem exists_realExpectedCost_lt_of_realTransportCost_lt
    (c : α × β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
    (hfinite : Nonempty (FiniteRealCostCoupling c μ ν)) {bound : ℝ}
    (hcost : realTransportCost c μ ν < bound) :
    ∃ π : FiniteRealCostCoupling c μ ν,
      ∫ z, c z ∂(π.1.joint : Measure (α × β)) < bound := by
  unfold realTransportCost at hcost
  obtain ⟨costValue, ⟨π, rfl⟩, hπcost⟩ :=
    exists_lt_of_csInf_lt (Set.range_nonempty _) hcost
  exact ⟨π, hπcost⟩

/--
The infimum transport cost is convex under mixing of source laws.  The proof
uses epsilon-optimal finite-cost couplings on both sides before mixing them;
it does not assume that either infimum is attained.
-/
theorem realTransportCost_convexCombination_le
    (c : α × β → ℝ) (ν : ProbabilityMeasure β)
    (weight : ℝ) (hweight_nonneg : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (first second : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source ν) })
    (hcost_nonneg : ∀ pair, 0 ≤ c pair) :
    realTransportCost c
        (ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one first.1 second.1)
        ν ≤
      weight * realTransportCost c first.1 ν +
        (1 - weight) * realTransportCost c second.1 ν := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨firstPlan, hfirstPlan⟩ :=
    exists_realExpectedCost_lt_of_realTransportCost_lt c first.1 ν first.2
      (bound := realTransportCost c first.1 ν + epsilon) (by linarith)
  obtain ⟨secondPlan, hsecondPlan⟩ :=
    exists_realExpectedCost_lt_of_realTransportCost_lt c second.1 ν second.2
      (bound := realTransportCost c second.1 ν + epsilon) (by linarith)
  let firstCandidate : FiniteRealCostCouplingTo c ν := {
    source := first.1
    coupling := firstPlan.1
    cost_integrable := firstPlan.2 }
  let secondCandidate : FiniteRealCostCouplingTo c ν := {
    source := second.1
    coupling := secondPlan.1
    cost_integrable := secondPlan.2 }
  let mixed := FiniteRealCostCouplingTo.convexCombination c ν weight hweight_nonneg hweight_le_one
    firstCandidate secondCandidate
  have hmixed_cost := realTransportCost_le_expectedCost c mixed.source ν hcost_nonneg
    ⟨mixed.coupling, mixed.cost_integrable⟩
  change realTransportCost c
      (ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one first.1 second.1)
      ν ≤
    ∫ pair, c pair ∂(mixed.coupling.joint : Measure (α × β)) at hmixed_cost
  rw [FiniteRealCostCouplingTo.integral_cost_convexCombination] at hmixed_cost
  have hweight_compl_nonneg : 0 ≤ 1 - weight := sub_nonneg.mpr hweight_le_one
  have hfirst_weighted : weight * ∫ pair, c pair ∂(firstPlan.1.joint : Measure (α × β)) ≤
      weight * (realTransportCost c first.1 ν + epsilon) :=
    mul_le_mul_of_nonneg_left hfirstPlan.le hweight_nonneg
  have hsecond_weighted : (1 - weight) * ∫ pair, c pair ∂
      (secondPlan.1.joint : Measure (α × β)) ≤
      (1 - weight) * (realTransportCost c second.1 ν + epsilon) :=
    mul_le_mul_of_nonneg_left hsecondPlan.le hweight_compl_nonneg
  calc
    realTransportCost c
        (ProbabilityMeasure.convexCombination weight hweight_nonneg hweight_le_one first.1 second.1)
        ν ≤ weight * ∫ pair, c pair ∂(firstPlan.1.joint : Measure (α × β)) +
          (1 - weight) * ∫ pair, c pair ∂(secondPlan.1.joint : Measure (α × β)) := by
            simpa [mixed, firstCandidate, secondCandidate] using hmixed_cost
    _ ≤ weight * (realTransportCost c first.1 ν + epsilon) +
          (1 - weight) * (realTransportCost c second.1 ν + epsilon) :=
      add_le_add hfirst_weighted hsecond_weighted
    _ = weight * realTransportCost c first.1 ν +
          (1 - weight) * realTransportCost c second.1 ν + epsilon := by
      ring

/--
Weak real-cost transport duality at the infimum-ball level.  Starting from the
usual cost-infimum constraint, the proof uses an epsilon-optimal coupling and
then lets epsilon vanish.  Thus it does not assume transport-plan attainment,
strong transport duality, or a measurable maximizer.

Library provenance: the epsilon-optimal selection uses Mathlib's
`exists_lt_of_csInf_lt` from
[`Order/ConditionallyCompleteLattice/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean)
and the limiting step uses `le_of_forall_pos_le_add` from
[`Algebra/Order/Field/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Field/Basic.lean).
Both are imported unchanged at the pinned Apache-2.0 Mathlib revision; the
real-cost transport interface and its proof are local, and no upstream source
text is copied or ported.
-/
theorem integral_fst_le_integral_snd_add_penalty_of_realTransportCost_le
    {f : α → ℝ} {g : β → ℝ} {c : α × β → ℝ} (penalty radius : ℝ)
    (hf : Integrable f (μ : Measure α))
    (hg : Integrable g (ν : Measure β))
    (hpenalty : 0 ≤ penalty)
    (hfinite : Nonempty (FiniteRealCostCoupling c μ ν))
    (hcost : realTransportCost c μ ν ≤ radius)
    (hdom : ∀ z : α × β, f z.1 ≤ g z.2 + penalty * c z) :
    (∫ x, f x ∂(μ : Measure α)) ≤
      (∫ y, g y ∂(ν : Measure β)) + penalty * radius := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let delta : ℝ := epsilon / (penalty + 1)
  have hdenom_pos : 0 < penalty + 1 := by linarith
  have hdelta_pos : 0 < delta := div_pos hepsilon hdenom_pos
  have hinf_lt : realTransportCost c μ ν < radius + delta := by linarith
  obtain ⟨π, hπ_cost_lt⟩ :=
    exists_realExpectedCost_lt_of_realTransportCost_lt c μ ν hfinite hinf_lt
  have hcertificate := π.1.integral_fst_le_integral_snd_add_penalty_cost penalty hf hg
    π.2 hdom
  have hscaled_cost : penalty * (∫ z, c z ∂(π.1.joint : Measure (α × β))) ≤
      penalty * (radius + delta) := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hπ_cost_lt) hpenalty
  have hpenalty_delta_le : penalty * delta ≤ epsilon := by
    dsimp [delta]
    have hdenom_ne : penalty + 1 ≠ 0 := ne_of_gt hdenom_pos
    calc
      penalty * (epsilon / (penalty + 1)) =
          epsilon * (penalty / (penalty + 1)) := by field_simp
      _ ≤ epsilon * 1 := by
        gcongr
        exact (div_le_one₀ hdenom_pos).mpr (by linarith)
      _ = epsilon := by ring
  calc
    (∫ x, f x ∂(μ : Measure α)) ≤
        (∫ y, g y ∂(ν : Measure β)) +
          penalty * ∫ z, c z ∂(π.1.joint : Measure (α × β)) := hcertificate
    _ ≤ (∫ y, g y ∂(ν : Measure β)) + penalty * (radius + delta) := by
      linarith
    _ = ((∫ y, g y ∂(ν : Measure β)) + penalty * radius) + penalty * delta := by
      ring
    _ ≤ ((∫ y, g y ∂(ν : Measure β)) + penalty * radius) + epsilon := by
      linarith

/--
The expected-loss supremum over a real-cost transport ball.  A candidate law
carries both a nonempty finite-real-cost coupling domain and its infimum-cost
ball membership, so the real-valued `sInf` transport cost is not interpreted
through an empty-domain convention.
-/
noncomputable def constrainedRealTransportValue
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β) : ℝ :=
  sSup (Set.range fun candidate : { source : ProbabilityMeasure α //
    Nonempty (FiniteRealCostCoupling c source nominal) ∧
      realTransportCost c source nominal ≤ radius } =>
    ∫ x, loss x ∂(candidate.1 : Measure α))

/--
The coupling-level form of a real-cost transport ball.  In contrast with
`constrainedRealTransportValue`, the cost here is the cost of a concrete
coupling rather than the infimum over couplings for its first marginal.  This
is the natural convex primal domain: mixing feasible couplings mixes both
their expected costs and their expected payoffs linearly.

The two values agree when every source law in the infimum-cost ball has an
attaining feasible coupling; that separate bridge is deliberately stated as a
theorem below rather than silently built into the definition.
-/
noncomputable def constrainedRealCouplingValue
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β) : ℝ :=
  sSup (Set.range fun candidate : { coupling : FiniteRealCostCouplingTo c nominal //
    ∫ pair, c pair ∂(coupling.coupling.joint : Measure (α × β)) ≤ radius } =>
    ∫ x, loss x ∂(candidate.1.source : Measure α))

/--
The concrete cost--payoff image of finite-cost couplings to a fixed nominal
law.  Unlike `realTransportCostPayoffFrontier`, no infimum is taken before the
pair is formed, so this is the appropriate frontier for a direct convexity
argument on transport plans.
-/
noncomputable def realCouplingCostPayoffFrontier
    (loss : α → ℝ) (c : α × β → ℝ)
    (nominal : ProbabilityMeasure β) : Set (ℝ × ℝ) :=
  Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
    (∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)),
      ∫ x, loss x ∂(candidate.source : Measure α))

/--
The feasible coupling cost--payoff frontier is convex whenever the payoff is
integrable under every finite-cost coupling.  Convexity is not a separate
economic assumption: a convex combination of plans preserves the fixed target
marginal, finite cost, and both expected coordinates.
-/
theorem convex_realCouplingCostPayoffFrontier_of_integrable
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β)
    (hloss_integrable : ∀ candidate : FiniteRealCostCouplingTo c nominal,
      Integrable loss (candidate.source : Measure α)) :
    Convex ℝ (realCouplingCostPayoffFrontier loss c nominal) := by
  intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
  obtain ⟨firstCoupling, rfl⟩ := hfirst
  obtain ⟨secondCoupling, rfl⟩ := hsecond
  have hweightFirst_le_one : weightFirst ≤ 1 := by linarith
  have hweightSecond_eq : weightSecond = 1 - weightFirst := by linarith
  subst weightSecond
  let mixed := FiniteRealCostCouplingTo.convexCombination c nominal weightFirst
    hweightFirst hweightFirst_le_one firstCoupling secondCoupling
  refine ⟨mixed, ?_⟩
  change
    (∫ pair, c pair ∂(mixed.coupling.joint : Measure (α × β)),
      ∫ x, loss x ∂(mixed.source : Measure α)) =
      (weightFirst * ∫ pair, c pair ∂(firstCoupling.coupling.joint : Measure (α × β)) +
        (1 - weightFirst) * ∫ pair, c pair ∂
          (secondCoupling.coupling.joint : Measure (α × β)),
      weightFirst * ∫ x, loss x ∂(firstCoupling.source : Measure α) +
        (1 - weightFirst) * ∫ x, loss x ∂(secondCoupling.source : Measure α))
  rw [FiniteRealCostCouplingTo.integral_cost_convexCombination,
    FiniteRealCostCouplingTo.integral_source_convexCombination c nominal weightFirst
      hweightFirst hweightFirst_le_one firstCoupling secondCoupling loss
      (hloss_integrable firstCoupling) (hloss_integrable secondCoupling)]

/-- The probability laws on a product space whose second marginal is fixed. -/
def fixedTargetJointLaws (ν : ProbabilityMeasure β) : Set (ProbabilityMeasure (α × β)) :=
  { joint | joint.map measurable_snd.aemeasurable = ν }

/--
For compact metric state spaces, joint laws with a fixed second marginal form
a compact set in the weak topology.

Library provenance: this applies the pinned Apache-2.0 Mathlib
[`ProbabilityMeasure` weak-topology API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean)
and its
[`Prokhorov` compactness theorem](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Prokhorov.lean).
The fixed-marginal construction and proof are local; no external proof text is
copied.
-/
theorem isCompact_fixedTargetJointLaws
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β] (ν : ProbabilityMeasure β) :
    IsCompact (fixedTargetJointLaws (α := α) ν) := by
  change IsCompact ((fun joint : ProbabilityMeasure (α × β) =>
    joint.map measurable_snd.aemeasurable) ⁻¹' {ν})
  have hmap : Continuous (fun joint : ProbabilityMeasure (α × β) =>
      joint.map measurable_snd.aemeasurable) := by
    simpa only using
      (ProbabilityMeasure.continuous_map (Ω := α × β) (Ω' := β) continuous_snd)
  exact (isClosed_singleton.preimage hmap).isCompact

/-- The expected cost and source payoff represented by a joint law. -/
noncomputable def fixedTargetJointCostPayoff (loss : α → ℝ) (c : α × β → ℝ)
    (joint : ProbabilityMeasure (α × β)) : ℝ × ℝ :=
  (∫ pair, c pair ∂(joint : Measure (α × β)),
    ∫ x, loss x ∂(joint.map measurable_fst.aemeasurable : Measure α))

/-- For compact metric state spaces, expected continuous cost and payoff vary
continuously with a joint probability law in the weak topology. -/
theorem continuous_fixedTargetJointCostPayoff
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β]
    (loss : α → ℝ) (c : α × β → ℝ)
    (hloss : Continuous loss) (hcost : Continuous c) :
    Continuous (fixedTargetJointCostPayoff loss c) := by
  let costBCF : BoundedContinuousFunction (α × β) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨c, hcost⟩
  let lossBCF : BoundedContinuousFunction α ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨loss, hloss⟩
  have hcost_cont : Continuous (fun joint : ProbabilityMeasure (α × β) =>
      ∫ pair, c pair ∂(joint : Measure (α × β))) := by
    simpa [costBCF] using
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction costBCF)
  have hloss_cont : Continuous (fun source : ProbabilityMeasure α =>
      ∫ x, loss x ∂(source : Measure α)) := by
    simpa [lossBCF] using
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction lossBCF)
  have hfst_map : Continuous (fun joint : ProbabilityMeasure (α × β) =>
      joint.map measurable_fst.aemeasurable) := by
    simpa only using
      (ProbabilityMeasure.continuous_map (Ω := α × β) (Ω' := α) continuous_fst)
  exact hcost_cont.prodMk (hloss_cont.comp hfst_map)

/--
For continuous real cost and loss on compact metric state spaces, the concrete
fixed-target coupling cost--payoff frontier is compact.  Continuous functions
are automatically bounded on the compact product, so every joint probability
law has finite real cost.
-/
theorem isCompact_realCouplingCostPayoffFrontier_of_compactSpace
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β]
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β)
    (hloss : Continuous loss) (hcost : Continuous c) :
    IsCompact (realCouplingCostPayoffFrontier loss c nominal) := by
  have hcost_integrable : ∀ joint : ProbabilityMeasure (α × β),
      Integrable c (joint : Measure (α × β)) := by
    intro joint
    let costBCF : BoundedContinuousFunction (α × β) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨c, hcost⟩
    simpa [costBCF] using costBCF.integrable (joint : Measure (α × β))
  have hfrontier : realCouplingCostPayoffFrontier loss c nominal =
      fixedTargetJointCostPayoff loss c '' fixedTargetJointLaws (α := α) nominal := by
    ext point
    constructor
    · rintro ⟨candidate, rfl⟩
      refine ⟨candidate.coupling.joint, ?_, ?_⟩
      · exact candidate.coupling.map_snd
      · change (∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)),
            ∫ x, loss x ∂(candidate.coupling.joint.map measurable_fst.aemeasurable : Measure α)) =
          (∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)),
            ∫ x, loss x ∂(candidate.source : Measure α))
        rw [candidate.coupling.map_fst]
    · rintro ⟨joint, htarget, rfl⟩
      let source : ProbabilityMeasure α :=
        joint.map measurable_fst.aemeasurable
      let candidate : FiniteRealCostCouplingTo c nominal := {
        source := source
        coupling := {
          joint := joint
          map_fst := rfl
          map_snd := htarget }
        cost_integrable := hcost_integrable joint }
      exact ⟨candidate, rfl⟩
  rw [hfrontier]
  exact (isCompact_fixedTargetJointLaws (α := α) nominal).image
    (continuous_fixedTargetJointCostPayoff loss c hloss hcost)

/-- The probability laws on a product space whose two marginals are fixed. -/
def fixedMarginalJointLaws (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    Set (ProbabilityMeasure (α × β)) :=
  fixedTargetJointLaws (α := α) ν ∩
    { joint | joint.map measurable_fst.aemeasurable = μ }

/-- For compact metric state spaces, the set of couplings of two fixed laws is
compact in the weak topology. -/
theorem isCompact_fixedMarginalJointLaws
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β]
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    IsCompact (fixedMarginalJointLaws μ ν) := by
  have hfst_map : Continuous (fun joint : ProbabilityMeasure (α × β) =>
      joint.map measurable_fst.aemeasurable) := by
    simpa only using
      (ProbabilityMeasure.continuous_map (Ω := α × β) (Ω' := α) continuous_fst)
  exact (isCompact_fixedTargetJointLaws (α := α) ν).inter_right
    (isClosed_singleton.preimage hfst_map)

/-- The expected real cost represented by a joint probability law. -/
noncomputable def jointExpectedRealCost (c : α × β → ℝ)
    (joint : ProbabilityMeasure (α × β)) : ℝ :=
  ∫ pair, c pair ∂(joint : Measure (α × β))

/-- Expected continuous real cost varies continuously with a joint law on
compact metric state spaces. -/
theorem continuous_jointExpectedRealCost
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β]
    (c : α × β → ℝ) (hcost : Continuous c) :
    Continuous (jointExpectedRealCost c) := by
  let costBCF : BoundedContinuousFunction (α × β) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨c, hcost⟩
  simpa [jointExpectedRealCost, costBCF] using
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction costBCF)

/--
Under compact metric state spaces and continuous real cost, a finite-cost
coupling minimizes expected cost among all couplings of two fixed laws.

Library provenance: compactness and weak-continuity use the pinned Apache-2.0
Mathlib probability-measure APIs cited at
`isCompact_fixedTargetJointLaws`; existence of a minimizer is Mathlib's
[`IsCompact.exists_isMinOn`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/Compact.lean).
This transport-plan attainment argument is local and no external proof text is
copied.
-/
theorem finiteRealCostCoupling_exists_isMinOn_of_compactSpace
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β]
    (c : α × β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
    (hcost : Continuous c) :
    ∃ coupling : FiniteRealCostCoupling c μ ν,
      ∀ other : FiniteRealCostCoupling c μ ν,
        ∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)) ≤
          ∫ pair, c pair ∂(other.1.joint : Measure (α × β)) := by
  have hcost_integrable : ∀ joint : ProbabilityMeasure (α × β),
      Integrable c (joint : Measure (α × β)) := by
    intro joint
    let costBCF : BoundedContinuousFunction (α × β) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨c, hcost⟩
    simpa [costBCF] using costBCF.integrable (joint : Measure (α × β))
  have hjoints_nonempty : (fixedMarginalJointLaws μ ν).Nonempty := by
    let product := independent μ ν
    refine ⟨product.joint, ?_⟩
    exact ⟨product.map_snd, product.map_fst⟩
  obtain ⟨joint, hjoint, hminimal⟩ :=
    (isCompact_fixedMarginalJointLaws μ ν).exists_isMinOn hjoints_nonempty
      (continuous_jointExpectedRealCost c hcost).continuousOn
  let coupling : FiniteRealCostCoupling c μ ν := ⟨{
    joint := joint
    map_fst := hjoint.2
    map_snd := hjoint.1 }, hcost_integrable joint⟩
  refine ⟨coupling, ?_⟩
  intro other
  change jointExpectedRealCost c joint ≤ jointExpectedRealCost c other.1.joint
  exact hminimal ⟨other.1.map_snd, other.1.map_fst⟩

/-- Under compact metric state spaces and continuous cost, the real transport
cost infimum is attained by a finite-cost coupling. -/
theorem exists_realTransportCost_eq_expectedCost_of_compactSpace
    [MetricSpace α] [MetricSpace β] [BorelSpace α] [BorelSpace β]
    [CompactSpace α] [CompactSpace β]
    (c : α × β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
    (hcost : Continuous c) :
    ∃ coupling : FiniteRealCostCoupling c μ ν,
      ∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)) = realTransportCost c μ ν := by
  obtain ⟨coupling, hminimal⟩ :=
    finiteRealCostCoupling_exists_isMinOn_of_compactSpace c μ ν hcost
  refine ⟨coupling, le_antisymm ?_ ?_⟩
  · unfold realTransportCost
    apply le_csInf
    · exact ⟨_, ⟨coupling, rfl⟩⟩
    · rintro cost ⟨other, rfl⟩
      exact hminimal other
  · unfold realTransportCost
    apply csInf_le
    · refine ⟨∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)), ?_⟩
      rintro cost ⟨other, rfl⟩
      exact hminimal other
    · exact Set.mem_range_self coupling

/--
The exact cost--payoff frontier underlying a real-cost transport problem.  A
point records the infimum transport cost of a source law to the fixed nominal
law and that source law's expected payoff.  Unlike a duality certificate,
this is a concrete image of the admissible finite-cost laws; compactness and
convexity of this set are separate mathematical obligations in non-finite
transport models.
-/
noncomputable def realTransportCostPayoffFrontier
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β) : Set (ℝ × ℝ) :=
  Set.range fun candidate : { source : ProbabilityMeasure α //
    Nonempty (FiniteRealCostCoupling c source nominal) } =>
    (realTransportCost c candidate.1 nominal,
      ∫ x, loss x ∂(candidate.1 : Measure α))

/--
The attainable upper/lower cost--payoff hypograph of an infimum-cost
transport frontier is convex.  Exact transport-cost pairs need not themselves
be convex because mixing can improve the infimum cost; the upper cost and
lower payoff coordinates in `Optimization.scalarAchievableSet` capture the
correct convex geometry.  The proof uses
`realTransportCost_convexCombination_le`, hence requires no optimal plan.
-/
theorem convex_scalarAchievableSet_realTransportCostPayoffFrontier
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hloss_integrable : ∀ candidate : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) },
      Integrable loss (candidate.1 : Measure α))
    (hcost_nonneg : ∀ pair, 0 ≤ c pair) :
    Convex ℝ (Optimization.scalarAchievableSet
      (realTransportCostPayoffFrontier loss c nominal) Prod.snd
      (fun point => point.1 - radius)) := by
  rintro ⟨firstCost, firstPayoff⟩
    ⟨firstPoint, hfirstPoint, hfirstCost, hfirstPayoff⟩
    ⟨secondCost, secondPayoff⟩
    ⟨secondPoint, hsecondPoint, hsecondCost, hsecondPayoff⟩
    weightFirst weightSecond hweightFirst hweightSecond hweights
  obtain ⟨first, hfirst_eq⟩ := hfirstPoint
  obtain ⟨second, hsecond_eq⟩ := hsecondPoint
  have hfirst_cost_eq : realTransportCost c first.1 nominal = firstPoint.1 := by
    simpa using congrArg Prod.fst hfirst_eq
  have hfirst_payoff_eq : (∫ x, loss x ∂(first.1 : Measure α)) = firstPoint.2 := by
    simpa using congrArg Prod.snd hfirst_eq
  have hsecond_cost_eq : realTransportCost c second.1 nominal = secondPoint.1 := by
    simpa using congrArg Prod.fst hsecond_eq
  have hsecond_payoff_eq : (∫ x, loss x ∂(second.1 : Measure α)) = secondPoint.2 := by
    simpa using congrArg Prod.snd hsecond_eq
  let firstPlan : FiniteRealCostCoupling c first.1 nominal := Classical.choice first.2
  let secondPlan : FiniteRealCostCoupling c second.1 nominal := Classical.choice second.2
  let firstCandidate : FiniteRealCostCouplingTo c nominal := {
    source := first.1
    coupling := firstPlan.1
    cost_integrable := firstPlan.2 }
  let secondCandidate : FiniteRealCostCouplingTo c nominal := {
    source := second.1
    coupling := secondPlan.1
    cost_integrable := secondPlan.2 }
  let mixedCandidate := FiniteRealCostCouplingTo.convexCombination c nominal
    weightFirst hweightFirst (by linarith) firstCandidate secondCandidate
  let mixedSource : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) } :=
    ⟨ProbabilityMeasure.convexCombination weightFirst hweightFirst (by linarith) first.1 second.1,
      ⟨⟨mixedCandidate.coupling, mixedCandidate.cost_integrable⟩⟩⟩
  have hmixed_cost : realTransportCost c mixedSource.1 nominal ≤
      weightFirst * realTransportCost c first.1 nominal +
        (1 - weightFirst) * realTransportCost c second.1 nominal := by
    simpa [mixedSource] using realTransportCost_convexCombination_le c nominal
      weightFirst hweightFirst (by linarith) first second hcost_nonneg
  have hmixed_payoff : (∫ x, loss x ∂(mixedSource.1 : Measure α)) =
      weightFirst * (∫ x, loss x ∂(first.1 : Measure α)) +
        (1 - weightFirst) * (∫ x, loss x ∂(second.1 : Measure α)) := by
    simpa [mixedSource, smul_eq_mul] using
      integral_probabilityMeasure_convexCombination weightFirst hweightFirst (by linarith)
        first.1 second.1 loss (hloss_integrable first) (hloss_integrable second)
  refine ⟨(realTransportCost c mixedSource.1 nominal,
      ∫ x, loss x ∂(mixedSource.1 : Measure α)), ?_, ?_, ?_⟩
  · exact ⟨mixedSource, rfl⟩
  · have hfirst_weighted : weightFirst * (firstPoint.1 - radius) ≤
        weightFirst * firstCost :=
      mul_le_mul_of_nonneg_left hfirstCost hweightFirst
    have hsecond_weighted : weightSecond * (secondPoint.1 - radius) ≤
        weightSecond * secondCost :=
      mul_le_mul_of_nonneg_left hsecondCost hweightSecond
    rw [← hfirst_cost_eq] at hfirst_weighted
    rw [← hsecond_cost_eq] at hsecond_weighted
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    calc
      realTransportCost c mixedSource.1 nominal - radius ≤
          weightFirst * realTransportCost c first.1 nominal +
            (1 - weightFirst) * realTransportCost c second.1 nominal - radius :=
        sub_le_sub_right hmixed_cost radius
      _ = weightFirst * (realTransportCost c first.1 nominal - radius) +
            weightSecond * (realTransportCost c second.1 nominal - radius) := by
        rw [show weightSecond = 1 - weightFirst by linarith]
        ring
      _ ≤ weightFirst * firstCost + weightSecond * secondCost := by
        exact add_le_add hfirst_weighted hsecond_weighted
  · have hfirst_weighted : weightFirst * firstPayoff ≤ weightFirst * firstPoint.2 :=
      mul_le_mul_of_nonneg_left hfirstPayoff hweightFirst
    have hsecond_weighted : (1 - weightFirst) * secondPayoff ≤
        (1 - weightFirst) * secondPoint.2 := by
      rw [← show weightSecond = 1 - weightFirst by linarith]
      exact mul_le_mul_of_nonneg_left hsecondPayoff hweightSecond
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [show weightSecond = 1 - weightFirst by linarith]
    rw [hmixed_payoff, hfirst_payoff_eq, hsecond_payoff_eq]
    exact add_le_add hfirst_weighted hsecond_weighted

/--
The Lagrangian value formed from an infimum real transport cost, with the
candidate source law restricted precisely to those admitting a finite-cost
coupling to the nominal law.  This is the fixed-penalty counterpart of
`realTransportCostPayoffFrontier` before any pointwise-envelope selection
argument is applied.
-/
noncomputable def realTransportCostPenalizedValue
    (loss : α → ℝ) (c : α × β → ℝ) (penalty : ℝ)
    (nominal : ProbabilityMeasure β) : ℝ :=
  sSup (Set.range fun candidate : { source : ProbabilityMeasure α //
    Nonempty (FiniteRealCostCoupling c source nominal) } =>
    (∫ x, loss x ∂(candidate.1 : Measure α)) -
      penalty * realTransportCost c candidate.1 nominal)

/--
The coupling-ball value is exactly the scalar constrained primal value of its
concrete coupling cost--payoff frontier.  This is a reindexing identity, so it
requires neither an optimal transport plan nor any topological transport
theory.
-/
theorem constrainedRealCouplingValue_eq_scalarPrimalValue_frontier
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β) :
    constrainedRealCouplingValue loss c radius nominal =
      Optimization.scalarPrimalValue (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  unfold constrainedRealCouplingValue Optimization.scalarPrimalValue
    Optimization.scalarFeasible realCouplingCostPayoffFrontier
  congr 1
  ext payoff
  constructor
  · rintro ⟨candidate, rfl⟩
    refine ⟨(∫ pair, c pair ∂(candidate.1.coupling.joint : Measure (α × β)),
      ∫ x, loss x ∂(candidate.1.source : Measure α)), ?_, rfl⟩
    refine ⟨⟨candidate.1, rfl⟩, ?_⟩
    exact sub_nonpos.mpr candidate.2
  · rintro ⟨point, hpoint, hpayoff⟩
    obtain ⟨hfrontier, hfeasible⟩ := hpoint
    obtain ⟨candidate, hpoint_eq⟩ := hfrontier
    subst point
    refine ⟨⟨candidate, sub_nonpos.mp hfeasible⟩, ?_⟩
    simpa using hpayoff

/--
The scalar dual objective of a coupling frontier is the direct penalized
coupling value plus the radius term.  This is the fixed-penalty identity used
by coupling-level constrained transport duality.
-/
theorem scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
    (loss : α → ℝ) (c : α × β → ℝ) (penalty radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hfinite : Nonempty (FiniteRealCostCouplingTo c nominal))
    (hbounded : BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
      (∫ x, loss x ∂(candidate.source : Measure α)) -
        penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)))) :
    Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
      penalizedCouplingValue loss c penalty nominal + penalty * radius := by
  let base : Set ℝ := Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
    (∫ x, loss x ∂(candidate.source : Measure α)) -
      penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β))
  have hbase_ne : base.Nonempty := by
    obtain ⟨candidate⟩ := hfinite
    exact ⟨_, ⟨candidate, rfl⟩⟩
  have hset :
      (fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
        realCouplingCostPayoffFrontier loss c nominal = base + {penalty * radius} := by
    ext value
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      change point ∈ Set.range (fun candidate : FiniteRealCostCouplingTo c nominal =>
        (∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)),
          ∫ x, loss x ∂(candidate.source : Measure α))) at hpoint
      obtain ⟨candidate, rfl⟩ := hpoint
      refine ⟨(∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)),
        ⟨candidate, rfl⟩, penalty * radius, Set.mem_singleton _, ?_⟩
      unfold Optimization.scalarLagrangian
      ring
    · rintro ⟨baseValue, hbaseValue, shift, hshift, hsum⟩
      obtain ⟨candidate, hbaseValue_eq⟩ := hbaseValue
      have hshift_eq : shift = penalty * radius := Set.mem_singleton_iff.mp hshift
      subst baseValue
      subst shift
      refine ⟨(∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)),
        ∫ x, loss x ∂(candidate.source : Measure α)), ?_, ?_⟩
      · exact ⟨candidate, rfl⟩
      · unfold Optimization.scalarLagrangian
        rw [← hsum]
        ring
  unfold Optimization.scalarDualObjective penalizedCouplingValue
  have hbase_bdd : BddAbove base := by simpa [base] using hbounded
  rw [hset, csSup_add hbase_ne hbase_bdd (Set.singleton_nonempty _) bddAbove_singleton]
  simp only [csSup_singleton]
  rfl

/--
Strong scalar duality for the coupling-level transport ball.  The compact
convex frontier and strict feasible coupling are ordinary geometric premises;
unlike the cost-infimum frontier, this formulation is aligned with the linear
structure of couplings.
-/
theorem constrainedRealCouplingValue_eq_scalarDualValue_of_compact_convex_frontier
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hfrontier_compact : IsCompact (realCouplingCostPayoffFrontier loss c nominal))
    (hfrontier_convex : Convex ℝ (realCouplingCostPayoffFrontier loss c nominal))
    (hstrict : ∃ point ∈ realCouplingCostPayoffFrontier loss c nominal, point.1 < radius) :
    constrainedRealCouplingValue loss c radius nominal =
      Optimization.scalarDualValue (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  rw [constrainedRealCouplingValue_eq_scalarPrimalValue_frontier]
  exact Optimization.scalarStrongDuality_costPayoffFrontier
    (realCouplingCostPayoffFrontier loss c nominal) radius hfrontier_compact hfrontier_convex
      hstrict

/--
Strong scalar duality for a coupling-level transport ball from convexity,
strict diagonal feasibility, and real boundedness alone.  The scalar Slater
argument works with the closure of the attainable hypograph, so a nonattained
bounded frontier payoff does not force a separate closed-frontier assumption.
-/
theorem constrainedRealCouplingValue_eq_scalarDualValue_of_bdd
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hfrontier_convex : Convex ℝ (realCouplingCostPayoffFrontier loss c nominal))
    (hstrict : ∃ point ∈ realCouplingCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realCouplingCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realCouplingCostPayoffFrontier loss c nominal)) :
    constrainedRealCouplingValue loss c radius nominal =
      Optimization.scalarDualValue (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  rw [constrainedRealCouplingValue_eq_scalarPrimalValue_frontier]
  apply Optimization.scalarStrongDuality_of_isScalarSlater_of_bdd
  · refine ⟨hfrontier_convex, ?_⟩
    intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
    change weightFirst * first.2 + weightSecond * second.2 ≤
      weightFirst * first.2 + weightSecond * second.2
    exact le_rfl
  · refine {
      convex_X := hfrontier_convex
      convex_g := ?_
      strict_feasible := ?_ }
    · refine ⟨hfrontier_convex, ?_⟩
      intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
      change weightFirst * first.1 + weightSecond * second.1 - radius ≤
        weightFirst * (first.1 - radius) + weightSecond * (second.1 - radius)
      have hradius : (weightFirst + weightSecond) * radius = radius := by
        rw [hweights]
        ring
      exact le_of_eq (by
        calc
          weightFirst * first.1 + weightSecond * second.1 - radius =
              weightFirst * first.1 + weightSecond * second.1 -
                (weightFirst + weightSecond) * radius := by rw [hradius]
          _ = weightFirst * (first.1 - radius) +
              weightSecond * (second.1 - radius) := by ring)
    · obtain ⟨point, hpoint, hcost⟩ := hstrict
      exact ⟨point, hpoint, sub_neg.mpr hcost⟩
  · exact hprimal_bdd
  · exact hdual_bdd

/--
Strong scalar duality for a coupling-level transport ball from closedness of
its attainable cost--payoff hypograph.  This is the noncompact counterpart of
`constrainedRealCouplingValue_eq_scalarDualValue_of_compact_convex_frontier`:
the underlying probability-law carrier need not be compact once the exact
finite-dimensional no-gap condition and real boundedness of the primal and
fixed-multiplier objectives are established.
-/
theorem constrainedRealCouplingValue_eq_scalarDualValue_of_closed_achievable
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hfrontier_convex : Convex ℝ (realCouplingCostPayoffFrontier loss c nominal))
    (hstrict : ∃ point ∈ realCouplingCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realCouplingCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realCouplingCostPayoffFrontier loss c nominal))
    (hachievable_closed : IsClosed (Optimization.scalarAchievableSet
      (realCouplingCostPayoffFrontier loss c nominal) Prod.snd
      (fun point => point.1 - radius))) :
    constrainedRealCouplingValue loss c radius nominal =
      Optimization.scalarDualValue (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  rw [constrainedRealCouplingValue_eq_scalarPrimalValue_frontier]
  apply Optimization.scalarStrongDuality_of_isScalarSlater_of_closed_achievable
  · refine ⟨hfrontier_convex, ?_⟩
    intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
    change weightFirst * first.2 + weightSecond * second.2 ≤
      weightFirst * first.2 + weightSecond * second.2
    exact le_rfl
  · refine {
      convex_X := hfrontier_convex
      convex_g := ?_
      strict_feasible := ?_ }
    · refine ⟨hfrontier_convex, ?_⟩
      intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
      change weightFirst * first.1 + weightSecond * second.1 - radius ≤
        weightFirst * (first.1 - radius) + weightSecond * (second.1 - radius)
      have hradius : (weightFirst + weightSecond) * radius = radius := by
        rw [hweights]
        ring
      exact le_of_eq (by
        calc
          weightFirst * first.1 + weightSecond * second.1 - radius =
              weightFirst * first.1 + weightSecond * second.1 -
                (weightFirst + weightSecond) * radius := by rw [hradius]
          _ = weightFirst * (first.1 - radius) +
              weightSecond * (second.1 - radius) := by ring)
    · obtain ⟨point, hpoint, hcost⟩ := hstrict
      exact ⟨point, hpoint, sub_neg.mpr hcost⟩
  · exact hprimal_bdd
  · exact hdual_bdd
  · exact hachievable_closed

/--
The infimum-cost transport ball and the concrete-coupling transport ball have
the same expected-payoff value when every source law in the former ball has a
cost-attaining (or otherwise radius-feasible) coupling.  The two directions
make the roles distinct: any feasible coupling supplies an infimum-ball law
by `realTransportCost_le_expectedCost`, while the reverse direction is exactly
the explicit attainment-on-the-ball hypothesis.
-/
theorem constrainedRealTransportValue_eq_constrainedRealCouplingValue_of_attained_ball
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hcoupling_nonempty : Nonempty { coupling : FiniteRealCostCouplingTo c nominal //
      ∫ pair, c pair ∂(coupling.coupling.joint : Measure (α × β)) ≤ radius })
    (hsource_bounded : BddAbove (Set.range fun candidate : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) ∧
        realTransportCost c source nominal ≤ radius } =>
      ∫ x, loss x ∂(candidate.1 : Measure α)))
    (hcoupling_bounded : BddAbove (Set.range fun candidate :
      { coupling : FiniteRealCostCouplingTo c nominal //
        ∫ pair, c pair ∂(coupling.coupling.joint : Measure (α × β)) ≤ radius } =>
      ∫ x, loss x ∂(candidate.1.source : Measure α)))
    (hattained_ball : ∀ source : ProbabilityMeasure α,
      ∀ hfinite : Nonempty (FiniteRealCostCoupling c source nominal),
      realTransportCost c source nominal ≤ radius →
        ∃ coupling : FiniteRealCostCoupling c source nominal,
          ∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)) ≤ radius) :
    constrainedRealTransportValue loss c radius nominal =
      constrainedRealCouplingValue loss c radius nominal := by
  let sourceValue : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) ∧
        realTransportCost c source nominal ≤ radius } → ℝ :=
    fun candidate => ∫ x, loss x ∂(candidate.1 : Measure α)
  let couplingValue : { coupling : FiniteRealCostCouplingTo c nominal //
      ∫ pair, c pair ∂(coupling.coupling.joint : Measure (α × β)) ≤ radius } → ℝ :=
    fun candidate => ∫ x, loss x ∂(candidate.1.source : Measure α)
  obtain ⟨coupling⟩ := hcoupling_nonempty
  let source : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) ∧
        realTransportCost c source nominal ≤ radius } := by
    refine ⟨coupling.1.source, ⟨?_, ?_⟩⟩
    · exact ⟨⟨coupling.1.coupling, coupling.1.cost_integrable⟩⟩
    · calc
        realTransportCost c coupling.1.source nominal ≤
            ∫ pair, c pair ∂(coupling.1.coupling.joint : Measure (α × β)) :=
          realTransportCost_le_expectedCost c coupling.1.source nominal hcost_nonneg
            ⟨coupling.1.coupling, coupling.1.cost_integrable⟩
        _ ≤ radius := coupling.2
  have hsource_nonempty : (Set.range sourceValue).Nonempty :=
    ⟨sourceValue source, ⟨source, rfl⟩⟩
  have hcoupling_nonempty' : (Set.range couplingValue).Nonempty :=
    ⟨couplingValue coupling, ⟨coupling, rfl⟩⟩
  apply le_antisymm
  · unfold constrainedRealTransportValue
    change sSup (Set.range sourceValue) ≤ sSup (Set.range couplingValue)
    apply csSup_le hsource_nonempty
    rintro payoff ⟨candidate, rfl⟩
    obtain ⟨attaining, hattaining_cost⟩ :=
      hattained_ball candidate.1 candidate.2.1 candidate.2.2
    let feasibleCoupling : { coupling : FiniteRealCostCouplingTo c nominal //
        ∫ pair, c pair ∂(coupling.coupling.joint : Measure (α × β)) ≤ radius } :=
      ⟨{
        source := candidate.1
        coupling := attaining.1
        cost_integrable := attaining.2 }, hattaining_cost⟩
    exact le_csSup hcoupling_bounded (Set.mem_range_self feasibleCoupling)
  · unfold constrainedRealCouplingValue
    change sSup (Set.range couplingValue) ≤ sSup (Set.range sourceValue)
    apply csSup_le hcoupling_nonempty'
    rintro payoff ⟨candidate, rfl⟩
    let feasibleSource : { source : ProbabilityMeasure α //
        Nonempty (FiniteRealCostCoupling c source nominal) ∧
          realTransportCost c source nominal ≤ radius } := by
      refine ⟨candidate.1.source, ⟨?_, ?_⟩⟩
      · exact ⟨⟨candidate.1.coupling, candidate.1.cost_integrable⟩⟩
      · calc
          realTransportCost c candidate.1.source nominal ≤
              ∫ pair, c pair ∂(candidate.1.coupling.joint : Measure (α × β)) :=
            realTransportCost_le_expectedCost c candidate.1.source nominal hcost_nonneg
              ⟨candidate.1.coupling, candidate.1.cost_integrable⟩
          _ ≤ radius := candidate.2
    exact le_csSup hsource_bounded (Set.mem_range_self feasibleSource)

/--
The scalar-duality objective of a transport cost--payoff frontier is its
infimum-cost penalized value plus the radius term.  Boundedness is stated for
the concrete penalized image, so the result does not hide any extended-value
convention for a supremum over probability laws.
-/
theorem scalarDualObjective_frontier_eq_realTransportCostPenalizedValue_add
    (loss : α → ℝ) (c : α × β → ℝ) (penalty radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hfinite : Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) })
    (hbounded : BddAbove (Set.range fun candidate : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) } =>
      (∫ x, loss x ∂(candidate.1 : Measure α)) -
        penalty * realTransportCost c candidate.1 nominal)) :
    Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
      realTransportCostPenalizedValue loss c penalty nominal + penalty * radius := by
  let base : Set ℝ := Set.range fun candidate : { source : ProbabilityMeasure α //
    Nonempty (FiniteRealCostCoupling c source nominal) } =>
    (∫ x, loss x ∂(candidate.1 : Measure α)) -
      penalty * realTransportCost c candidate.1 nominal
  have hbase_ne : base.Nonempty := by
    obtain ⟨candidate⟩ := hfinite
    exact ⟨_, ⟨candidate, rfl⟩⟩
  have hset :
      (fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
        realTransportCostPayoffFrontier loss c nominal = base + {penalty * radius} := by
    ext value
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      change point ∈ Set.range (fun candidate : { source : ProbabilityMeasure α //
        Nonempty (FiniteRealCostCoupling c source nominal) } =>
        (realTransportCost c candidate.1 nominal,
          ∫ x, loss x ∂(candidate.1 : Measure α))) at hpoint
      obtain ⟨candidate, rfl⟩ := hpoint
      refine ⟨(∫ x, loss x ∂(candidate.1 : Measure α)) -
          penalty * realTransportCost c candidate.1 nominal, ⟨candidate, rfl⟩,
        penalty * radius, Set.mem_singleton _, ?_⟩
      unfold Optimization.scalarLagrangian
      ring
    · rintro ⟨baseValue, hbaseValue, shift, hshift, hsum⟩
      obtain ⟨candidate, hbaseValue_eq⟩ := hbaseValue
      have hshift_eq : shift = penalty * radius := Set.mem_singleton_iff.mp hshift
      subst baseValue
      subst shift
      refine ⟨(realTransportCost c candidate.1 nominal,
        ∫ x, loss x ∂(candidate.1 : Measure α)), ?_, ?_⟩
      · exact ⟨candidate, rfl⟩
      · unfold Optimization.scalarLagrangian
        rw [← hsum]
        ring
  unfold Optimization.scalarDualObjective realTransportCostPenalizedValue
  have hbase_bdd : BddAbove base := by simpa [base] using hbounded
  rw [hset, csSup_add hbase_ne hbase_bdd (Set.singleton_nonempty _) bddAbove_singleton]
  simp only [csSup_singleton]
  rfl

/--
For a strictly positive penalty, minimizing the coupling cost before taking
the source-law supremum is equivalent to taking the supremum over finite-cost
couplings directly.  The proof uses epsilon-optimal couplings in one direction
and the infimum lower bound in the other, so it does not assume an optimal
transport plan.
-/
theorem realTransportCostPenalizedValue_eq_penalizedCouplingValue_of_pos
    (loss : α → ℝ) (c : α × β → ℝ) (penalty : ℝ)
    (nominal : ProbabilityMeasure β)
    (hfinite : Nonempty (FiniteRealCostCouplingTo c nominal))
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hpenalty : 0 < penalty)
    (hbounded : BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
      (∫ x, loss x ∂(candidate.source : Measure α)) -
        penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)))) :
    realTransportCostPenalizedValue loss c penalty nominal =
      penalizedCouplingValue loss c penalty nominal := by
  let sourceScore : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) } → ℝ :=
    fun source => (∫ x, loss x ∂(source.1 : Measure α)) -
      penalty * realTransportCost c source.1 nominal
  have hsource_ne : (Set.range sourceScore).Nonempty := by
    obtain ⟨candidate⟩ := hfinite
    exact ⟨sourceScore ⟨candidate.source,
      ⟨⟨candidate.coupling, candidate.cost_integrable⟩⟩⟩,
      ⟨⟨candidate.source, ⟨⟨candidate.coupling, candidate.cost_integrable⟩⟩⟩, rfl⟩⟩
  have hsource_le : ∀ source : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) },
      sourceScore source ≤ penalizedCouplingValue loss c penalty nominal := by
    intro source
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let delta : ℝ := epsilon / (penalty + 1)
    have hdenom_pos : 0 < penalty + 1 := by linarith
    have hdelta_pos : 0 < delta := div_pos hepsilon hdenom_pos
    have hinf_lt : realTransportCost c source.1 nominal <
        realTransportCost c source.1 nominal + delta := by linarith
    obtain ⟨coupling, hcoupling_lt⟩ :=
      exists_realExpectedCost_lt_of_realTransportCost_lt c source.1 nominal source.2 hinf_lt
    let candidate : FiniteRealCostCouplingTo c nominal := {
      source := source.1
      coupling := coupling.1
      cost_integrable := coupling.2 }
    have hcandidate_le :
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)) ≤
          penalizedCouplingValue loss c penalty nominal := by
      unfold penalizedCouplingValue
      exact le_csSup hbounded (Set.mem_range_self candidate)
    have hpenalty_delta_le : penalty * delta ≤ epsilon := by
      dsimp [delta]
      calc
        penalty * (epsilon / (penalty + 1)) =
            epsilon * (penalty / (penalty + 1)) := by field_simp
        _ ≤ epsilon * 1 := by
          gcongr
          exact (div_le_one₀ hdenom_pos).mpr (by linarith)
        _ = epsilon := by ring
    dsimp [sourceScore]
    have hscaled_cost : penalty *
        ∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)) ≤
          penalty * (realTransportCost c source.1 nominal + delta) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hcoupling_lt) hpenalty.le
    have hcandidate_eq :
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)) =
        (∫ x, loss x ∂(source.1 : Measure α)) -
          penalty * ∫ pair, c pair ∂(coupling.1.joint : Measure (α × β)) := by
      rfl
    rw [hcandidate_eq] at hcandidate_le
    linarith
  have hsource_bdd : BddAbove (Set.range sourceScore) := by
    refine ⟨penalizedCouplingValue loss c penalty nominal, ?_⟩
    rintro value ⟨source, rfl⟩
    exact hsource_le source
  apply le_antisymm
  · unfold realTransportCostPenalizedValue
    simpa [sourceScore] using (csSup_le hsource_ne (by
      rintro value ⟨source, rfl⟩
      exact hsource_le source))
  · unfold penalizedCouplingValue
    apply csSup_le (Set.range_nonempty _)
    rintro value ⟨candidate, rfl⟩
    let source : { source : ProbabilityMeasure α //
        Nonempty (FiniteRealCostCoupling c source nominal) } :=
      ⟨candidate.source, ⟨⟨candidate.coupling, candidate.cost_integrable⟩⟩⟩
    have hcost_le := realTransportCost_le_expectedCost c candidate.source nominal hcost_nonneg
      ⟨candidate.coupling, candidate.cost_integrable⟩
    have hsource_mem : sourceScore source ∈ Set.range sourceScore :=
      Set.mem_range_self source
    have hsource_score_le : sourceScore source ≤
        sSup (Set.range sourceScore) := le_csSup hsource_bdd hsource_mem
    have hcoupling_score_le :
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)) ≤
        sourceScore source := by
      dsimp [sourceScore, source]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hcost_le hpenalty.le) _
    calc
      (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × β)) ≤
          sourceScore source := hcoupling_score_le
      _ ≤ sSup (Set.range sourceScore) := hsource_score_le
      _ = realTransportCostPenalizedValue loss c penalty nominal := by
        rfl

/--
At zero penalty, the finite-cost source-law and finite-cost coupling
formulations have the same values.  This is a set-level reindexing, so no
cost minimizer or moment bound is needed.
-/
theorem realTransportCostPenalizedValue_zero_eq_penalizedCouplingValue_zero
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β) :
    realTransportCostPenalizedValue loss c 0 nominal =
      penalizedCouplingValue loss c 0 nominal := by
  unfold realTransportCostPenalizedValue penalizedCouplingValue
  congr 1
  ext value
  constructor
  · rintro ⟨source, rfl⟩
    obtain ⟨coupling⟩ := source.2
    refine ⟨{
      source := source.1
      coupling := coupling.1
      cost_integrable := coupling.2 }, ?_⟩
    simp
  · rintro ⟨candidate, rfl⟩
    refine ⟨⟨candidate.source,
      ⟨⟨candidate.coupling, candidate.cost_integrable⟩⟩⟩, ?_⟩
    simp

/--
If every source law has a finite-cost coupling to the nominal law, the
zero-penalty infimum-cost value is the unrestricted expected-payoff value.
This makes the usual `0 · transportCost` convention explicit rather than
silently discarding laws with an infinite transport moment.
-/
theorem realTransportCostPenalizedValue_zero_eq_unpenalizedValue
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β)
    (hfinite_all : ∀ source : ProbabilityMeasure α,
      Nonempty (FiniteRealCostCoupling c source nominal)) :
    realTransportCostPenalizedValue loss c 0 nominal = unpenalizedValue loss := by
  unfold realTransportCostPenalizedValue unpenalizedValue
  congr 1
  ext value
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨source.1, by simp⟩
  · rintro ⟨source, rfl⟩
    refine ⟨⟨source, hfinite_all source⟩, ?_⟩
    simp

/--
The zero-penalty value over finite-cost source laws never exceeds the
unrestricted zero-penalty value.  This is the one-sided comparison needed
when the extended-value convention admits every source law only at multiplier
zero; it does not assert finite transport cost for those additional laws.
-/
theorem realTransportCostPenalizedValue_zero_le_unpenalizedValue
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β)
    (hfinite : Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) })
    (hunpenalized_bdd : BddAbove (Set.range fun source : ProbabilityMeasure α =>
      ∫ x, loss x ∂(source : Measure α))) :
    realTransportCostPenalizedValue loss c 0 nominal ≤ unpenalizedValue loss := by
  unfold realTransportCostPenalizedValue unpenalizedValue
  simp only [zero_mul, sub_zero]
  apply csSup_le
  · obtain ⟨source⟩ := hfinite
    exact ⟨_, ⟨source, rfl⟩⟩
  · rintro _ ⟨source, rfl⟩
    exact le_csSup hunpenalized_bdd ⟨source.1, rfl⟩

/--
At zero penalty, finite-cost access to each Dirac source law already suffices
to recover the unrestricted payoff value.  This is strictly weaker than
finite-cost access for every source law: bounded/integrable loss controls the
upper bound, while Dirac laws recover every pointwise payoff lower bound.
-/
theorem realTransportCostPenalizedValue_zero_eq_unpenalizedValue_of_dirac
    [Nonempty α]
    (loss : α → ℝ) (c : α × β → ℝ) (nominal : ProbabilityMeasure β)
    (hloss_strongly_measurable : StronglyMeasurable loss)
    (hloss_integrable : ∀ source : ProbabilityMeasure α,
      Integrable loss (source : Measure α))
    (hloss_bddAbove : BddAbove (Set.range loss))
    (hdirac_finite : ∀ point : α,
      Nonempty (FiniteRealCostCoupling c (diracProba point) nominal)) :
    realTransportCostPenalizedValue loss c 0 nominal = unpenalizedValue loss := by
  rw [unpenalizedValue_eq_sSup_range loss hloss_strongly_measurable
    hloss_integrable hloss_bddAbove]
  unfold realTransportCostPenalizedValue
  simp only [zero_mul, sub_zero]
  let finiteScores : Set ℝ := Set.range fun candidate : { source : ProbabilityMeasure α //
    Nonempty (FiniteRealCostCoupling c source nominal) } =>
      ∫ x, loss x ∂(candidate.1 : Measure α)
  change sSup finiteScores = sSup (Set.range loss)
  have hfinite_ne : finiteScores.Nonempty := by
    let point : α := Classical.choice inferInstance
    exact ⟨∫ x, loss x ∂(diracProba point : Measure α),
      ⟨⟨diracProba point, hdirac_finite point⟩, rfl⟩⟩
  have hscore_le : ∀ candidate : { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) },
      (∫ x, loss x ∂(candidate.1 : Measure α)) ≤ sSup (Set.range loss) := by
    intro candidate
    calc
      (∫ x, loss x ∂(candidate.1 : Measure α)) ≤
          ∫ _ : α, sSup (Set.range loss) ∂(candidate.1 : Measure α) := by
        apply integral_mono (hloss_integrable candidate.1) (integrable_const _)
        intro x
        exact le_csSup hloss_bddAbove (Set.mem_range_self x)
      _ = sSup (Set.range loss) := by simp
  have hfinite_bdd : BddAbove finiteScores := by
    refine ⟨sSup (Set.range loss), ?_⟩
    rintro value ⟨candidate, rfl⟩
    exact hscore_le candidate
  apply le_antisymm
  · exact csSup_le hfinite_ne (by
      rintro value ⟨candidate, rfl⟩
      exact hscore_le candidate)
  · apply csSup_le (Set.range_nonempty loss)
    rintro value ⟨point, rfl⟩
    rw [← integral_dirac' loss point hloss_strongly_measurable]
    exact le_csSup hfinite_bdd
      ⟨⟨diracProba point, hdirac_finite point⟩, rfl⟩

/--
The real transport-ball value is exactly the scalar-constrained primal value
of its concrete cost--payoff frontier.  This conversion is algebraic: it does
not assume transport-plan attainment, compactness, or strong duality.
-/
theorem constrainedRealTransportValue_eq_scalarPrimalValue_frontier
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β) :
    constrainedRealTransportValue loss c radius nominal =
      Optimization.scalarPrimalValue (realTransportCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  unfold constrainedRealTransportValue Optimization.scalarPrimalValue
    Optimization.scalarFeasible realTransportCostPayoffFrontier
  congr 1
  ext payoff
  constructor
  · rintro ⟨candidate, rfl⟩
    refine ⟨(realTransportCost c candidate.1 nominal,
      ∫ x, loss x ∂(candidate.1 : Measure α)), ?_, rfl⟩
    refine ⟨⟨⟨candidate.1, candidate.2.1⟩, rfl⟩, ?_⟩
    exact sub_nonpos.mpr candidate.2.2
  · rintro ⟨point, hpoint, hpayoff⟩
    obtain ⟨hfrontier, hfeasible⟩ := hpoint
    obtain ⟨candidate, hpoint_eq⟩ := hfrontier
    subst point
    refine ⟨⟨candidate.1, candidate.2, sub_nonpos.mp hfeasible⟩, ?_⟩
    simpa using hpayoff

/--
Strong scalar duality for the source's infimum-cost transport ball, assuming
convexity of its attainable upper/lower hypograph rather than convexity of the
exact cost graph.  This is the noncompact no-gap step that remains valid when
finite-cost plans only approximate the transport infimum.
-/
theorem constrainedRealTransportValue_eq_scalarDualValue_of_convex_achievableSet
    (loss : α → ℝ) (c : α × β → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure β)
    (hachievable_convex : Convex ℝ (Optimization.scalarAchievableSet
      (realTransportCostPayoffFrontier loss c nominal) Prod.snd
      (fun point => point.1 - radius)))
    (hstrict : ∃ point ∈ realTransportCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realTransportCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realTransportCostPayoffFrontier loss c nominal)) :
    constrainedRealTransportValue loss c radius nominal =
      Optimization.scalarDualValue (realTransportCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  rw [constrainedRealTransportValue_eq_scalarPrimalValue_frontier]
  apply Optimization.scalarStrongDuality_of_convex_achievableSet_of_bdd
  · exact hachievable_convex
  · obtain ⟨point, hpoint, hcost⟩ := hstrict
    exact ⟨point, hpoint, sub_neg.mpr hcost⟩
  · exact hprimal_bdd
  · exact hdual_bdd

/--
Weak duality for the real-cost transport-ball value.  No optimal transport
plan, strong duality, or measurable maximizer is assumed: each candidate is
handled by the finite-real-cost infimum-ball certificate, then `csSup_le`
passes that common upper bound to the ball supremum.

Library provenance: this uses Mathlib's
[`csSup_le`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean)
at the repository-pinned Apache-2.0 Mathlib revision.  The transport-ball
value, finite-domain condition, and weak-duality proof are local; no upstream
proof text is copied or ported.
-/
theorem constrainedRealTransportValue_le_integral_envelope_add_penalty
    (loss : α → ℝ) (c : α × β → ℝ) (penalty radius : ℝ)
    (nominal : ProbabilityMeasure β) (envelope : β → ℝ)
    (hfeasible : Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) ∧
        realTransportCost c source nominal ≤ radius })
    (hloss_integrable : ∀ source : ProbabilityMeasure α,
      Integrable loss (source : Measure α))
    (henvelope_integrable : Integrable envelope (nominal : Measure β))
    (hpenalty : 0 ≤ penalty)
    (hdom : ∀ pair : α × β, loss pair.1 ≤ envelope pair.2 + penalty * c pair) :
    constrainedRealTransportValue loss c radius nominal ≤
      (∫ y, envelope y ∂(nominal : Measure β)) + penalty * radius := by
  unfold constrainedRealTransportValue
  apply csSup_le
  · obtain ⟨candidate⟩ := hfeasible
    exact ⟨_, ⟨candidate, rfl⟩⟩
  · rintro _ ⟨candidate, rfl⟩
    exact integral_fst_le_integral_snd_add_penalty_of_realTransportCost_le
      penalty radius (hloss_integrable candidate.1) henvelope_integrable hpenalty
      candidate.2.1 candidate.2.2 hdom

/--
The diagonal coupling has finite real cost when the cost is measurable and
vanishes on the diagonal.  This makes the usual nonnegative-radius
transport-ball nonemptiness condition explicit in real-valued transport
models.

Library provenance: `integrable_map_measure` is Mathlib's unchanged map
integrability equivalence from
[`MeasureTheory/Function/L1Space/Integrable.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean)
at the repository-pinned Apache-2.0 Mathlib revision.  The diagonal-coupling
specialization is local and no upstream proof text is copied or ported.
-/
theorem integrable_refl_cost_of_self_eq_zero
    {α : Type*} [MeasurableSpace α]
    (c : α × α → ℝ) (nominal : ProbabilityMeasure α)
    (hc_measurable : Measurable c)
    (hself_zero : ∀ point, c (point, point) = 0) :
    Integrable c ((ProbabilityCoupling.refl nominal).joint : Measure (α × α)) := by
  change Integrable c
    (Measure.map (fun point : α => (id point, id point)) (nominal : Measure α))
  rw [integrable_map_measure hc_measurable.aestronglyMeasurable
    (measurable_id.prodMk measurable_id).aemeasurable]
  exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun point =>
    (hself_zero point).symm)

/-- The finite-real-cost diagonal coupling selected by `integrable_refl_cost_of_self_eq_zero`. -/
noncomputable def reflFiniteRealCostCoupling
    {α : Type*} [MeasurableSpace α]
    (c : α × α → ℝ) (nominal : ProbabilityMeasure α)
    (hc_measurable : Measurable c)
    (hself_zero : ∀ point, c (point, point) = 0) :
    FiniteRealCostCoupling c nominal nominal :=
  ⟨ProbabilityCoupling.refl nominal,
    integrable_refl_cost_of_self_eq_zero c nominal hc_measurable hself_zero⟩

/-- The selected finite-real-cost diagonal coupling has expected cost zero. -/
theorem integral_reflFiniteRealCostCoupling_eq_zero
    {α : Type*} [MeasurableSpace α]
    (c : α × α → ℝ) (nominal : ProbabilityMeasure α)
    (hc_measurable : Measurable c)
    (hself_zero : ∀ point, c (point, point) = 0) :
    ∫ pair, c pair ∂((reflFiniteRealCostCoupling c nominal hc_measurable hself_zero).1.joint :
      Measure (α × α)) = 0 := by
  change ∫ pair, c pair ∂
    (Measure.map (fun point : α => (id point, id point)) (nominal : Measure α)) = 0
  rw [integral_map (measurable_id.prodMk measurable_id).aemeasurable
    hc_measurable.aestronglyMeasurable]
  simp only [hself_zero, integral_zero]

/-- Under nonnegative diagonal-zero cost, the real transport cost of a law to itself is at most zero. -/
theorem realTransportCost_refl_le_zero
    {α : Type*} [MeasurableSpace α]
    (c : α × α → ℝ) (nominal : ProbabilityMeasure α)
    (hc_measurable : Measurable c)
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hself_zero : ∀ point, c (point, point) = 0) :
    realTransportCost c nominal nominal ≤ 0 := by
  unfold realTransportCost
  have hbelow : BddBelow (Set.range fun π : FiniteRealCostCoupling c nominal nominal =>
      ∫ pair, c pair ∂(π.1.joint : Measure (α × α))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨π, rfl⟩
    exact integral_nonneg fun pair => hcost_nonneg pair
  have hle := csInf_le hbelow (Set.mem_range_self
    (reflFiniteRealCostCoupling c nominal hc_measurable hself_zero))
  rw [integral_reflFiniteRealCostCoupling_eq_zero c nominal hc_measurable hself_zero] at hle
  exact hle

/-- A nonnegative-radius ball is nonempty under measurable nonnegative diagonal-zero cost. -/
theorem constrainedRealTransportValue_feasible_refl
    {α : Type*} [MeasurableSpace α]
    (c : α × α → ℝ) (radius : ℝ) (nominal : ProbabilityMeasure α)
    (hc_measurable : Measurable c)
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hself_zero : ∀ point, c (point, point) = 0)
    (hradius : 0 ≤ radius) :
    Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) ∧
        realTransportCost c source nominal ≤ radius } := by
  refine ⟨nominal, ?_, ?_⟩
  · exact ⟨reflFiniteRealCostCoupling c nominal hc_measurable hself_zero⟩
  · exact (realTransportCost_refl_le_zero c nominal hc_measurable hcost_nonneg hself_zero).trans
      hradius

/--
Compact convexity of the *actual* cost--payoff frontier, together with the
usual diagonal strict-feasibility condition, proves the constrained
transport-ball/lagrangian scalar duality step.  The conclusion is intentionally
left at the scalar frontier dual: identifying each fixed-penalty frontier
objective with a pointwise transport envelope is a separate selection theorem.
-/
theorem constrainedRealTransportValue_eq_scalarDualValue_of_compact_convex_frontier
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α)
    (hfrontier_compact : IsCompact (realTransportCostPayoffFrontier loss c nominal))
    (hfrontier_convex : Convex ℝ (realTransportCostPayoffFrontier loss c nominal))
    (hc_measurable : Measurable c)
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hself_zero : ∀ point, c (point, point) = 0)
    (hradius : 0 < radius) :
    constrainedRealTransportValue loss c radius nominal =
      Optimization.scalarDualValue (realTransportCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) := by
  rw [constrainedRealTransportValue_eq_scalarPrimalValue_frontier]
  apply Optimization.scalarStrongDuality_costPayoffFrontier
    (realTransportCostPayoffFrontier loss c nominal) radius hfrontier_compact hfrontier_convex
  refine ⟨(realTransportCost c nominal nominal,
    ∫ x, loss x ∂(nominal : Measure α)), ?_, ?_⟩
  · exact ⟨⟨nominal,
      ⟨reflFiniteRealCostCoupling c nominal hc_measurable hself_zero⟩⟩, rfl⟩
  · change realTransportCost c nominal nominal < radius
    exact (realTransportCost_refl_le_zero c nominal hc_measurable hcost_nonneg hself_zero).trans_lt
      hradius

/--
The envelope-side scalar dual for a real transport-ball problem.  The envelope
is passed explicitly because its identification with a pointwise supremum is a
separate measurable-selection theorem.
-/
noncomputable def constrainedRealTransportEnvelopeDualValue
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ) : ℝ :=
  sInf ((fun penalty => (∫ x, envelope penalty x ∂(nominal : Measure α)) +
    penalty * radius) '' Set.Ici 0)

/--
An arbitrary-law constrained transport equality obtained from a compact convex
cost--payoff frontier and independently proved fixed-penalty envelope
identities.  This theorem does not accept a constrained-duality equality as a
premise: the only frontier assumptions are compactness and convexity, and the
strict Slater point is constructed from the diagonal coupling.  The fixed
penalty identities are intentionally separate, so applications must prove
their measurable-selection and zero-penalty conventions explicitly.
-/
theorem constrainedRealTransportValue_eq_envelopeDualValue_of_compact_convex_frontier
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ)
    (hfrontier_compact : IsCompact (realTransportCostPayoffFrontier loss c nominal))
    (hfrontier_convex : Convex ℝ (realTransportCostPayoffFrontier loss c nominal))
    (hc_measurable : Measurable c)
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hself_zero : ∀ point, c (point, point) = 0)
    (hradius : 0 < radius)
    (hfinite : Nonempty (FiniteRealCostCouplingTo c nominal))
    (hfinite_all : ∀ source : ProbabilityMeasure α,
      Nonempty (FiniteRealCostCoupling c source nominal))
    (hsource_bounded : ∀ penalty, 0 ≤ penalty →
      BddAbove (Set.range fun candidate : { source : ProbabilityMeasure α //
        Nonempty (FiniteRealCostCoupling c source nominal) } =>
        (∫ x, loss x ∂(candidate.1 : Measure α)) -
          penalty * realTransportCost c candidate.1 nominal))
    (hcoupling_bounded : ∀ penalty, 0 < penalty →
      BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × α))))
    (hpenalized_envelope : ∀ penalty, 0 < penalty →
      penalizedCouplingValue loss c penalty nominal =
        ∫ x, envelope penalty x ∂(nominal : Measure α))
    (hzero_envelope : unpenalizedValue loss =
      ∫ x, envelope 0 x ∂(nominal : Measure α)) :
    constrainedRealTransportValue loss c radius nominal =
      constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
  have hfinite_frontier : Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) } := by
    obtain ⟨candidate⟩ := hfinite
    exact ⟨candidate.source, ⟨⟨candidate.coupling, candidate.cost_integrable⟩⟩⟩
  have hfixed : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
        (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
    intro penalty hpenalty_nonneg
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty_nonneg) with rfl | hpenalty_pos
    · calc
        Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) 0 =
            realTransportCostPenalizedValue loss c 0 nominal + 0 * radius :=
          scalarDualObjective_frontier_eq_realTransportCostPenalizedValue_add
            loss c 0 radius nominal hfinite_frontier (hsource_bounded 0 (by norm_num))
        _ = unpenalizedValue loss := by
          rw [realTransportCostPenalizedValue_zero_eq_unpenalizedValue loss c nominal hfinite_all]
          ring
        _ = (∫ x, envelope 0 x ∂(nominal : Measure α)) + 0 * radius := by
          rw [hzero_envelope]
          ring
    · calc
        Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) penalty =
            realTransportCostPenalizedValue loss c penalty nominal + penalty * radius :=
          scalarDualObjective_frontier_eq_realTransportCostPenalizedValue_add
            loss c penalty radius nominal hfinite_frontier
              (hsource_bounded penalty hpenalty_pos.le)
        _ = penalizedCouplingValue loss c penalty nominal + penalty * radius := by
          rw [realTransportCostPenalizedValue_eq_penalizedCouplingValue_of_pos
            loss c penalty nominal hfinite hcost_nonneg hpenalty_pos
            (hcoupling_bounded penalty hpenalty_pos)]
        _ = (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
          rw [hpenalized_envelope penalty hpenalty_pos]
  calc
    constrainedRealTransportValue loss c radius nominal =
        Optimization.scalarDualValue (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) :=
      constrainedRealTransportValue_eq_scalarDualValue_of_compact_convex_frontier
        loss c radius nominal hfrontier_compact hfrontier_convex hc_measurable hcost_nonneg
          hself_zero hradius
    _ = constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
      unfold Optimization.scalarDualValue constrainedRealTransportEnvelopeDualValue
      congr 1
      ext value
      constructor
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, (hfixed penalty hpenalty).symm⟩
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, hfixed penalty hpenalty⟩

/--
The source's infimum-cost transport ball equals its envelope dual whenever the
attainable upper/lower hypograph is convex and the infimum-cost fixed-penalty
values have been identified with that envelope.  No transport-plan attainment
is assumed: the scalar no-gap step is the direct
`constrainedRealTransportValue_eq_scalarDualValue_of_convex_achievableSet`
route.
-/
theorem constrainedRealTransportValue_eq_envelopeDualValue_of_convex_achievableSet
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ)
    (hachievable_convex : Convex ℝ (Optimization.scalarAchievableSet
      (realTransportCostPayoffFrontier loss c nominal) Prod.snd
      (fun point => point.1 - radius)))
    (hstrict : ∃ point ∈ realTransportCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realTransportCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realTransportCostPayoffFrontier loss c nominal))
    (hfinite : Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) })
    (hsource_bounded : ∀ penalty, 0 ≤ penalty →
      BddAbove (Set.range fun candidate : { source : ProbabilityMeasure α //
        Nonempty (FiniteRealCostCoupling c source nominal) } =>
        (∫ x, loss x ∂(candidate.1 : Measure α)) -
          penalty * realTransportCost c candidate.1 nominal))
    (hpenalized_envelope : ∀ penalty, 0 ≤ penalty →
      realTransportCostPenalizedValue loss c penalty nominal =
        ∫ x, envelope penalty x ∂(nominal : Measure α)) :
    constrainedRealTransportValue loss c radius nominal =
      constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
  have hfixed : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
        (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
    intro penalty hpenalty
    calc
      Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) penalty =
          realTransportCostPenalizedValue loss c penalty nominal + penalty * radius :=
        scalarDualObjective_frontier_eq_realTransportCostPenalizedValue_add
          loss c penalty radius nominal hfinite
            (hsource_bounded penalty (Set.mem_Ici.mp hpenalty))
      _ = (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
        rw [hpenalized_envelope penalty (Set.mem_Ici.mp hpenalty)]
  calc
    constrainedRealTransportValue loss c radius nominal =
        Optimization.scalarDualValue (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) :=
      constrainedRealTransportValue_eq_scalarDualValue_of_convex_achievableSet
        loss c radius nominal hachievable_convex hstrict hprimal_bdd hdual_bdd
    _ = constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
      unfold Optimization.scalarDualValue constrainedRealTransportEnvelopeDualValue
      congr 1
      ext value
      constructor
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, (hfixed penalty hpenalty).symm⟩
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, hfixed penalty hpenalty⟩

/--
The source-compatible zero-multiplier version of constrained transport
duality.  Positive multipliers use the finite-real-cost transport domain, but
at multiplier zero the envelope may use the unrestricted expected-payoff
value.  The latter replacement does not change the infimum: for every
positive tolerance, a positive-multiplier finite-cost Lagrangian objective is
at most its zero-multiplier value plus that tolerance when the radius is
nonnegative.
-/
theorem constrainedRealTransportValue_eq_envelopeDualValue_of_convex_achievableSet_of_pos
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ)
    (hachievable_convex : Convex ℝ (Optimization.scalarAchievableSet
      (realTransportCostPayoffFrontier loss c nominal) Prod.snd
      (fun point => point.1 - radius)))
    (hstrict : ∃ point ∈ realTransportCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realTransportCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realTransportCostPayoffFrontier loss c nominal))
    (hfinite : Nonempty { source : ProbabilityMeasure α //
      Nonempty (FiniteRealCostCoupling c source nominal) })
    (hcost_nonneg : ∀ pair, 0 ≤ c pair)
    (hradius_nonneg : 0 ≤ radius)
    (hsource_bounded : ∀ penalty, 0 ≤ penalty →
      BddAbove (Set.range fun candidate : { source : ProbabilityMeasure α //
        Nonempty (FiniteRealCostCoupling c source nominal) } =>
        (∫ x, loss x ∂(candidate.1 : Measure α)) -
          penalty * realTransportCost c candidate.1 nominal))
    (hunpenalized_bdd : BddAbove (Set.range fun source : ProbabilityMeasure α =>
      ∫ x, loss x ∂(source : Measure α)))
    (hpenalized_envelope : ∀ penalty, 0 < penalty →
      realTransportCostPenalizedValue loss c penalty nominal =
        ∫ x, envelope penalty x ∂(nominal : Measure α))
    (hzero_envelope : unpenalizedValue loss =
      ∫ x, envelope 0 x ∂(nominal : Measure α)) :
    constrainedRealTransportValue loss c radius nominal =
      constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
  let fixedDual : ℝ → ℝ := fun penalty =>
    Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
      Prod.snd (fun point => point.1 - radius) penalty
  let envelopeDual : ℝ → ℝ := fun penalty =>
    (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius
  obtain ⟨strictPoint, hstrictPoint, hstrictCost⟩ := hstrict
  have hfrontier_ne : (realTransportCostPayoffFrontier loss c nominal).Nonempty := by
    obtain ⟨source⟩ := hfinite
    exact ⟨(realTransportCost c source.1 nominal,
      ∫ x, loss x ∂(source.1 : Measure α)), ⟨source, rfl⟩⟩
  have hfixed_lower : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      strictPoint.2 ≤ fixedDual penalty := by
    intro penalty hpenalty
    have hlagrangian : strictPoint.2 ≤ Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) strictPoint penalty := by
      unfold Optimization.scalarLagrangian
      have hmult : penalty * (strictPoint.1 - radius) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Set.mem_Ici.mp hpenalty)
          (sub_nonpos.mpr hstrictCost.le)
      linarith
    have hsup := Optimization.scalarLagrangian_le_scalarDualObjective
      (hdual_bdd penalty (Set.mem_Ici.mp hpenalty)) hstrictPoint
    exact hlagrangian.trans (by simpa [fixedDual] using hsup)
  have hfixed_bddBelow : BddBelow (fixedDual '' Set.Ici (0 : ℝ)) := by
    refine ⟨strictPoint.2, ?_⟩
    rintro value ⟨penalty, hpenalty, rfl⟩
    exact hfixed_lower penalty hpenalty
  have hfixed_ne : (fixedDual '' Set.Ici (0 : ℝ)).Nonempty :=
    ⟨fixedDual 0, 0, Set.mem_Ici.mpr le_rfl, rfl⟩
  have hfixed_pos : ∀ penalty, 0 < penalty → fixedDual penalty = envelopeDual penalty := by
    intro penalty hpenalty
    dsimp [fixedDual, envelopeDual]
    calc
      Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) penalty =
          realTransportCostPenalizedValue loss c penalty nominal + penalty * radius :=
        scalarDualObjective_frontier_eq_realTransportCostPenalizedValue_add
          loss c penalty radius nominal hfinite (hsource_bounded penalty hpenalty.le)
      _ = (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
        rw [hpenalized_envelope penalty hpenalty]
  have hzero_dominates : fixedDual 0 ≤ envelopeDual 0 := by
    dsimp [fixedDual, envelopeDual]
    calc
      Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) 0 =
          realTransportCostPenalizedValue loss c 0 nominal + 0 * radius :=
        scalarDualObjective_frontier_eq_realTransportCostPenalizedValue_add
          loss c 0 radius nominal hfinite (hsource_bounded 0 (by norm_num))
      _ = realTransportCostPenalizedValue loss c 0 nominal := by ring
      _ ≤ unpenalizedValue loss :=
        realTransportCostPenalizedValue_zero_le_unpenalizedValue
          loss c nominal hfinite hunpenalized_bdd
      _ = (∫ x, envelope 0 x ∂(nominal : Measure α)) + 0 * radius := by
        rw [hzero_envelope]
        ring
  have henvelope_lower : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      strictPoint.2 ≤ envelopeDual penalty := by
    intro penalty hpenalty
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty) with rfl | hpenalty_pos
    · exact (hfixed_lower 0 (Set.mem_Ici.mpr le_rfl)).trans hzero_dominates
    · rw [← hfixed_pos penalty hpenalty_pos]
      exact hfixed_lower penalty hpenalty
  have henvelope_bddBelow : BddBelow (envelopeDual '' Set.Ici (0 : ℝ)) := by
    refine ⟨strictPoint.2, ?_⟩
    rintro value ⟨penalty, hpenalty, rfl⟩
    exact henvelope_lower penalty hpenalty
  have henvelope_ne : (envelopeDual '' Set.Ici (0 : ℝ)).Nonempty :=
    ⟨envelopeDual 0, 0, Set.mem_Ici.mpr le_rfl, rfl⟩
  have hfixed_upper : ∀ penalty, 0 ≤ penalty →
      fixedDual penalty ≤ fixedDual 0 + penalty * radius := by
    intro penalty hpenalty
    dsimp [fixedDual]
    apply Optimization.scalarDualObjective_le hfrontier_ne
    intro point hpoint
    obtain ⟨source, rfl⟩ := hpoint
    have hcost : 0 ≤ realTransportCost c source.1 nominal :=
      realTransportCost_nonneg c source.1 nominal source.2 hcost_nonneg
    have hpayoff : (∫ x, loss x ∂(source.1 : Measure α)) ≤
        Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) 0 := by
      have hsup := Optimization.scalarLagrangian_le_scalarDualObjective
        (hdual_bdd 0 (by norm_num)) ⟨source, rfl⟩
      simpa [Optimization.scalarLagrangian] using hsup
    have hpenalized_cost : 0 ≤ penalty * realTransportCost c source.1 nominal :=
      mul_nonneg hpenalty hcost
    change (∫ x, loss x ∂(source.1 : Measure α)) -
        penalty * (realTransportCost c source.1 nominal - radius) ≤
      Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) 0 + penalty * radius
    calc
      (∫ x, loss x ∂(source.1 : Measure α)) -
          penalty * (realTransportCost c source.1 nominal - radius) =
          ((∫ x, loss x ∂(source.1 : Measure α)) -
            penalty * realTransportCost c source.1 nominal) + penalty * radius := by ring
      _ ≤ Optimization.scalarDualObjective (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) 0 + penalty * radius := by
        linarith
  have hfixed_approaches_zero : ∀ epsilon, 0 < epsilon →
      ∃ penalty, 0 < penalty ∧ fixedDual penalty < fixedDual 0 + epsilon := by
    intro epsilon hepsilon
    let penalty : ℝ := epsilon / (radius + 1)
    have hdenom_pos : 0 < radius + 1 := by linarith
    have hpenalty_pos : 0 < penalty := div_pos hepsilon hdenom_pos
    refine ⟨penalty, hpenalty_pos, ?_⟩
    have hpenalty_radius : penalty * radius < epsilon := by
      dsimp [penalty]
      calc
        epsilon / (radius + 1) * radius = epsilon * (radius / (radius + 1)) := by
          field_simp
        _ < epsilon * 1 := by
          gcongr
          exact (div_lt_one₀ hdenom_pos).mpr (by linarith)
        _ = epsilon := by ring
    exact (hfixed_upper penalty hpenalty_pos.le).trans_lt (by linarith)
  have hsInf_eq : sInf (fixedDual '' Set.Ici (0 : ℝ)) =
      sInf (envelopeDual '' Set.Ici (0 : ℝ)) := by
    apply le_antisymm
    · apply le_csInf henvelope_ne
      rintro value ⟨penalty, hpenalty, rfl⟩
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty) with rfl | hpenalty_pos
      · exact (csInf_le hfixed_bddBelow ⟨0, Set.mem_Ici.mpr le_rfl, rfl⟩).trans
          hzero_dominates
      · calc
          sInf (fixedDual '' Set.Ici (0 : ℝ)) ≤ fixedDual penalty :=
            csInf_le hfixed_bddBelow ⟨penalty, hpenalty, rfl⟩
          _ = envelopeDual penalty := hfixed_pos penalty hpenalty_pos
    · apply le_csInf hfixed_ne
      rintro value ⟨penalty, hpenalty, rfl⟩
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty) with rfl | hpenalty_pos
      · apply le_of_forall_pos_le_add
        intro epsilon hepsilon
        obtain ⟨positivePenalty, hpositivePenalty, hnear⟩ :=
          hfixed_approaches_zero epsilon hepsilon
        calc
          sInf (envelopeDual '' Set.Ici (0 : ℝ)) ≤ envelopeDual positivePenalty :=
            csInf_le henvelope_bddBelow ⟨positivePenalty, hpositivePenalty.le, rfl⟩
          _ = fixedDual positivePenalty := (hfixed_pos positivePenalty hpositivePenalty).symm
          _ ≤ fixedDual 0 + epsilon := hnear.le
      · calc
          sInf (envelopeDual '' Set.Ici (0 : ℝ)) ≤ envelopeDual penalty :=
            csInf_le henvelope_bddBelow ⟨penalty, hpenalty, rfl⟩
          _ = fixedDual penalty := (hfixed_pos penalty hpenalty_pos).symm
  calc
    constrainedRealTransportValue loss c radius nominal =
        Optimization.scalarDualValue (realTransportCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) :=
      constrainedRealTransportValue_eq_scalarDualValue_of_convex_achievableSet
        loss c radius nominal hachievable_convex
          ⟨strictPoint, hstrictPoint, hstrictCost⟩ hprimal_bdd hdual_bdd
    _ = constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
      simpa [Optimization.scalarDualValue, constrainedRealTransportEnvelopeDualValue,
        fixedDual, envelopeDual] using hsInf_eq

/--
The coupling-level constrained transport value equals its pointwise-envelope
dual once the concrete coupling frontier has compact convex geometry and the
fixed-penalty envelope identities have been established.  This is the
source-faithful constrained-duality route for models whose transport plans
(rather than their already-minimized costs) form the convex primal domain.
-/
theorem constrainedRealCouplingValue_eq_envelopeDualValue_of_compact_convex_frontier
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ)
    (hfrontier_compact : IsCompact (realCouplingCostPayoffFrontier loss c nominal))
    (hfrontier_convex : Convex ℝ (realCouplingCostPayoffFrontier loss c nominal))
    (hstrict : ∃ point ∈ realCouplingCostPayoffFrontier loss c nominal, point.1 < radius)
    (hfinite : Nonempty (FiniteRealCostCouplingTo c nominal))
    (hcoupling_bounded : ∀ penalty, 0 ≤ penalty →
      BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × α))))
    (hpenalized_envelope : ∀ penalty, 0 < penalty →
      penalizedCouplingValue loss c penalty nominal =
        ∫ x, envelope penalty x ∂(nominal : Measure α))
    (hzero_envelope : penalizedCouplingValue loss c 0 nominal =
      ∫ x, envelope 0 x ∂(nominal : Measure α)) :
    constrainedRealCouplingValue loss c radius nominal =
      constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
  have hfixed : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
        (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
    intro penalty hpenalty_nonneg
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty_nonneg) with rfl | hpenalty_pos
    · calc
        Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) 0 =
            penalizedCouplingValue loss c 0 nominal + 0 * radius :=
          scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
            loss c 0 radius nominal hfinite (hcoupling_bounded 0 le_rfl)
        _ = (∫ x, envelope 0 x ∂(nominal : Measure α)) + 0 * radius := by
          rw [hzero_envelope]
    · calc
        Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) penalty =
            penalizedCouplingValue loss c penalty nominal + penalty * radius :=
          scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
            loss c penalty radius nominal hfinite (hcoupling_bounded penalty hpenalty_pos.le)
        _ = (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
          rw [hpenalized_envelope penalty hpenalty_pos]
  calc
    constrainedRealCouplingValue loss c radius nominal =
        Optimization.scalarDualValue (realCouplingCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) :=
      constrainedRealCouplingValue_eq_scalarDualValue_of_compact_convex_frontier
        loss c radius nominal hfrontier_compact hfrontier_convex hstrict
    _ = constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
      unfold Optimization.scalarDualValue constrainedRealTransportEnvelopeDualValue
      congr 1
      ext value
      constructor
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, (hfixed penalty hpenalty).symm⟩
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, hfixed penalty hpenalty⟩

/--
The coupling-level transport value equals its pointwise-envelope dual from
convexity, strict feasibility, and real boundedness.  This is the noncompact
counterpart of the preceding compact-frontier theorem and does not require
closedness of the attainable frontier hypograph.
-/
theorem constrainedRealCouplingValue_eq_envelopeDualValue_of_bdd
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ)
    (hfrontier_convex : Convex ℝ (realCouplingCostPayoffFrontier loss c nominal))
    (hstrict : ∃ point ∈ realCouplingCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realCouplingCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realCouplingCostPayoffFrontier loss c nominal))
    (hfinite : Nonempty (FiniteRealCostCouplingTo c nominal))
    (hcoupling_bounded : ∀ penalty, 0 ≤ penalty →
      BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × α))))
    (hpenalized_envelope : ∀ penalty, 0 < penalty →
      penalizedCouplingValue loss c penalty nominal =
        ∫ x, envelope penalty x ∂(nominal : Measure α))
    (hzero_envelope : penalizedCouplingValue loss c 0 nominal =
      ∫ x, envelope 0 x ∂(nominal : Measure α)) :
    constrainedRealCouplingValue loss c radius nominal =
      constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
  have hfixed : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
        (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
    intro penalty hpenalty_nonneg
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty_nonneg) with rfl | hpenalty_pos
    · calc
        Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) 0 =
            penalizedCouplingValue loss c 0 nominal + 0 * radius :=
          scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
            loss c 0 radius nominal hfinite (hcoupling_bounded 0 le_rfl)
        _ = (∫ x, envelope 0 x ∂(nominal : Measure α)) + 0 * radius := by
          rw [hzero_envelope]
    · calc
        Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) penalty =
            penalizedCouplingValue loss c penalty nominal + penalty * radius :=
          scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
            loss c penalty radius nominal hfinite (hcoupling_bounded penalty hpenalty_pos.le)
        _ = (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
          rw [hpenalized_envelope penalty hpenalty_pos]
  calc
    constrainedRealCouplingValue loss c radius nominal =
        Optimization.scalarDualValue (realCouplingCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) :=
      constrainedRealCouplingValue_eq_scalarDualValue_of_bdd
        loss c radius nominal hfrontier_convex hstrict hprimal_bdd hdual_bdd
    _ = constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
      unfold Optimization.scalarDualValue constrainedRealTransportEnvelopeDualValue
      congr 1
      ext value
      constructor
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, (hfixed penalty hpenalty).symm⟩
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, hfixed penalty hpenalty⟩

/--
The coupling-level transport value equals its pointwise-envelope dual under a
closed attainable cost--payoff hypograph.  This generalizes the preceding
compact-frontier theorem to noncompact transport-law domains.  Fixed-penalty
envelope identities and their real boundedness remain explicit, so this does
not hide a measurable-selection or extended-value convention.
-/
theorem constrainedRealCouplingValue_eq_envelopeDualValue_of_closed_achievable
    (loss : α → ℝ) (c : α × α → ℝ) (radius : ℝ)
    (nominal : ProbabilityMeasure α) (envelope : ℝ → α → ℝ)
    (hfrontier_convex : Convex ℝ (realCouplingCostPayoffFrontier loss c nominal))
    (hstrict : ∃ point ∈ realCouplingCostPayoffFrontier loss c nominal, point.1 < radius)
    (hprimal_bdd : BddAbove (Prod.snd '' Optimization.scalarFeasible
      (realCouplingCostPayoffFrontier loss c nominal) (fun point => point.1 - radius)))
    (hdual_bdd : ∀ penalty, 0 ≤ penalty →
      BddAbove ((fun point => Optimization.scalarLagrangian Prod.snd
        (fun point => point.1 - radius) point penalty) ''
          realCouplingCostPayoffFrontier loss c nominal))
    (hachievable_closed : IsClosed (Optimization.scalarAchievableSet
      (realCouplingCostPayoffFrontier loss c nominal) Prod.snd
      (fun point => point.1 - radius)))
    (hfinite : Nonempty (FiniteRealCostCouplingTo c nominal))
    (hcoupling_bounded : ∀ penalty, 0 ≤ penalty →
      BddAbove (Set.range fun candidate : FiniteRealCostCouplingTo c nominal =>
        (∫ x, loss x ∂(candidate.source : Measure α)) -
          penalty * ∫ pair, c pair ∂(candidate.coupling.joint : Measure (α × α))))
    (hpenalized_envelope : ∀ penalty, 0 < penalty →
      penalizedCouplingValue loss c penalty nominal =
        ∫ x, envelope penalty x ∂(nominal : Measure α))
    (hzero_envelope : penalizedCouplingValue loss c 0 nominal =
      ∫ x, envelope 0 x ∂(nominal : Measure α)) :
    constrainedRealCouplingValue loss c radius nominal =
      constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
  have hfixed : ∀ penalty, penalty ∈ Set.Ici (0 : ℝ) →
      Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
        Prod.snd (fun point => point.1 - radius) penalty =
        (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
    intro penalty hpenalty_nonneg
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hpenalty_nonneg) with rfl | hpenalty_pos
    · calc
        Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) 0 =
            penalizedCouplingValue loss c 0 nominal + 0 * radius :=
          scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
            loss c 0 radius nominal hfinite (hcoupling_bounded 0 le_rfl)
        _ = (∫ x, envelope 0 x ∂(nominal : Measure α)) + 0 * radius := by
          rw [hzero_envelope]
    · calc
        Optimization.scalarDualObjective (realCouplingCostPayoffFrontier loss c nominal)
            Prod.snd (fun point => point.1 - radius) penalty =
            penalizedCouplingValue loss c penalty nominal + penalty * radius :=
          scalarDualObjective_couplingFrontier_eq_penalizedCouplingValue_add
            loss c penalty radius nominal hfinite (hcoupling_bounded penalty hpenalty_pos.le)
        _ = (∫ x, envelope penalty x ∂(nominal : Measure α)) + penalty * radius := by
          rw [hpenalized_envelope penalty hpenalty_pos]
  calc
    constrainedRealCouplingValue loss c radius nominal =
        Optimization.scalarDualValue (realCouplingCostPayoffFrontier loss c nominal)
          Prod.snd (fun point => point.1 - radius) :=
      constrainedRealCouplingValue_eq_scalarDualValue_of_closed_achievable
        loss c radius nominal hfrontier_convex hstrict hprimal_bdd hdual_bdd
          hachievable_closed
    _ = constrainedRealTransportEnvelopeDualValue loss c radius nominal envelope := by
      unfold Optimization.scalarDualValue constrainedRealTransportEnvelopeDualValue
      congr 1
      ext value
      constructor
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, (hfixed penalty hpenalty).symm⟩
      · rintro ⟨penalty, hpenalty, rfl⟩
        exact ⟨penalty, hpenalty, hfixed penalty hpenalty⟩

/--
A pointwise transport domination bounds the expectation under the first
marginal by the expectation under the second marginal plus coupling cost.
-/
theorem lintegral_fst_le_lintegral_snd_add_cost
    (π : ProbabilityCoupling μ ν) {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
    {c : α × β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hdom : ∀ z : α × β, f z.1 ≤ g z.2 + c z) :
    (∫⁻ x, f x ∂(μ : Measure α)) ≤
      (∫⁻ y, g y ∂(ν : Measure β)) + π.cost c := by
  calc
    (∫⁻ x, f x ∂(μ : Measure α)) =
        ∫⁻ z, f z.1 ∂(π.joint : Measure (α × β)) := π.lintegral_fst hf
    _ ≤ ∫⁻ z, g z.2 + c z ∂(π.joint : Measure (α × β)) :=
      lintegral_mono hdom
    _ = (∫⁻ z, g z.2 ∂(π.joint : Measure (α × β))) + π.cost c := by
      change (∫⁻ z, (g ∘ Prod.snd) z + c z ∂(π.joint : Measure (α × β))) = _
      rw [lintegral_add_left (hg.comp measurable_snd) c]
      rfl
    _ = (∫⁻ y, g y ∂(ν : Measure β)) + π.cost c := by
      rw [← π.lintegral_snd hg]

/--
The infimum expected cost over all couplings.  This is the general
transport-cost primitive; specializing `c` to a metric cost gives W₁.
-/
noncomputable def transportCost (c : α × β → ℝ≥0∞)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : ℝ≥0∞ :=
  sInf (Set.range fun π : ProbabilityCoupling μ ν => π.cost c)

/-- Every particular coupling bounds the infimum transport cost from above. -/
theorem transportCost_le_cost (c : α × β → ℝ≥0∞)
    (π : ProbabilityCoupling μ ν) :
    transportCost c μ ν ≤ π.cost c := by
  apply sInf_le
  exact ⟨π, rfl⟩

/-- The extended-real 1-Wasserstein transport cost on a metric measurable space. -/
noncomputable def wassersteinOne {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : ProbabilityMeasure α) : ℝ≥0∞ :=
  transportCost (fun z : α × α => edist z.1 z.2) μ ν

/-- Every coupling bounds the extended-real 1-Wasserstein cost by its expected distance. -/
theorem wassersteinOne_le_cost {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    {μ ν : ProbabilityMeasure α} (π : ProbabilityCoupling μ ν) :
    wassersteinOne μ ν ≤ π.cost (fun z : α × α => edist z.1 z.2) :=
  transportCost_le_cost _ π

/--
The cost of the graph coupling is the expected pointwise transport cost.
This turns a measurable clipping or shell map into a quantitative W₁ bound.
-/
theorem graph_cost_eq (μ : ProbabilityMeasure α) (T : α → α)
    (hT : Measurable T) (c : α × α → ℝ≥0∞) (hc : Measurable c) :
    (graph μ T hT).cost c = ∫⁻ x, c (x, T x) ∂(μ : Measure α) := by
  unfold ProbabilityCoupling.cost graph
  change ∫⁻ z, c z ∂Measure.map (fun x : α => (x, T x)) (μ : Measure α) = _
  have hgraph : Measurable (fun x : α => (x, T x)) := measurable_id.prodMk hT
  rw [lintegral_map hc hgraph]

/--
Wasserstein-1 from a law to a measurable pushforward is bounded by the expected
distance moved by the map.  This is the reusable noncompact-to-compact bridge
for the Fournier--Guillin truncation/shell stage.
-/
theorem wassersteinOne_le_lintegral_edist_map
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (μ : ProbabilityMeasure α) (T : α → α) (hT : Measurable T) :
    wassersteinOne μ (μ.map hT.aemeasurable) ≤
      ∫⁻ x, edist x (T x) ∂(μ : Measure α) := by
  calc
    wassersteinOne μ (μ.map hT.aemeasurable) ≤
        (graph μ T hT).cost (fun z : α × α => edist z.1 z.2) :=
      wassersteinOne_le_cost (graph μ T hT)
    _ = ∫⁻ x, edist x (T x) ∂(μ : Measure α) :=
      graph_cost_eq μ T hT (fun z : α × α => edist z.1 z.2) measurable_edist

/--
Push a local probability coupling through a pair of measurable maps.  This is
the primal coupling counterpart of a pushforward operation: it preserves the
two prescribed marginals exactly.
-/
noncomputable def map
    {α β α' β' : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β']
    {μ : ProbabilityMeasure α} {ν : ProbabilityMeasure β}
    (π : ProbabilityCoupling μ ν)
    (F : α → α') (G : β → β') (hF : Measurable F) (hG : Measurable G) :
    ProbabilityCoupling (μ.map hF.aemeasurable) (ν.map hG.aemeasurable) where
  joint := π.joint.map (hF.prodMap hG).aemeasurable
  map_fst := by
    apply Subtype.ext
    change Measure.map Prod.fst (Measure.map (Prod.map F G) (π.joint : Measure (α × β))) =
      Measure.map F (μ : Measure α)
    rw [Measure.map_map measurable_fst (hF.prodMap hG)]
    change Measure.map (Prod.fst ∘ Prod.map F G) (π.joint : Measure (α × β)) = _
    rw [show Prod.fst ∘ Prod.map F G = F ∘ Prod.fst by rfl,
      ← Measure.map_map hF measurable_fst]
    exact congrArg (Measure.map F) (congrArg ProbabilityMeasure.toMeasure π.map_fst)
  map_snd := by
    apply Subtype.ext
    change Measure.map Prod.snd (Measure.map (Prod.map F G) (π.joint : Measure (α × β))) =
      Measure.map G (ν : Measure β)
    rw [Measure.map_map measurable_snd (hF.prodMap hG)]
    change Measure.map (Prod.snd ∘ Prod.map F G) (π.joint : Measure (α × β)) = _
    rw [show Prod.snd ∘ Prod.map F G = G ∘ Prod.snd by rfl,
      ← Measure.map_map hG measurable_snd]
    exact congrArg (Measure.map G) (congrArg ProbabilityMeasure.toMeasure π.map_snd)

/-- The pushed coupling's cost is the source coupling's pushed pointwise cost. -/
theorem map_cost_eq
    {α β α' β' : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β']
    {μ : ProbabilityMeasure α} {ν : ProbabilityMeasure β}
    (π : ProbabilityCoupling μ ν)
    (F : α → α') (G : β → β') (hF : Measurable F) (hG : Measurable G)
    (c : α' × β' → ℝ≥0∞) (hc : Measurable c) :
    (π.map F G hF hG).cost c =
      ∫⁻ z, c (F z.1, G z.2) ∂(π.joint : Measure (α × β)) := by
  unfold ProbabilityCoupling.cost map
  change ∫⁻ z, c z ∂Measure.map (Prod.map F G) (π.joint : Measure (α × β)) = _
  rw [lintegral_map hc (hF.prodMap hG)]
  rfl

/--
A measurable `L`-Lipschitz map contracts the local primal Wasserstein-1 cost
by the factor `L`.  This permits a compact empirical-W₁ theorem to be scaled
back to a Euclidean truncation without appealing to a new optimal-transport
duality theorem.

The finite factor commutes with the infimum by Mathlib's `ENNReal.mul_iInf`;
the proof also uses `lintegral_const_mul` from
[`MeasureTheory/Integral/Lebesgue/Add.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean)
at the pinned Apache-2.0 Mathlib commit. No source text is copied or ported.
-/
theorem wassersteinOne_map_le_of_lipschitz
    {E F : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [MeasurableSpace F] [PseudoMetricSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (T : E → F) (L : NNReal) (hL : LipschitzWith L T) (hT : Measurable T)
    (μ ν : ProbabilityMeasure E) :
    wassersteinOne (μ.map hT.aemeasurable) (ν.map hT.aemeasurable) ≤
      (L : ℝ≥0∞) * wassersteinOne μ ν := by
  letI : Nonempty (ProbabilityCoupling μ ν) := ⟨independent μ ν⟩
  unfold wassersteinOne transportCost
  rw [sInf_range, sInf_range,
    ENNReal.mul_iInf (a := (L : ℝ≥0∞)) (f := fun π : ProbabilityCoupling μ ν =>
      π.cost (fun z : E × E => edist z.1 z.2)) (by simp)]
  refine le_iInf fun π => ?_
  calc
    (⨅ π : ProbabilityCoupling (μ.map hT.aemeasurable) (ν.map hT.aemeasurable),
        π.cost (fun z : F × F => edist z.1 z.2)) ≤
        (π.map T T hT hT).cost (fun z : F × F => edist z.1 z.2) :=
      iInf_le _ (π.map T T hT hT)
    _ = ∫⁻ z, edist (T z.1) (T z.2) ∂(π.joint : Measure (E × E)) :=
      map_cost_eq π T T hT hT (fun z : F × F => edist z.1 z.2) measurable_edist
    _ ≤ ∫⁻ z, (L : ℝ≥0∞) * edist z.1 z.2 ∂(π.joint : Measure (E × E)) := by
      apply lintegral_mono
      intro z
      change edist (T z.1) (T z.2) ≤ (L : ℝ≥0∞) * edist z.1 z.2
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
      exact ENNReal.ofReal_le_ofReal (hL.dist_le_mul z.1 z.2)
    _ = (L : ℝ≥0∞) * ∫⁻ z, edist z.1 z.2 ∂(π.joint : Measure (E × E)) := by
      rw [lintegral_const_mul _ measurable_edist]

/-- The set of finite real expected-distance costs of couplings of two laws. -/
noncomputable def expectedDistanceCosts {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : ProbabilityMeasure α) : Set ℝ :=
  {r | ∃ π : ProbabilityCoupling μ ν,
    ∃ _ : Integrable (fun z : α × α => dist z.1 z.2) (π.joint : Measure (α × α)),
      r = ∫ z, dist z.1 z.2 ∂(π.joint : Measure (α × α))}

/--
The real-valued 1-Wasserstein distance, defined when at least one coupling has
finite expected distance.  The nonemptiness argument records the required
first-moment hypothesis instead of giving an empty infimum a spurious meaning.
-/
noncomputable def wassersteinOneReal {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : ProbabilityMeasure α) (_ : (expectedDistanceCosts μ ν).Nonempty) : ℝ :=
  sInf (expectedDistanceCosts μ ν)

/--
Every finite expected-distance coupling bounds real W₁ from above.  The
nonnegativity of metric distance supplies the lower-bound condition needed for
the real infimum.
-/
theorem wassersteinOneReal_le_expectedDistance
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    {μ ν : ProbabilityMeasure α}
    (hfinite : (expectedDistanceCosts μ ν).Nonempty) (π : ProbabilityCoupling μ ν)
    (hdist : Integrable (fun z : α × α => dist z.1 z.2) (π.joint : Measure (α × α))) :
    wassersteinOneReal μ ν hfinite ≤
      ∫ z, dist z.1 z.2 ∂(π.joint : Measure (α × α)) := by
  unfold wassersteinOneReal
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro cost ⟨coupling, hcost_integrable, rfl⟩
    exact integral_nonneg fun _ => dist_nonneg
  · exact ⟨π, hdist, rfl⟩

/--
Two Dirac laws always have a finite expected-distance coupling.  This is the
common first-moment witness for deterministic-response models, including the
point-mass constructions used in performative-prediction counterexamples.
-/
theorem expectedDistanceCosts_dirac_nonempty
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [PseudoMetricSpace α]
    (first second : α) :
    (expectedDistanceCosts (diracProba first) (diracProba second)).Nonempty := by
  let coupling : ProbabilityCoupling (diracProba first) (diracProba second) :=
    ProbabilityCoupling.dirac first second
  refine ⟨dist first second, coupling, ?_, ?_⟩
  · change Integrable (fun z : α × α => dist z.1 z.2)
      (Measure.dirac (first, second))
    exact integrable_dirac (by finiteness)
  · change dist first second =
      (∫ z : α × α, dist z.1 z.2 ∂Measure.dirac (first, second))
    rw [integral_dirac]

/--
Two probability laws on a normed space have a finite real W₁ witness whenever
both have integrable first moments.  The witness is their independent product
coupling; it is intentionally an existence statement rather than an optimal
transport assertion.
-/
theorem expectedDistanceCosts_nonempty_of_integrable_norm
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    (μ ν : ProbabilityMeasure E)
    (hμ : Integrable (fun x : E => ‖x‖) (μ : Measure E))
    (hν : Integrable (fun x : E => ‖x‖) (ν : Measure E)) :
    (expectedDistanceCosts μ ν).Nonempty := by
  let π : ProbabilityCoupling μ ν := independent μ ν
  refine ⟨∫ z, dist z.1 z.2 ∂(π.joint : Measure (E × E)), π, ?_, rfl⟩
  simpa [π] using integrable_dist_independent μ ν hμ hν

/--
The real W₁ cost of two Dirac laws is bounded by the distance between their
atoms.  The result accepts any finite-cost witness because the real W₁
definition records that witness explicitly.
-/
theorem wassersteinOneReal_dirac_le_dist
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [PseudoMetricSpace α]
    (first second : α)
    (hfinite : (expectedDistanceCosts (diracProba first) (diracProba second)).Nonempty) :
    wassersteinOneReal (diracProba first) (diracProba second) hfinite ≤ dist first second := by
  let coupling : ProbabilityCoupling (diracProba first) (diracProba second) :=
    ProbabilityCoupling.dirac first second
  have hdist : Integrable (fun z : α × α => dist z.1 z.2)
      (coupling.joint : Measure (α × α)) := by
    change Integrable (fun z : α × α => dist z.1 z.2)
      (Measure.dirac (first, second))
    exact integrable_dirac (by finiteness)
  calc
    wassersteinOneReal (diracProba first) (diracProba second) hfinite ≤
        ∫ z, dist z.1 z.2 ∂(coupling.joint : Measure (α × α)) :=
      wassersteinOneReal_le_expectedDistance hfinite coupling hdist
    _ = dist first second := by
      change (∫ z : α × α, dist z.1 z.2 ∂Measure.dirac (first, second)) = _
      rw [integral_dirac]

/--
An integrable vector-valued Lipschitz test function changes by at most its
Lipschitz constant times the expected distance under any coupling.
-/
theorem norm_integral_sub_le_lipschitz_expectedDist
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    {μ ν : ProbabilityMeasure α} (π : ProbabilityCoupling μ ν)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : α → V} {L : NNReal} (hL : LipschitzWith L f)
    (hμ : Integrable f (μ : Measure α)) (hν : Integrable f (ν : Measure α))
    (hdist : Integrable (fun z : α × α => dist z.1 z.2) (π.joint : Measure (α × α))) :
    ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
      (L : ℝ) * ∫ z, dist z.1 z.2 ∂(π.joint : Measure (α × α)) := by
  have hmap_fst : Measure.map Prod.fst (π.joint : Measure (α × α)) = (μ : Measure α) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_fst
  have hmap_snd : Measure.map Prod.snd (π.joint : Measure (α × α)) = (ν : Measure α) := by
    exact congrArg ProbabilityMeasure.toMeasure π.map_snd
  have hμ_map : Integrable f (Measure.map Prod.fst (π.joint : Measure (α × α))) := by
    simpa only [hmap_fst] using hμ
  have hν_map : Integrable f (Measure.map Prod.snd (π.joint : Measure (α × α))) := by
    simpa only [hmap_snd] using hν
  have hfst : Integrable (fun z : α × α => f z.1) (π.joint : Measure (α × α)) := by
    simpa only [Function.comp_apply] using hμ_map.comp_measurable measurable_fst
  have hsnd : Integrable (fun z : α × α => f z.2) (π.joint : Measure (α × α)) := by
    simpa only [Function.comp_apply] using hν_map.comp_measurable measurable_snd
  have hscaled : Integrable (fun z : α × α => (L : ℝ) * dist z.1 z.2)
      (π.joint : Measure (α × α)) := hdist.const_mul (L : ℝ)
  have hpointwise : ∀ z : α × α, ‖f z.1 - f z.2‖ ≤ (L : ℝ) * dist z.1 z.2 := by
    intro z
    simpa only [dist_eq_norm] using hL.dist_le_mul z.1 z.2
  calc
    ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ =
        ‖(∫ z, f z.1 ∂(π.joint : Measure (α × α))) -
          ∫ z, f z.2 ∂(π.joint : Measure (α × α))‖ := by
      rw [← π.integral_fst hμ.aestronglyMeasurable, ← π.integral_snd hν.aestronglyMeasurable]
    _ = ‖∫ z, f z.1 - f z.2 ∂(π.joint : Measure (α × α))‖ := by
      rw [integral_sub hfst hsnd]
    _ ≤ ∫ z, ‖f z.1 - f z.2‖ ∂(π.joint : Measure (α × α)) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (L : ℝ) * dist z.1 z.2 ∂(π.joint : Measure (α × α)) :=
      integral_mono (hfst.sub hsnd).norm hscaled hpointwise
    _ = (L : ℝ) * ∫ z, dist z.1 z.2 ∂(π.joint : Measure (α × α)) := by
      rw [integral_const_mul]

/-- The scalar specialization of `norm_integral_sub_le_lipschitz_expectedDist`. -/
theorem abs_integral_sub_le_lipschitz_expectedDist
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    {μ ν : ProbabilityMeasure α} (π : ProbabilityCoupling μ ν)
    {f : α → ℝ} {L : NNReal} (hL : LipschitzWith L f)
    (hμ : Integrable f (μ : Measure α)) (hν : Integrable f (ν : Measure α))
    (hdist : Integrable (fun z : α × α => dist z.1 z.2) (π.joint : Measure (α × α))) :
    |(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)| ≤
      (L : ℝ) * ∫ z, dist z.1 z.2 ∂(π.joint : Measure (α × α)) := by
  simpa only [Real.norm_eq_abs] using
    π.norm_integral_sub_le_lipschitz_expectedDist hL hμ hν hdist

/--
A coupling whose extended-distance cost is finite has an integrable real
distance.  This is the conversion needed to apply Bochner integral estimates
inside an extended-real transport infimum.
-/
theorem integrable_dist_of_cost_ne_top
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α]
    {μ ν : ProbabilityMeasure α} (π : ProbabilityCoupling μ ν)
    (hcost : π.cost (fun z : α × α => edist z.1 z.2) ≠ ∞) :
    Integrable (fun z : α × α => dist z.1 z.2) (π.joint : Measure (α × α)) := by
  refine ⟨(measurable_fst.dist measurable_snd).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg, edist_dist,
    ProbabilityCoupling.cost, lt_top_iff_ne_top] using hcost

/--
The extended-real primal W₁ cost controls the discrepancy of integrals of an
integrable Lipschitz vector-valued test function.  The strictly positive
Lipschitz factor is explicit so that an infinite coupling cost is a trivial
case; the zero-factor specialization is left to applications that choose a
constant test function.

The finite/infinite-cost split follows the mathematical route of the easy
primal direction in
[`Vlasov.wasserstein1_le_wasserstein1_coupling`](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization/blob/b2eda09e58ceebad6cf23b8a7a6839001d4e7c15/Vlasov/Vlasov/OT/Coupling.lean)
from the Apache-2.0 project
[Hydrodynamical/Vlasov_Meanfield_Formalization](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization/tree/b2eda09e58ceebad6cf23b8a7a6839001d4e7c15),
but is written independently for this local `ProbabilityCoupling` interface
and vector-valued test functions; no upstream source is copied or ported.
It uses Mathlib's `ENNReal.mul_iInf`, `hasFiniteIntegral_iff_enorm`, and
`ofReal_integral_eq_lintegral_ofReal`, at pinned Apache-2.0 Mathlib commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
-/
theorem ofReal_norm_integral_sub_le_lipschitz_wassersteinOne
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α]
    {μ ν : ProbabilityMeasure α} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : α → V} {L : NNReal} (hL : LipschitzWith L f) (hLpos : L ≠ 0)
    (hμ : Integrable f (μ : Measure α)) (hν : Integrable f (ν : Measure α)) :
    ENNReal.ofReal ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
      (L : ℝ≥0∞) * wassersteinOne μ ν := by
  letI : Nonempty (ProbabilityCoupling μ ν) := ⟨independent μ ν⟩
  unfold wassersteinOne transportCost
  rw [sInf_range, ENNReal.mul_iInf (a := (L : ℝ≥0∞))
    (f := fun π : ProbabilityCoupling μ ν => π.cost (fun z : α × α => edist z.1 z.2))
    (by simp)]
  refine le_iInf fun π => ?_
  by_cases htop : π.cost (fun z : α × α => edist z.1 z.2) = ∞
  · rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.mpr hLpos)]
    exact le_top
  have hdist := integrable_dist_of_cost_ne_top π htop
  have hbound := π.norm_integral_sub_le_lipschitz_expectedDist hL hμ hν hdist
  calc
    ENNReal.ofReal ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
        ENNReal.ofReal ((L : ℝ) * ∫ z, dist z.1 z.2 ∂(π.joint : Measure (α × α))) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = (L : ℝ≥0∞) * π.cost (fun z : α × α => edist z.1 z.2) := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
      rw [ENNReal.ofReal_coe_nnreal]
      congr 1
      symm
      simpa only [ProbabilityCoupling.cost, edist_dist] using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdist
          (Filter.Eventually.of_forall fun _ => dist_nonneg)).symm

/--
The coupling-level Lipschitz estimate descends to the infimum over all
finite-expected-distance couplings.  This is the primal W₁ test-function
direction, stated with explicit finiteness rather than silently interpreting
an infinite transport cost as a real number.
-/
theorem norm_integral_sub_le_lipschitz_sInf_expectedDistance
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    {μ ν : ProbabilityMeasure α} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : α → V} {L : NNReal} (hL : LipschitzWith L f)
    (hμ : Integrable f (μ : Measure α)) (hν : Integrable f (ν : Measure α))
    (hfinite : (expectedDistanceCosts μ ν).Nonempty) :
    ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
      (L : ℝ) * sInf (expectedDistanceCosts μ ν) := by
  have hscaled_nonempty : ((L : ℝ) • expectedDistanceCosts μ ν).Nonempty := by
    rcases hfinite with ⟨r, hr⟩
    exact ⟨(L : ℝ) • r, Set.smul_mem_smul_set hr⟩
  change ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
    (L : ℝ) • sInf (expectedDistanceCosts μ ν)
  rw [← Real.sInf_smul_of_nonneg (NNReal.coe_nonneg L) (expectedDistanceCosts μ ν)]
  refine le_csInf hscaled_nonempty ?_
  intro r hr
  rcases hr with ⟨cost, hcost, rfl⟩
  rcases hcost with ⟨π, hdist, hcost_eq⟩
  change ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
    (L : ℝ) * cost
  rw [hcost_eq]
  exact π.norm_integral_sub_le_lipschitz_expectedDist hL hμ hν hdist

/-- The Lipschitz-test bound in terms of the finite real 1-Wasserstein distance. -/
theorem norm_integral_sub_le_lipschitz_wassersteinOneReal
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    {μ ν : ProbabilityMeasure α} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : α → V} {L : NNReal} (hL : LipschitzWith L f)
    (hμ : Integrable f (μ : Measure α)) (hν : Integrable f (ν : Measure α))
    (hfinite : (expectedDistanceCosts μ ν).Nonempty) :
    ‖(∫ x, f x ∂(μ : Measure α)) - ∫ y, f y ∂(ν : Measure α)‖ ≤
      (L : ℝ) * wassersteinOneReal μ ν hfinite :=
  norm_integral_sub_le_lipschitz_sInf_expectedDistance hL hμ hν hfinite

end ProbabilityCoupling

end AppliedModelingLib
