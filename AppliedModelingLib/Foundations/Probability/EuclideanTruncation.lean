import AppliedModelingLib.Foundations.Probability.EuclideanDyadicPartition

/-!
# Euclidean truncation and compact scaling

This module gives the concrete collapse-and-scale maps used to reduce an
unbounded Euclidean empirical-Wasserstein problem to the half-open dyadic cube
`(-1, 1]^d`. Points outside the radius-`R` Euclidean ball are collapsed to
zero, retained points are divided by `2R`, and the inverse scaling map has
Lipschitz constant `2R`.

The construction is the compact reduction needed before the outer-shell/tail
argument in Fournier--Guillin (2015), Theorem 2, can invoke the reusable
dyadic concentration bound. It does not itself bound the truncation error.

## Library provenance

The coordinate estimate uses Mathlib's `PiLp.norm_apply_le` and
`PiLp.smul_apply` from
[`Analysis/Normed/Lp/PiLp.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Normed/Lp/PiLp.lean),
and the inverse-map proof uses `LipschitzWith.of_dist_le_mul` from
[`Topology/EMetricSpace/Lipschitz.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/EMetricSpace/Lipschitz.lean),
while the exact tail-cost calculation uses `lintegral_indicator` from
[`MeasureTheory/Integral/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Collapse the complement of the closed Euclidean ball of radius `radius` to zero. -/
def euclideanRadialCollapse (dimension : ℕ) (radius : ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) : EuclideanSpace ℝ (Fin dimension) :=
  if ‖x‖ ≤ radius then x else 0

/-- The Euclidean radial-collapse map is measurable. -/
theorem measurable_euclideanRadialCollapse (dimension : ℕ) (radius : ℝ) :
    Measurable (euclideanRadialCollapse dimension radius) := by
  unfold euclideanRadialCollapse
  apply Measurable.ite
  · exact measurableSet_Iic.preimage measurable_norm
  · exact measurable_id
  · exact measurable_const

/--
The pointwise transport cost of radial collapse is exactly the norm on the
strict outer tail, and zero on the retained ball.  This is the deterministic
tail term that the exponential-moment argument must subsequently estimate.
-/
theorem lintegral_edist_euclideanRadialCollapse_eq_setLIntegral
    (dimension : ℕ) (radius : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin dimension))) :
    ∫⁻ x, edist x (euclideanRadialCollapse dimension radius x) ∂μ =
      ∫⁻ x in {x | radius < ‖x‖}, ENNReal.ofReal ‖x‖ ∂μ := by
  let tail : Set (EuclideanSpace ℝ (Fin dimension)) := {x | radius < ‖x‖}
  have htail : MeasurableSet tail := measurableSet_Ioi.preimage measurable_norm
  have hpoint : (fun x : EuclideanSpace ℝ (Fin dimension) =>
      edist x (euclideanRadialCollapse dimension radius x)) =
      tail.indicator (fun x => ENNReal.ofReal ‖x‖) := by
    funext x
    by_cases hx : x ∈ tail
    · rw [Set.indicator_of_mem hx]
      have hx' : ¬ ‖x‖ ≤ radius := by simpa [tail] using hx
      simp [euclideanRadialCollapse, hx', edist_dist, dist_zero_right]
    · rw [Set.indicator_of_notMem hx]
      have hx' : ‖x‖ ≤ radius := by simpa [tail] using (le_of_not_gt hx)
      simp [euclideanRadialCollapse, hx']
  rw [hpoint, lintegral_indicator htail]

/--
The W₁ error made by collapsing a Euclidean law outside a ball is bounded by
its exact outer-tail first moment.
-/
theorem wassersteinOne_euclideanRadialCollapse_le_tailFirstMoment
    (dimension : ℕ) (radius : ℝ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    ProbabilityCoupling.wassersteinOne law
      (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
      ∫⁻ x in {x | radius < ‖x‖}, ENNReal.ofReal ‖x‖ ∂
        (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
  calc
    ProbabilityCoupling.wassersteinOne law
        (law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
        ∫⁻ x, edist x (euclideanRadialCollapse dimension radius x) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) :=
      ProbabilityCoupling.wassersteinOne_le_lintegral_edist_map law
        (euclideanRadialCollapse dimension radius)
        (measurable_euclideanRadialCollapse dimension radius)
    _ = ∫⁻ x in {x | radius < ‖x‖}, ENNReal.ofReal ‖x‖ ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) :=
      lintegral_edist_euclideanRadialCollapse_eq_setLIntegral dimension radius law

/-- Every coordinate of a collapsed point is bounded by the collapse radius. -/
theorem abs_euclideanRadialCollapse_coordinate_le_radius
    (dimension : ℕ) (radius : ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (i : Fin dimension)
    (hradius : 0 ≤ radius) :
    |euclideanRadialCollapse dimension radius x i| ≤ radius := by
  by_cases hx : ‖x‖ ≤ radius
  · rw [euclideanRadialCollapse, if_pos hx]
    calc
      |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := PiLp.norm_apply_le x i
      _ ≤ radius := hx
  · rw [euclideanRadialCollapse, if_neg hx]
    simp [hradius]

/--
Collapse outside the radius-`R` ball and scale the retained part into the
half-open unit cube. The factor `2R` leaves a margin at the cube boundary,
which matches the source's `(-1, 1]^d` dyadic convention.
-/
def euclideanRadialCollapseScale (dimension : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (x : EuclideanSpace ℝ (Fin dimension)) : HalfOpenUnitCube dimension :=
  ⟨(2 * radius)⁻¹ • euclideanRadialCollapse dimension radius x, by
    intro i
    have habs := abs_euclideanRadialCollapse_coordinate_le_radius
      dimension radius x i hradius.le
    have hcoordinates := abs_le.mp habs
    have hden : 0 < 2 * radius := by positivity
    change -1 < ((2 * radius)⁻¹ • euclideanRadialCollapse dimension radius x) i ∧
      ((2 * radius)⁻¹ • euclideanRadialCollapse dimension radius x) i ≤ 1
    rw [PiLp.smul_apply]
    change -1 < (2 * radius)⁻¹ * euclideanRadialCollapse dimension radius x i ∧
      (2 * radius)⁻¹ * euclideanRadialCollapse dimension radius x i ≤ 1
    rw [show (2 * radius)⁻¹ * euclideanRadialCollapse dimension radius x i =
        euclideanRadialCollapse dimension radius x i / (2 * radius) by field_simp]
    constructor
    · apply (lt_div_iff₀ hden).mpr
      nlinarith
    · apply (div_le_iff₀ hden).mpr
      nlinarith⟩

/-- The collapse-and-scale map into the dyadic cube is measurable. -/
theorem measurable_euclideanRadialCollapseScale (dimension : ℕ) (radius : ℝ)
    (hradius : 0 < radius) :
    Measurable (euclideanRadialCollapseScale dimension radius hradius) := by
  apply Measurable.subtype_mk
  exact (measurable_euclideanRadialCollapse dimension radius).const_smul (2 * radius)⁻¹

/-- Scale a point of the half-open unit cube back into Euclidean space. -/
def euclideanScaleBack (dimension : ℕ) (radius : ℝ)
    (x : HalfOpenUnitCube dimension) : EuclideanSpace ℝ (Fin dimension) :=
  (2 * radius) • x.1

/-- The inverse scaling map is measurable. -/
theorem measurable_euclideanScaleBack (dimension : ℕ) (radius : ℝ) :
    Measurable (euclideanScaleBack dimension radius) := by
  exact measurable_subtype_coe.const_smul (2 * radius)

/-- The inverse scaling map has Lipschitz constant `2 * radius`. -/
theorem lipschitzWith_euclideanScaleBack (dimension : ℕ) (radius : ℝ)
    (hradius : 0 ≤ radius) :
    LipschitzWith ⟨2 * radius, by positivity⟩ (euclideanScaleBack dimension radius) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((2 * radius) • (x : EuclideanSpace ℝ (Fin dimension)))
      ((2 * radius) • (y : EuclideanSpace ℝ (Fin dimension))) ≤
    (2 * radius) * dist (x : EuclideanSpace ℝ (Fin dimension)) y
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity),
    dist_eq_norm]

/-- Scaling back a collapsed-and-scaled point recovers its Euclidean collapse. -/
theorem euclideanScaleBack_radialCollapseScale (dimension : ℕ) (radius : ℝ)
    (hradius : 0 < radius) (x : EuclideanSpace ℝ (Fin dimension)) :
    euclideanScaleBack dimension radius
      (euclideanRadialCollapseScale dimension radius hradius x) =
      euclideanRadialCollapse dimension radius x := by
  unfold euclideanScaleBack euclideanRadialCollapseScale
  change (2 * radius) • ((2 * radius)⁻¹ • euclideanRadialCollapse dimension radius x) = _
  rw [← mul_smul, mul_inv_cancel₀ (by positivity : 2 * radius ≠ 0), one_smul]

/-- The inverse scaling map composed with collapse-and-scale is radial collapse. -/
theorem euclideanScaleBack_comp_radialCollapseScale
    (dimension : ℕ) (radius : ℝ) (hradius : 0 < radius) :
    euclideanScaleBack dimension radius ∘
      euclideanRadialCollapseScale dimension radius hradius =
      euclideanRadialCollapse dimension radius := by
  funext x
  exact euclideanScaleBack_radialCollapseScale dimension radius hradius x

/--
Pushing a law through collapse-and-scale and then through inverse scaling is
exactly its radial-collapse pushforward.
-/
theorem map_euclideanScaleBack_radialCollapseScale
    (dimension : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    (law.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable).map
      (measurable_euclideanScaleBack dimension radius).aemeasurable =
      law.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable := by
  apply Subtype.ext
  change Measure.map (euclideanScaleBack dimension radius)
      (Measure.map (euclideanRadialCollapseScale dimension radius hradius) (law : Measure _)) =
    Measure.map (euclideanRadialCollapse dimension radius) (law : Measure _)
  rw [Measure.map_map (measurable_euclideanScaleBack dimension radius)
    (measurable_euclideanRadialCollapseScale dimension radius hradius)]
  rw [euclideanScaleBack_comp_radialCollapseScale dimension radius hradius]

/--
The W₁ distance between two radial-collapse laws is at most `2R` times the W₁
distance of their collapse-and-scale laws on the dyadic cube. This is the
compact-to-Euclidean transport bridge used by the outer-tail argument.
-/
theorem wassersteinOne_radialCollapse_le_scaleBack_compact
    (dimension : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    ProbabilityCoupling.wassersteinOne
      (mu.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable)
      (nu.map (measurable_euclideanRadialCollapse dimension radius).aemeasurable) ≤
      ((NNReal.mk (2 * radius) (by positivity) : NNReal) : ℝ≥0∞) *
        ProbabilityCoupling.wassersteinOne
          (mu.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
          (nu.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable) := by
  rw [← map_euclideanScaleBack_radialCollapseScale dimension radius hradius mu,
    ← map_euclideanScaleBack_radialCollapseScale dimension radius hradius nu]
  exact ProbabilityCoupling.wassersteinOne_map_le_of_lipschitz
    (euclideanScaleBack dimension radius) (NNReal.mk (2 * radius) (by positivity))
    (lipschitzWith_euclideanScaleBack dimension radius hradius.le)
    (measurable_euclideanScaleBack dimension radius)
    (mu.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)
    (nu.map (measurable_euclideanRadialCollapseScale dimension radius hradius).aemeasurable)

end

end AppliedModelingLib.Probability
