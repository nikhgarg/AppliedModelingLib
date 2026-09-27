import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import PZMH20PerformativePrediction.DomainGradientInterpolation

/-!
# Affine-domain geometry for projected gradient methods

A closed convex parameter domain may lie in a proper affine subspace of the
ambient Hilbert space.  Gradient components normal to that affine hull do not
enter feasible first-order models, and Euclidean projection ignores them.

This file records those two facts and gives an affine-isometric chart from the
affine hull to its direction subspace.  In finite dimension the charted domain
is closed and convex, spans the whole direction subspace, and consequently has
nonempty interior there.  Thus open-domain gradient interpolation can be
applied intrinsically and then extended to the closed domain.
-/

namespace PZMH20PerformativePrediction.AffineDomainGeometry

open AppliedModelingLib
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear direction of the affine hull of a feasible domain. -/
def affineDirection (domain : Set E) : Submodule ℝ E :=
  (affineSpan ℝ domain).direction

/-- The displacement between two feasible points lies in the direction of the
affine hull. -/
theorem sub_mem_affineDirection {domain : Set E} {first second : E}
    (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    first - second ∈ affineDirection domain := by
  rw [affineDirection, direction_affineSpan]
  simpa only [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hfirst hsecond

section FiniteDimensionalProjection

variable [FiniteDimensional ℝ E]

/-- The component of an ambient vector tangent to the affine hull of `domain`. -/
noncomputable def tangentComponent (domain : Set E) (vector : E) : E :=
  (affineDirection domain).starProjection vector

/-- The discarded component of a vector is normal to the affine hull. -/
theorem sub_tangentComponent_mem_orthogonal (domain : Set E) (vector : E) :
    vector - tangentComponent domain vector ∈ (affineDirection domain)ᗮ := by
  exact (affineDirection domain).sub_starProjection_mem_orthogonal vector

/-- Tangent projection does not change pairings against feasible
displacements. -/
theorem inner_tangentComponent_sub_eq {domain : Set E} (vector : E)
    {first second : E} (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    ⟪tangentComponent domain vector, first - second⟫_ℝ =
      ⟪vector, first - second⟫_ℝ := by
  have hnormal :
      ⟪vector - tangentComponent domain vector, first - second⟫_ℝ = 0 :=
    ((affineDirection domain).mem_orthogonal' _).1
      (sub_tangentComponent_mem_orthogonal domain vector) _
      (sub_mem_affineDirection hfirst hsecond)
  rw [inner_sub_left] at hnormal
  linarith

/-- Tangent projection is norm non-increasing. -/
theorem norm_tangentComponent_le (domain : Set E) (vector : E) :
    ‖tangentComponent domain vector‖ ≤ ‖vector‖ := by
  exact (affineDirection domain).norm_starProjection_apply_le vector

/-- Tangent projection commutes with subtraction. -/
theorem tangentComponent_sub (domain : Set E) (first second : E) :
    tangentComponent domain (first - second) =
      tangentComponent domain first - tangentComponent domain second := by
  exact (affineDirection domain).starProjection.map_sub first second

end FiniteDimensionalProjection

/-- A variational Euclidean projection is unchanged when its input is shifted
in a direction normal to the affine hull of its feasible set. -/
theorem project_add_normal_eq
    {domain : Set E} {project : E → E}
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (input normal : E)
    (hnormal : normal ∈ (affineDirection domain)ᗮ) :
    project (input + normal) = project input := by
  let projected := project input
  let shiftedProjected := project (input + normal)
  have hprojected : projected ∈ domain := hproject.1 input
  have hshiftedProjected : shiftedProjected ∈ domain := hproject.1 (input + normal)
  have hdirection : shiftedProjected - projected ∈ affineDirection domain :=
    sub_mem_affineDirection hshiftedProjected hprojected
  have hnormalInner : ⟪normal, shiftedProjected - projected⟫_ℝ = 0 :=
    ((affineDirection domain).mem_orthogonal' normal).1 hnormal _ hdirection
  have hunshifted := hproject.2 input shiftedProjected hshiftedProjected
  have hshifted := hproject.2 (input + normal) projected hprojected
  change ⟪input - projected, shiftedProjected - projected⟫_ℝ ≤ 0 at hunshifted
  change ⟪input + normal - shiftedProjected, projected - shiftedProjected⟫_ℝ ≤ 0 at hshifted
  rw [show projected - shiftedProjected = -(shiftedProjected - projected) by abel,
    inner_neg_right] at hshifted
  have hshifted' : 0 ≤
      ⟪input + normal - shiftedProjected, shiftedProjected - projected⟫_ℝ := by
    linarith
  have hdecompose : input + normal - shiftedProjected =
      (input - projected) + normal - (shiftedProjected - projected) := by
    abel
  rw [hdecompose, inner_sub_left, inner_add_left, hnormalInner,
    real_inner_self_eq_norm_sq, add_zero] at hshifted'
  have hnorm : ‖shiftedProjected - projected‖ = 0 := by
    nlinarith [sq_nonneg ‖shiftedProjected - projected‖]
  have heq : shiftedProjected = projected := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  simpa only [shiftedProjected, projected] using heq

section FiniteDimensionalProjection

variable [FiniteDimensional ℝ E]

/-- A projected-gradient step depends only on the tangent component of the
gradient, even if the ambient gradient has an arbitrary normal component. -/
theorem project_sub_smul_tangentComponent_eq
    {domain : Set E} {project : E → E}
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (parameter gradient : E) (stepSize : ℝ) :
    project (parameter - stepSize • gradient) =
      project (parameter - stepSize • tangentComponent domain gradient) := by
  let normal := (-stepSize) • (gradient - tangentComponent domain gradient)
  have hnormal : normal ∈ (affineDirection domain)ᗮ :=
    ((affineDirection domain)ᗮ).smul_mem (-stepSize)
      (sub_tangentComponent_mem_orthogonal domain gradient)
  have hinvariant := project_add_normal_eq hproject
    (parameter - stepSize • tangentComponent domain gradient) normal hnormal
  calc
    project (parameter - stepSize • gradient) =
        project ((parameter - stepSize • tangentComponent domain gradient) + normal) := by
      congr 1
      dsimp only [normal]
      module
    _ = project (parameter - stepSize • tangentComponent domain gradient) := hinvariant

end FiniteDimensionalProjection

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The affine-isometric inclusion taking an intrinsic coordinate back to its
ambient point. -/
noncomputable def affineCoordinatesToAmbient (domain : Set E) (anchor : domain) :
    affineDirection domain →ᵃⁱ[ℝ] E := by
  exact (AffineIsometryEquiv.constVAdd ℝ E (anchor : E)).toAffineIsometry.comp
    (affineDirection domain).subtypeₗᵢ.toAffineIsometry

/-- The intrinsic coordinate of a feasible point, namely `point - anchor`. -/
def affineCoordinateOf (domain : Set E) (anchor point : domain) : affineDirection domain :=
  ⟨(point : E) - (anchor : E), sub_mem_affineDirection point.property anchor.property⟩

/-- The feasible domain in intrinsic linear coordinates. -/
noncomputable def affineCoordinateDomain (domain : Set E) (anchor : domain) :
    Set (affineDirection domain) :=
  (affineCoordinatesToAmbient domain anchor) ⁻¹' domain

@[simp]
theorem affineCoordinatesToAmbient_apply (domain : Set E) (anchor : domain)
    (coordinate : affineDirection domain) :
    affineCoordinatesToAmbient domain anchor coordinate =
      (coordinate : E) + (anchor : E) := by
  simp [affineCoordinatesToAmbient, add_comm]

@[simp]
theorem affineCoordinatesToAmbient_affineCoordinateOf
    (domain : Set E) (anchor point : domain) :
    affineCoordinatesToAmbient domain anchor (affineCoordinateOf domain anchor point) = point := by
  simp only [affineCoordinatesToAmbient_apply, affineCoordinateOf, Submodule.coe_mk]
  abel

/-- Every feasible point gives a feasible intrinsic coordinate. -/
theorem affineCoordinateOf_mem (domain : Set E) (anchor point : domain) :
    affineCoordinateOf domain anchor point ∈ affineCoordinateDomain domain anchor := by
  rw [affineCoordinateDomain, Set.mem_preimage,
    affineCoordinatesToAmbient_affineCoordinateOf]
  exact point.property

@[simp]
theorem mem_affineCoordinateDomain_iff (domain : Set E) (anchor : domain)
    (coordinate : affineDirection domain) :
    coordinate ∈ affineCoordinateDomain domain anchor ↔
      (coordinate : E) + (anchor : E) ∈ domain := by
  rw [affineCoordinateDomain, Set.mem_preimage, affineCoordinatesToAmbient_apply]

/-- Intrinsic coordinates preserve displacement norms. -/
theorem norm_affineCoordinatesToAmbient_sub (domain : Set E) (anchor : domain)
    (first second : affineDirection domain) :
    ‖affineCoordinatesToAmbient domain anchor first -
        affineCoordinatesToAmbient domain anchor second‖ = ‖first - second‖ := by
  simpa only [dist_eq_norm] using
    (affineCoordinatesToAmbient domain anchor).dist_map first second

/-- The intrinsic coordinate domain is convex. -/
theorem convex_affineCoordinateDomain {domain : Set E} (hconvex : Convex ℝ domain)
    (anchor : domain) : Convex ℝ (affineCoordinateDomain domain anchor) := by
  exact hconvex.affine_preimage (affineCoordinatesToAmbient domain anchor).toAffineMap

/-- The intrinsic coordinate domain is closed when the ambient domain is
closed. -/
theorem isClosed_affineCoordinateDomain {domain : Set E} (hclosed : IsClosed domain)
    (anchor : domain) : IsClosed (affineCoordinateDomain domain anchor) := by
  exact hclosed.preimage (affineCoordinatesToAmbient domain anchor).continuous

/-- The origin is the coordinate of the chosen feasible anchor. -/
theorem zero_mem_affineCoordinateDomain (domain : Set E) (anchor : domain) :
    (0 : affineDirection domain) ∈ affineCoordinateDomain domain anchor := by
  simp

/-- The intrinsic coordinate domain has full affine span in the direction
subspace. -/
theorem affineSpan_affineCoordinateDomain_eq_top (domain : Set E) (anchor : domain) :
    affineSpan ℝ (affineCoordinateDomain domain anchor) = ⊤ := by
  letI : Nonempty domain := ⟨anchor⟩
  let anchorInSpan : affineSpan ℝ domain :=
    ⟨anchor, subset_affineSpan ℝ domain anchor.property⟩
  letI : Nonempty (affineSpan ℝ domain) := ⟨anchorInSpan⟩
  let chart : affineSpan ℝ domain ≃ᵃⁱ[ℝ] (affineSpan ℝ domain).direction :=
    (AffineIsometryEquiv.constVSub ℝ anchorInSpan).trans
      (LinearIsometryEquiv.neg ℝ).toAffineIsometryEquiv
  have hchartToAmbient (point : affineSpan ℝ domain) :
      affineCoordinatesToAmbient domain anchor (chart point) = (point : E) := by
    simp [chart, affineCoordinatesToAmbient, anchorInSpan, add_comm]
  have himage : affineCoordinateDomain domain anchor =
      chart ''
        (((↑) : affineSpan ℝ domain → E) ⁻¹' domain) := by
    ext coordinate
    constructor
    · intro hcoordinate
      let point : affineSpan ℝ domain :=
        ⟨affineCoordinatesToAmbient domain anchor coordinate,
          subset_affineSpan ℝ domain hcoordinate⟩
      refine ⟨point, hcoordinate, ?_⟩
      apply (affineCoordinatesToAmbient domain anchor).injective
      rw [hchartToAmbient]
    · rintro ⟨point, hpoint, rfl⟩
      rw [affineCoordinateDomain, Set.mem_preimage, hchartToAmbient]
      exact hpoint
  rw [himage]
  apply chart.toAffineEquiv.toAffineMap.span_eq_top_of_surjective chart.surjective
  exact affineSpan_coe_preimage_eq_top domain

/-- A nonempty convex domain has nonempty interior in its own affine
coordinates, including when its ambient interior is empty. -/
theorem interior_affineCoordinateDomain_nonempty {domain : Set E}
    (hconvex : Convex ℝ domain) (anchor : domain) :
    (interior (affineCoordinateDomain domain anchor)).Nonempty := by
  rw [convex_affineCoordinateDomain hconvex anchor |>.interior_nonempty_iff_affineSpan_eq_top]
  exact affineSpan_affineCoordinateDomain_eq_top domain anchor

/-- The relative interior is dense in a closed nonempty convex domain, stated
in intrinsic coordinates. -/
theorem closure_interior_affineCoordinateDomain {domain : Set E}
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) (anchor : domain) :
    closure (interior (affineCoordinateDomain domain anchor)) =
      affineCoordinateDomain domain anchor := by
  calc
    closure (interior (affineCoordinateDomain domain anchor)) =
        closure (affineCoordinateDomain domain anchor) :=
      (convex_affineCoordinateDomain hconvex anchor).closure_interior_eq_closure_of_nonempty_interior
        (interior_affineCoordinateDomain_nonempty hconvex anchor)
    _ = affineCoordinateDomain domain anchor :=
      (isClosed_affineCoordinateDomain hclosed anchor).closure_eq

/-- The gradient expressed in intrinsic coordinates. -/
noncomputable def affineCoordinateGradient (domain : Set E) (anchor : domain)
    (gradient : E → E) : affineDirection domain → affineDirection domain :=
  fun coordinate => (affineDirection domain).orthogonalProjection
    (gradient (affineCoordinatesToAmbient domain anchor coordinate))

/-- Continuity of an ambient gradient on the feasible domain transfers to its
tangent component in intrinsic coordinates. -/
theorem continuousOn_affineCoordinateGradient {domain : Set E} (anchor : domain)
    (gradient : E → E) (hgradient : ContinuousOn gradient domain) :
    ContinuousOn (affineCoordinateGradient domain anchor gradient)
      (affineCoordinateDomain domain anchor) := by
  have hcomposed : ContinuousOn
      (fun coordinate : affineDirection domain =>
        gradient (affineCoordinatesToAmbient domain anchor coordinate))
      (affineCoordinateDomain domain anchor) :=
    hgradient.comp' (affineCoordinatesToAmbient domain anchor).continuous.continuousOn
      (fun _ hcoordinate => hcoordinate)
  exact (affineDirection domain).orthogonalProjection.continuous.comp_continuousOn' hcomposed

/-- At the coordinate of a feasible point, the intrinsic gradient coerces to
the tangent component of the ambient gradient. -/
theorem coe_affineCoordinateGradient_affineCoordinateOf
    (domain : Set E) (anchor point : domain) (gradient : E → E) :
    (affineCoordinateGradient domain anchor gradient
        (affineCoordinateOf domain anchor point) : E) =
      tangentComponent domain (gradient point) := by
  rw [affineCoordinateGradient, affineCoordinatesToAmbient_affineCoordinateOf]
  rfl

/-- Intrinsic gradient pairings are exactly the ambient gradient pairings
against the corresponding feasible displacement. -/
theorem inner_affineCoordinateGradient_sub_eq (domain : Set E) (anchor : domain)
    (gradient : E → E) (center candidate : affineDirection domain) :
    ⟪affineCoordinateGradient domain anchor gradient center, candidate - center⟫_ℝ =
      ⟪gradient (affineCoordinatesToAmbient domain anchor center),
        affineCoordinatesToAmbient domain anchor candidate -
          affineCoordinatesToAmbient domain anchor center⟫_ℝ := by
  rw [show affineCoordinatesToAmbient domain anchor candidate -
      affineCoordinatesToAmbient domain anchor center =
        ((candidate - center : affineDirection domain) : E) by
      simp only [affineCoordinatesToAmbient_apply, Submodule.coe_sub]
      abel]
  exact (affineDirection domain).inner_orthogonalProjection_eq_of_mem_right
    (candidate - center) (gradient (affineCoordinatesToAmbient domain anchor center))

/-- A scalar quadratic lower model transfers verbatim to intrinsic
coordinates. -/
theorem affineCoordinate_lower_model
    {domain : Set E} (anchor : domain) (objective : E → ℝ) (gradient : E → E)
    (modulus : ℝ)
    (hlower : ∀ center ∈ domain, ∀ candidate ∈ domain,
      objective candidate ≥ objective center +
        ⟪gradient center, candidate - center⟫_ℝ +
          modulus / 2 * ‖candidate - center‖ ^ 2)
    (center : affineDirection domain) (hcenter : center ∈ affineCoordinateDomain domain anchor)
    (candidate : affineDirection domain)
    (hcandidate : candidate ∈ affineCoordinateDomain domain anchor) :
    objective (affineCoordinatesToAmbient domain anchor candidate) ≥
      objective (affineCoordinatesToAmbient domain anchor center) +
        ⟪affineCoordinateGradient domain anchor gradient center, candidate - center⟫_ℝ +
          modulus / 2 * ‖candidate - center‖ ^ 2 := by
  rw [inner_affineCoordinateGradient_sub_eq,
    ← norm_affineCoordinatesToAmbient_sub domain anchor candidate center]
  exact hlower _ hcenter _ hcandidate

/-- A scalar quadratic upper model transfers verbatim to intrinsic
coordinates. -/
theorem affineCoordinate_upper_model
    {domain : Set E} (anchor : domain) (objective : E → ℝ) (gradient : E → E)
    (smoothness : ℝ)
    (hupper : ∀ center ∈ domain, ∀ candidate ∈ domain,
      objective candidate ≤ objective center +
        ⟪gradient center, candidate - center⟫_ℝ +
          smoothness / 2 * ‖candidate - center‖ ^ 2)
    (center : affineDirection domain) (hcenter : center ∈ affineCoordinateDomain domain anchor)
    (candidate : affineDirection domain)
    (hcandidate : candidate ∈ affineCoordinateDomain domain anchor) :
    objective (affineCoordinatesToAmbient domain anchor candidate) ≤
      objective (affineCoordinatesToAmbient domain anchor center) +
        ⟪affineCoordinateGradient domain anchor gradient center, candidate - center⟫_ℝ +
          smoothness / 2 * ‖candidate - center‖ ^ 2 := by
  rw [inner_affineCoordinateGradient_sub_eq,
    ← norm_affineCoordinatesToAmbient_sub domain anchor candidate center]
  exact hupper _ hcenter _ hcandidate

/-- Smooth--strong gradient interpolation on an arbitrary nonempty closed
convex finite-dimensional domain.  The ambient gradient is first projected to
the affine direction.  Normal gradient components remain unrestricted. -/
theorem tangentComponent_interpolation_on_closed_of_quadratic_models
    (objective : E → ℝ) (gradient : E → E) (domain : Set E)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) (anchor : domain)
    (hgradient : ContinuousOn gradient domain) {β γ : ℝ} (hgap : γ < β)
    (hlower : ∀ center ∈ domain, ∀ candidate ∈ domain,
      objective center + ⟪gradient center, candidate - center⟫_ℝ +
        γ / 2 * ‖candidate - center‖ ^ 2 ≤ objective candidate)
    (hupper : ∀ center ∈ domain, ∀ candidate ∈ domain,
      objective candidate ≤ objective center +
        ⟪gradient center, candidate - center⟫_ℝ +
          β / 2 * ‖candidate - center‖ ^ 2)
    (first second : E) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    β * γ * ‖second - first‖ ^ 2 +
        ‖tangentComponent domain (gradient second - gradient first)‖ ^ 2 ≤
      (β + γ) * ⟪gradient second - gradient first, second - first⟫_ℝ := by
  let firstPoint : domain := ⟨first, hfirst⟩
  let secondPoint : domain := ⟨second, hsecond⟩
  let firstCoordinate := affineCoordinateOf domain anchor firstPoint
  let secondCoordinate := affineCoordinateOf domain anchor secondPoint
  have hinterpolation :=
    DomainGradient.gradient_interpolation_on_closed_of_quadratic_models
      (fun coordinate => objective (affineCoordinatesToAmbient domain anchor coordinate))
      (affineCoordinateGradient domain anchor gradient)
      (affineCoordinateDomain domain anchor)
      (isClosed_affineCoordinateDomain hclosed anchor)
      (convex_affineCoordinateDomain hconvex anchor)
      (interior_affineCoordinateDomain_nonempty hconvex anchor)
      (continuousOn_affineCoordinateGradient anchor gradient hgradient)
      hgap
      (fun center hcenter candidate hcandidate =>
        affineCoordinate_lower_model anchor objective gradient γ hlower
          center hcenter candidate hcandidate)
      (fun center hcenter candidate hcandidate =>
        affineCoordinate_upper_model anchor objective gradient β hupper
          center hcenter candidate hcandidate)
      firstCoordinate secondCoordinate
      (affineCoordinateOf_mem domain anchor firstPoint)
      (affineCoordinateOf_mem domain anchor secondPoint)
  have hparameterNorm : ‖secondCoordinate - firstCoordinate‖ = ‖second - first‖ := by
    rw [← norm_affineCoordinatesToAmbient_sub domain anchor]
    simp only [firstCoordinate, secondCoordinate,
      affineCoordinatesToAmbient_affineCoordinateOf, firstPoint, secondPoint]
  have hgradientNorm :
      ‖affineCoordinateGradient domain anchor gradient secondCoordinate -
          affineCoordinateGradient domain anchor gradient firstCoordinate‖ =
        ‖tangentComponent domain (gradient second - gradient first)‖ := by
    calc
      ‖affineCoordinateGradient domain anchor gradient secondCoordinate -
          affineCoordinateGradient domain anchor gradient firstCoordinate‖ =
          ‖tangentComponent domain (gradient second) -
            tangentComponent domain (gradient first)‖ := by
              simp only [firstCoordinate, secondCoordinate, firstPoint, secondPoint,
                ← Submodule.norm_coe,
                coe_affineCoordinateGradient_affineCoordinateOf, Submodule.coe_sub]
      _ = ‖tangentComponent domain (gradient second - gradient first)‖ := by
        rw [tangentComponent_sub]
  have hpairing :
      ⟪affineCoordinateGradient domain anchor gradient secondCoordinate -
          affineCoordinateGradient domain anchor gradient firstCoordinate,
        secondCoordinate - firstCoordinate⟫_ℝ =
        ⟪gradient second - gradient first, second - first⟫_ℝ := by
    calc
      ⟪affineCoordinateGradient domain anchor gradient secondCoordinate -
          affineCoordinateGradient domain anchor gradient firstCoordinate,
        secondCoordinate - firstCoordinate⟫_ℝ =
          ⟪tangentComponent domain (gradient second) -
              tangentComponent domain (gradient first),
            second - first⟫_ℝ := by
              rw [Submodule.coe_inner, Submodule.coe_sub,
                coe_affineCoordinateGradient_affineCoordinateOf,
                coe_affineCoordinateGradient_affineCoordinateOf, Submodule.coe_sub]
              simp only [firstCoordinate, secondCoordinate, firstPoint, secondPoint,
                affineCoordinateOf, Submodule.coe_mk]
              congr 1
              abel
      _ = ⟪tangentComponent domain (gradient second - gradient first),
          second - first⟫_ℝ := by rw [tangentComponent_sub]
      _ = ⟪gradient second - gradient first, second - first⟫_ℝ :=
        inner_tangentComponent_sub_eq (gradient second - gradient first) hsecond hfirst
  rw [hparameterNorm, hgradientNorm, hpairing] at hinterpolation
  exact hinterpolation

end FiniteDimensional

end PZMH20PerformativePrediction.AffineDomainGeometry
