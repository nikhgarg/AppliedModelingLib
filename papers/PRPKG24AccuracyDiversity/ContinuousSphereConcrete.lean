import PRPKG24AccuracyDiversity.ProofInterface
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.Compact

/-!
# Concrete Sphere Support for Proposition 4

This file records source-level facts for the continuous-sphere model in
Proposition 4.  The declarations here avoid bundling the sphere action,
distance-kernel invariance, and transitivity into an opaque certificate.
-/

namespace PRPKG24AccuracyDiversity

open Filter MeasureTheory
open scoped Pointwise

namespace Proposition4Sphere

/-- The paper's unit sphere, as a subtype of the ambient real inner-product space. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  {x : E // x ∈ Metric.sphere (0 : E) 1}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A noncomputable unit-sphere point, constructed from nontriviality. -/
noncomputable def defaultUnitSpherePoint
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] :
    UnitSphere E := by
  classical
  let x : E := Classical.choose (exists_ne (0 : E))
  have hx : x ≠ 0 := Classical.choose_spec (exists_ne (0 : E))
  refine ⟨(‖x‖)⁻¹ • x, ?_⟩
  rw [Metric.mem_sphere, dist_zero_right, norm_smul]
  have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm_ne : ‖x‖ ≠ 0 := ne_of_gt hnorm_pos
  rw [norm_inv, Real.norm_of_nonneg (norm_nonneg x)]
  exact inv_mul_cancel₀ hnorm_ne

/-- A real linear isometry restricts to an action on the unit sphere. -/
def linearIsometrySphereAction (g : E ≃ₗᵢ[ℝ] E) :
    UnitSphere E → UnitSphere E :=
  fun x => ⟨g (x : E), by
    rw [Metric.mem_sphere, dist_zero_right, g.norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using x.property⟩

@[simp]
theorem linearIsometrySphereAction_coe
    (g : E ≃ₗᵢ[ℝ] E) (x : UnitSphere E) :
    (linearIsometrySphereAction g x : E) = g (x : E) :=
  rfl

@[simp]
theorem linearIsometrySphereAction_refl (x : UnitSphere E) :
    linearIsometrySphereAction (LinearIsometryEquiv.refl ℝ E) x = x := by
  apply Subtype.ext
  rfl

@[simp]
theorem linearIsometrySphereAction_trans
    (g h : E ≃ₗᵢ[ℝ] E) (x : UnitSphere E) :
    linearIsometrySphereAction (g.trans h) x =
      linearIsometrySphereAction h (linearIsometrySphereAction g x) := by
  apply Subtype.ext
  rfl

/-- The restricted sphere action is a measurable embedding. -/
theorem linearIsometrySphereAction_measurableEmbedding
    [MeasurableSpace E] [BorelSpace E] (g : E ≃ₗᵢ[ℝ] E) :
    MeasurableEmbedding (linearIsometrySphereAction g : UnitSphere E → UnitSphere E) := by
  let e : UnitSphere E ≃ᵐ UnitSphere E := {
    toEquiv :=
      ({ toFun := linearIsometrySphereAction g
         invFun := linearIsometrySphereAction g.symm
         left_inv := by
           intro x
           apply Subtype.ext
           simp [linearIsometrySphereAction]
         right_inv := by
           intro x
           apply Subtype.ext
           simp [linearIsometrySphereAction] } :
        UnitSphere E ≃ UnitSphere E)
    measurable_toFun := by
      change Measurable (linearIsometrySphereAction g : UnitSphere E → UnitSphere E)
      exact
        ((g.continuous.comp continuous_subtype_val).subtype_mk
          (fun x : UnitSphere E => by
            rw [Metric.mem_sphere, dist_zero_right]
            change ‖g (x : E)‖ = 1
            rw [g.norm_map]
            simpa [Metric.mem_sphere, dist_zero_right] using x.property)).measurable
    measurable_invFun := by
      change Measurable
        (linearIsometrySphereAction g.symm : UnitSphere E → UnitSphere E)
      exact
        ((g.symm.continuous.comp continuous_subtype_val).subtype_mk
          (fun x : UnitSphere E => by
            rw [Metric.mem_sphere, dist_zero_right]
            change ‖g.symm (x : E)‖ = 1
            rw [g.symm.norm_map]
            simpa [Metric.mem_sphere, dist_zero_right] using x.property)).measurable }
  exact e.measurableEmbedding

/--
Linear isometries act transitively on the unit sphere of a real inner-product
space: a reflection sends any anchor point to any target point with the same
norm.
-/
theorem linearIsometrySphereAction_transitive (anchor : UnitSphere E) :
    ∀ x : UnitSphere E,
      ∃ g : E ≃ₗᵢ[ℝ] E, linearIsometrySphereAction g anchor = x := by
  intro x
  let g : E ≃ₗᵢ[ℝ] E :=
    Submodule.reflection (ℝ ∙ ((anchor : E) - (x : E)))ᗮ
  refine ⟨g, ?_⟩
  apply Subtype.ext
  have hnorm : ‖(anchor : E)‖ = ‖(x : E)‖ := by
    have hanchor : ‖(anchor : E)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using anchor.property
    have hx : ‖(x : E)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.property
    rw [hanchor, hx]
  simpa [g, linearIsometrySphereAction] using
    (Submodule.reflection_sub (F := E) hnorm)

/-- The ambient distance is invariant under the restricted sphere action. -/
theorem dist_linearIsometrySphereAction
    (g : E ≃ₗᵢ[ℝ] E) (x u : UnitSphere E) :
    dist ((linearIsometrySphereAction g x : UnitSphere E) : E)
        ((linearIsometrySphereAction g u : UnitSphere E) : E) =
      dist (x : E) (u : E) := by
  simpa [linearIsometrySphereAction, dist_eq_norm] using
    g.norm_map ((x : E) - (u : E))

/-- A radial distance kernel is diagonally invariant under the sphere action. -/
theorem radialDistanceKernel_diagonal_invariant
    (q : ℝ → ℝ) (g : E ≃ₗᵢ[ℝ] E) (x u : UnitSphere E) :
    q (dist ((linearIsometrySphereAction g x : UnitSphere E) : E)
        ((linearIsometrySphereAction g u : UnitSphere E) : E)) =
      q (dist (x : E) (u : E)) := by
  rw [dist_linearIsometrySphereAction]

/-- The paper's log radial kernel is diagonally invariant under sphere isometries. -/
theorem logRadialDistanceKernel_diagonal_invariant
    (p : ℝ → ℝ) (g : E ≃ₗᵢ[ℝ] E) (x u : UnitSphere E) :
    Real.log
        (p (dist ((linearIsometrySphereAction g x : UnitSphere E) : E)
          ((linearIsometrySphereAction g u : UnitSphere E) : E))) =
      Real.log (p (dist (x : E) (u : E))) := by
  rw [dist_linearIsometrySphereAction]

/-- The cone over a sphere set is transported by a linear isometry. -/
theorem linearIsometry_preimage_Ioo_smul_sphere_image
    (g : E ≃ₗᵢ[ℝ] E) (s : Set (UnitSphere E)) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' ((linearIsometrySphereAction g) ⁻¹' s)) =
      g ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨r, hr, z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨r, hr, ((linearIsometrySphereAction g x : UnitSphere E) : E), ?_, ?_⟩
    · exact ⟨linearIsometrySphereAction g x, hx, rfl⟩
    · simp [linearIsometrySphereAction]
  · intro hy
    rcases hy with ⟨r, hr, z, hz, hzy⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨r, hr, ((linearIsometrySphereAction g.symm x : UnitSphere E) : E), ?_, ?_⟩
    · refine ⟨linearIsometrySphereAction g.symm x, ?_, rfl⟩
      simpa [linearIsometrySphereAction] using hx
    · apply g.injective
      simpa [linearIsometrySphereAction] using hzy

/-- Haar-induced surface measure on the unit sphere from an ambient Haar measure. -/
noncomputable abbrev sphereSurfaceMeasure
    [MeasurableSpace E] (μ : MeasureTheory.Measure E) :
    MeasureTheory.Measure (UnitSphere E) :=
  μ.toSphere

/-- Ambient measure preservation induces surface-measure preservation on the unit sphere. -/
theorem sphereSurfaceMeasure_measurePreserving_linearIsometrySphereAction
    [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) (g : E ≃ₗᵢ[ℝ] E)
    (hμ : MeasureTheory.MeasurePreserving g μ μ) :
    MeasureTheory.MeasurePreserving (linearIsometrySphereAction g)
      (sphereSurfaceMeasure μ) (sphereSurfaceMeasure μ) := by
  refine ⟨(linearIsometrySphereAction_measurableEmbedding g).measurable, ?_⟩
  apply MeasureTheory.Measure.ext
  intro s hs
  have hpre :
      MeasurableSet ((linearIsometrySphereAction g) ⁻¹' s) :=
    hs.preimage (linearIsometrySphereAction_measurableEmbedding g).measurable
  rw [(linearIsometrySphereAction_measurableEmbedding g).map_apply,
    sphereSurfaceMeasure,
    MeasureTheory.Measure.toSphere_apply' μ hpre,
    MeasureTheory.Measure.toSphere_apply' μ hs,
    linearIsometry_preimage_Ioo_smul_sphere_image,
    hμ.measure_preimage_emb g.toHomeomorph.measurableEmbedding]

/-- Probability-normalized Haar surface measure on the unit sphere. -/
noncomputable abbrev sphereUniformMeasure
    [MeasurableSpace E] (μ : MeasureTheory.Measure E) :
    MeasureTheory.Measure (UnitSphere E) :=
  ((sphereSurfaceMeasure μ) Set.univ)⁻¹ • sphereSurfaceMeasure μ

/-- Ambient measure preservation induces normalized surface-measure preservation. -/
theorem sphereUniformMeasure_measurePreserving_linearIsometrySphereAction
    [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) (g : E ≃ₗᵢ[ℝ] E)
    (hμ : MeasureTheory.MeasurePreserving g μ μ) :
    MeasureTheory.MeasurePreserving (linearIsometrySphereAction g)
      (sphereUniformMeasure μ) (sphereUniformMeasure μ) := by
  refine ⟨(linearIsometrySphereAction_measurableEmbedding g).measurable, ?_⟩
  unfold sphereUniformMeasure
  rw [MeasureTheory.Measure.map_smul,
    (sphereSurfaceMeasure_measurePreserving_linearIsometrySphereAction
      μ g hμ).map_eq]

theorem sphereSurfaceMeasure_ne_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] :
    sphereSurfaceMeasure μ ≠ 0 := by
  simpa [sphereSurfaceMeasure] using
    (MeasureTheory.Measure.toSphere_ne_zero (μ := μ))

theorem sphereUniformMeasure_isProbabilityMeasure
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] :
    MeasureTheory.IsProbabilityMeasure (sphereUniformMeasure μ) := by
  unfold sphereUniformMeasure sphereSurfaceMeasure
  haveI : NeZero μ.toSphere :=
    ⟨MeasureTheory.Measure.toSphere_ne_zero (μ := μ)⟩
  infer_instance

theorem sphereUniformMeasure_isOpenPosMeasure
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] [μ.IsOpenPosMeasure] :
    MeasureTheory.Measure.IsOpenPosMeasure (sphereUniformMeasure μ) := by
  unfold sphereUniformMeasure sphereSurfaceMeasure
  haveI : MeasureTheory.Measure.IsOpenPosMeasure μ.toSphere := inferInstance
  exact MeasureTheory.Measure.isOpenPosMeasure_smul
    (μ := μ.toSphere)
    (by
      rw [ENNReal.inv_ne_zero]
      exact measure_ne_top μ.toSphere (Set.univ : Set (UnitSphere E)))

/-- The paper's log radial-distance non-satisfaction kernel. -/
noncomputable def logRadialDistanceKernel
    (p : ℝ → ℝ) (x u : UnitSphere E) : ℝ :=
  Real.log (p (dist (x : E) (u : E)))

/-- The log radial-distance kernel is symmetric in item and user variables. -/
theorem logRadialDistanceKernel_swap
    (p : ℝ → ℝ) (x u : UnitSphere E) :
    logRadialDistanceKernel p x u = logRadialDistanceKernel p u x := by
  simp [logRadialDistanceKernel, dist_comm]

/-- Distances between two points on the unit sphere lie in the interval `[0, 2]`. -/
theorem unitSphere_dist_mem_Icc_zero_two (x u : UnitSphere E) :
    dist (x : E) (u : E) ∈ Set.Icc (0 : ℝ) 2 := by
  constructor
  · exact dist_nonneg
  · have hx : ‖(x : E)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.property
    have hu : ‖(u : E)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using u.property
    exact
      (dist_le_norm_add_norm (x : E) (u : E)).trans_eq
        (by rw [hx, hu]; norm_num)

/--
A continuous positive radial profile on the sphere distance range induces a
jointly continuous log radial-distance kernel.
-/
theorem logRadialDistanceKernel_continuous_of_continuous_positive
    (p : ℝ → ℝ)
    (hp : Continuous p)
    (hp_pos : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r) :
    Continuous
      (Function.uncurry
        (fun u : UnitSphere E =>
          fun x : UnitSphere E => logRadialDistanceKernel p x u)) := by
  unfold logRadialDistanceKernel
  have hdist :
      Continuous
        (fun y : UnitSphere E × UnitSphere E =>
          dist (y.2 : E) (y.1 : E)) :=
    (continuous_subtype_val.comp continuous_snd).dist
      (continuous_subtype_val.comp continuous_fst)
  exact
    (hp.comp hdist).log
      (by
        intro y
        exact ne_of_gt
          (hp_pos (dist (y.2 : E) (y.1 : E))
            (unitSphere_dist_mem_Icc_zero_two y.2 y.1)))

/--
Source Proposition 4, concrete unit-sphere radial-kernel endpoint.

This specializes the paper-facing two-measure Proposition 4 theorem to the
unit sphere with kernel `log (p (dist x u))`.  The sphere action,
measurable-embedding, diagonal radial-kernel invariance, and transitivity
premises are proved here from linear-isometry/reflection facts; the remaining
premises are the measure/integrability/Laplace and uniform-average facts.
-/
theorem radialDistanceKernel_uniform_minimizes_of_laplace_defined_gamma
    {Profile : Type*} [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    (preferenceMeasure uniformSphereMeasure :
      MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    [MeasureTheory.IsProbabilityMeasure uniformSphereMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure (UnitSphere E))
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (supValue : Profile → ℝ)
    (p : ℝ → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                (∫ x, logRadialDistanceKernel p x u
                  ∂profileMeasure alpha)))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : Profile,
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((profileMeasure alpha).prod uniformSphereMeasure))
    (uniform_sup_eq : supValue uniformProfile = uniformValue)
    (anchor : UnitSphere E)
    (sphere_action_measurePreserving_uniform :
      ∀ g : E ≃ₗᵢ[ℝ] E,
        MeasureTheory.MeasurePreserving (linearIsometrySphereAction g)
          uniformSphereMeasure uniformSphereMeasure)
    (anchor_integral_eq_uniformValue :
      (∫ u, logRadialDistanceKernel p anchor u ∂uniformSphereMeasure) =
        uniformValue)
    (x0 : Profile → UnitSphere E)
    (hmax :
      ∀ alpha : Profile, ∀ u : UnitSphere E,
        (∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha) ≤
          supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, logRadialDistanceKernel p x (x0 alpha)
            ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : UnitSphere E =>
            ∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, supValue uniformProfile ≤ supValue alpha := by
  exact
    PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_preference_laplace_and_uniform_average_laplace_defined_gamma
      preferenceMeasure uniformSphereMeasure profileMeasure profile_probability
      supValue (logRadialDistanceKernel (E := E) p) uniformProfile
      uniformValue hopen hF_int kernel_integrable_uniform uniform_sup_eq
      (fun g : E ≃ₗᵢ[ℝ] E => linearIsometrySphereAction g)
      (fun g : E ≃ₗᵢ[ℝ] E => linearIsometrySphereAction g)
      anchor sphere_action_measurePreserving_uniform
      (fun g => linearIsometrySphereAction_measurableEmbedding g)
      (by
        intro g x u
        exact logRadialDistanceKernel_diagonal_invariant p g x u)
      (linearIsometrySphereAction_transitive anchor)
      anchor_integral_eq_uniformValue x0 hmax hx0 hcont

/--
Concrete Proposition 4 endpoint with the uniform averaging measure fixed to
the normalized Haar surface measure induced by an ambient Haar measure.

Compared with `radialDistanceKernel_uniform_minimizes_of_laplace_defined_gamma`,
this proves the sphere-level linear-isometry measure-preservation premise from
ambient measure preservation and the concrete `sphereUniformMeasure`.
-/
theorem radialDistanceKernel_sphereUniformMeasure_minimizes_of_laplace_defined_gamma
    {Profile : Type*} [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (ambientMeasure : MeasureTheory.Measure E)
    [ambientMeasure.IsAddHaarMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure (UnitSphere E))
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (supValue : Profile → ℝ)
    (p : ℝ → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                (∫ x, logRadialDistanceKernel p x u
                  ∂profileMeasure alpha)))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : Profile,
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((profileMeasure alpha).prod (sphereUniformMeasure ambientMeasure)))
    (uniform_sup_eq : supValue uniformProfile = uniformValue)
    (anchor : UnitSphere E)
    (ambient_linearIsometry_measurePreserving :
      ∀ g : E ≃ₗᵢ[ℝ] E,
        MeasureTheory.MeasurePreserving g ambientMeasure ambientMeasure)
    (anchor_integral_eq_uniformValue :
      (∫ u, logRadialDistanceKernel p anchor u
          ∂sphereUniformMeasure ambientMeasure) =
        uniformValue)
    (x0 : Profile → UnitSphere E)
    (hmax :
      ∀ alpha : Profile, ∀ u : UnitSphere E,
        (∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha) ≤
          supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, logRadialDistanceKernel p x (x0 alpha)
            ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : UnitSphere E =>
            ∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, supValue uniformProfile ≤ supValue alpha := by
  haveI :
      MeasureTheory.IsProbabilityMeasure
        (sphereUniformMeasure ambientMeasure) :=
    sphereUniformMeasure_isProbabilityMeasure ambientMeasure
  exact
    radialDistanceKernel_uniform_minimizes_of_laplace_defined_gamma
      (E := E) (Profile := Profile)
      preferenceMeasure (sphereUniformMeasure ambientMeasure)
      profileMeasure profile_probability supValue p uniformProfile
      uniformValue hopen hF_int kernel_integrable_uniform uniform_sup_eq
      anchor
      (fun g =>
        sphereUniformMeasure_measurePreserving_linearIsometrySphereAction
          ambientMeasure g (ambient_linearIsometry_measurePreserving g))
      anchor_integral_eq_uniformValue x0 hmax hx0 hcont

/--
Concrete Proposition 4 endpoint with the uniform profile identified with the
normalized Haar surface measure.

This removes the explicit `uniform_sup_eq` and `anchor_integral_eq_uniformValue`
premises from
`radialDistanceKernel_sphereUniformMeasure_minimizes_of_laplace_defined_gamma`:
the radial kernel is symmetric, and the linear-isometry action proves the
anchor integral is the common user integral for the uniform profile.
-/
theorem
    radialDistanceKernel_sphereUniformProfile_minimizes_of_laplace_defined_gamma
    {Profile : Type*} [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (ambientMeasure : MeasureTheory.Measure E)
    [ambientMeasure.IsAddHaarMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure (UnitSphere E))
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (supValue : Profile → ℝ)
    (p : ℝ → ℝ)
    (uniformProfile : Profile)
    (profileMeasure_uniform :
      profileMeasure uniformProfile = sphereUniformMeasure ambientMeasure)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                (∫ x, logRadialDistanceKernel p x u
                  ∂profileMeasure alpha)))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : Profile,
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((profileMeasure alpha).prod (sphereUniformMeasure ambientMeasure)))
    (anchor : UnitSphere E)
    (ambient_linearIsometry_measurePreserving :
      ∀ g : E ≃ₗᵢ[ℝ] E,
        MeasureTheory.MeasurePreserving g ambientMeasure ambientMeasure)
    (x0 : Profile → UnitSphere E)
    (hmax :
      ∀ alpha : Profile, ∀ u : UnitSphere E,
        (∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha) ≤
          supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, logRadialDistanceKernel p x (x0 alpha)
            ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : UnitSphere E =>
            ∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, supValue uniformProfile ≤ supValue alpha := by
  let uniformValue : ℝ :=
    ∫ u, logRadialDistanceKernel p anchor u
      ∂sphereUniformMeasure ambientMeasure
  have hkernel_user_integral_eq :
      ∀ x : UnitSphere E,
        (∫ u, logRadialDistanceKernel p x u
          ∂sphereUniformMeasure ambientMeasure) =
          uniformValue := by
    intro x
    exact
      AppliedModelingLib.Probability.integral_kernel_eq_anchor_of_transitive_diagonal_invariance
        (sphereUniformMeasure ambientMeasure)
        (fun g : E ≃ₗᵢ[ℝ] E => linearIsometrySphereAction g)
        (fun g : E ≃ₗᵢ[ℝ] E => linearIsometrySphereAction g)
        (logRadialDistanceKernel (E := E) p) anchor
        (fun g =>
          sphereUniformMeasure_measurePreserving_linearIsometrySphereAction
            ambientMeasure g (ambient_linearIsometry_measurePreserving g))
        (fun g => linearIsometrySphereAction_measurableEmbedding g)
        (by
          intro g y u
          exact logRadialDistanceKernel_diagonal_invariant p g y u)
        (linearIsometrySphereAction_transitive anchor)
        x
  have huniform_sup_eq : supValue uniformProfile = uniformValue := by
    calc
      supValue uniformProfile =
          (∫ x, logRadialDistanceKernel p x (x0 uniformProfile)
            ∂profileMeasure uniformProfile) := (hx0 uniformProfile).symm
      _ = (∫ x, logRadialDistanceKernel p (x0 uniformProfile) x
            ∂sphereUniformMeasure ambientMeasure) := by
        rw [profileMeasure_uniform]
        apply integral_congr_ae
        filter_upwards with x
        exact logRadialDistanceKernel_swap p x (x0 uniformProfile)
      _ = uniformValue := hkernel_user_integral_eq (x0 uniformProfile)
  exact
    radialDistanceKernel_sphereUniformMeasure_minimizes_of_laplace_defined_gamma
      (E := E) (Profile := Profile)
      preferenceMeasure ambientMeasure profileMeasure profile_probability
      supValue p uniformProfile uniformValue hopen hF_int
      kernel_integrable_uniform huniform_sup_eq anchor
      ambient_linearIsometry_measurePreserving rfl x0 hmax hx0 hcont

/--
Concrete Proposition 4 endpoint with the ambient Haar measure fixed to the
canonical finite-dimensional inner-product-space volume.
-/
theorem
    radialDistanceKernel_sphereVolumeUniformProfile_minimizes_of_laplace_defined_gamma
    {Profile : Type*} [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure (UnitSphere E))
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (supValue : Profile → ℝ)
    (p : ℝ → ℝ)
    (uniformProfile : Profile)
    (profileMeasure_uniform :
      profileMeasure uniformProfile =
        sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E))
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                (∫ x, logRadialDistanceKernel p x u
                  ∂profileMeasure alpha)))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : Profile,
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((profileMeasure alpha).prod
            (sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))))
    (anchor : UnitSphere E)
    (x0 : Profile → UnitSphere E)
    (hmax :
      ∀ alpha : Profile, ∀ u : UnitSphere E,
        (∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha) ≤
          supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, logRadialDistanceKernel p x (x0 alpha)
            ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : UnitSphere E =>
            ∫ x, logRadialDistanceKernel p x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, supValue uniformProfile ≤ supValue alpha :=
  radialDistanceKernel_sphereUniformProfile_minimizes_of_laplace_defined_gamma
    (E := E) (Profile := Profile)
    preferenceMeasure (MeasureTheory.volume : MeasureTheory.Measure E)
    profileMeasure profile_probability supValue p uniformProfile
    profileMeasure_uniform hopen hF_int kernel_integrable_uniform anchor
    (fun g => g.measurePreserving) x0 hmax hx0 hcont

/-- The normalized volume surface measure as a probability measure on the sphere. -/
noncomputable def sphereVolumeUniformProbabilityMeasure
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    MeasureTheory.ProbabilityMeasure (UnitSphere E) :=
  ⟨sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E),
    sphereUniformMeasure_isProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure E)⟩

/--
Concrete Proposition 4 endpoint where relaxed profiles are literally
probability measures on the unit sphere.
-/
theorem
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_laplace_defined_gamma
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (supValue : MeasureTheory.ProbabilityMeasure (UnitSphere E) → ℝ)
    (p : ℝ → ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E), ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                (∫ x, logRadialDistanceKernel p x u
                  ∂(alpha : MeasureTheory.Measure (UnitSphere E)))))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((alpha : MeasureTheory.Measure (UnitSphere E)).prod
            (sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))))
    (anchor : UnitSphere E)
    (x0 : MeasureTheory.ProbabilityMeasure (UnitSphere E) → UnitSphere E)
    (hmax :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        ∀ u : UnitSphere E,
          (∫ x, logRadialDistanceKernel p x u
            ∂(alpha : MeasureTheory.Measure (UnitSphere E))) ≤
            supValue alpha)
    (hx0 :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        (∫ x, logRadialDistanceKernel p x (x0 alpha)
            ∂(alpha : MeasureTheory.Measure (UnitSphere E))) =
          supValue alpha)
    (hcont :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        ContinuousAt
          (fun u : UnitSphere E =>
            ∫ x, logRadialDistanceKernel p x u
              ∂(alpha : MeasureTheory.Measure (UnitSphere E)))
          (x0 alpha)) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
      supValue (sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        supValue alpha :=
  radialDistanceKernel_sphereVolumeUniformProfile_minimizes_of_laplace_defined_gamma
    (E := E) (Profile := MeasureTheory.ProbabilityMeasure (UnitSphere E))
    preferenceMeasure
    (fun alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E) =>
      (alpha : MeasureTheory.Measure (UnitSphere E)))
    (fun alpha => inferInstance)
    supValue p (sphereVolumeUniformProbabilityMeasure (E := E))
    rfl hopen hF_int kernel_integrable_uniform anchor x0 hmax hx0 hcont

/-- User payoff for a probability profile under the log radial-distance kernel. -/
noncomputable def logRadialDistanceProfilePayoff
    [MeasurableSpace E] (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (u : UnitSphere E) : ℝ :=
  ∫ x, logRadialDistanceKernel p x u
    ∂(alpha : MeasureTheory.Measure (UnitSphere E))

/-- Supremum objective over users for a probability profile. -/
noncomputable def logRadialDistanceProfileSupValue
    [MeasurableSpace E] (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E)) : ℝ :=
  sSup (Set.range (logRadialDistanceProfilePayoff (E := E) p alpha))

/--
Equation (25): normalized Haar-sphere symmetry makes the user integral of the
radial log kernel independent of the item.  The source writes the corresponding
unnormalized surface integral as a constant `C`; this normalized form divides
that constant by the sphere's surface mass.
-/
theorem logRadialDistanceKernel_sphereVolumeUniform_integral_eq_anchor
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ) (anchor x : UnitSphere E) :
    (∫ u, logRadialDistanceKernel p x u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ u, logRadialDistanceKernel p anchor u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E) := by
  exact
    AppliedModelingLib.Probability.integral_kernel_eq_anchor_of_transitive_diagonal_invariance
      (sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E))
      (fun g : E ≃ₗᵢ[ℝ] E => linearIsometrySphereAction g)
      (fun g : E ≃ₗᵢ[ℝ] E => linearIsometrySphereAction g)
      (logRadialDistanceKernel (E := E) p) anchor
      (fun g =>
        sphereUniformMeasure_measurePreserving_linearIsometrySphereAction
          (MeasureTheory.volume : MeasureTheory.Measure E) g
          g.measurePreserving)
      (fun g => linearIsometrySphereAction_measurableEmbedding g)
      (by
        intro g y u
        exact logRadialDistanceKernel_diagonal_invariant p g y u)
      (linearIsometrySphereAction_transitive anchor)
      x

/-- Continuous real-valued functions on compact spaces are integrable against probability measures. -/
theorem continuous_integrable_of_probability_compact
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X]
    [SecondCountableTopologyEither X ℝ]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Continuous f) :
    MeasureTheory.Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f)

/--
Equations (21)--(22): Fubini swaps the normalized user average of the profile
payoff with the item-profile integral.  Continuity on the compact product
sphere supplies the product integrability that is implicit in the paper.
-/
theorem logRadialDistanceProfilePayoff_sphereVolume_average_swap
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (hp : Continuous p)
    (hp_pos : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r) :
    (∫ u, logRadialDistanceProfilePayoff (E := E) p alpha u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ x, (∫ u, logRadialDistanceKernel p x u
          ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E))
        ∂(alpha : MeasureTheory.Measure (UnitSphere E)) := by
  haveI :
      MeasureTheory.IsProbabilityMeasure
        (sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)) :=
    sphereUniformMeasure_isProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure E)
  have hkernel :
      Continuous
        (Function.uncurry
          (fun u : UnitSphere E =>
            fun x : UnitSphere E => logRadialDistanceKernel p x u)) :=
    logRadialDistanceKernel_continuous_of_continuous_positive
      (E := E) p hp hp_pos
  have hkernel_swap :
      Continuous
        (Function.uncurry (logRadialDistanceKernel (E := E) p)) := by
    simpa [Function.uncurry] using
      hkernel.comp (continuous_snd.prodMk continuous_fst)
  have hkernel_integrable :
      MeasureTheory.Integrable
        (Function.uncurry (logRadialDistanceKernel (E := E) p))
        ((alpha : MeasureTheory.Measure (UnitSphere E)).prod
          (sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E))) :=
    continuous_integrable_of_probability_compact
      (μ := (alpha : MeasureTheory.Measure (UnitSphere E)).prod
        (sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)))
      hkernel_swap
  have hswap :=
    MeasureTheory.integral_integral_swap
      (μ := (alpha : MeasureTheory.Measure (UnitSphere E)))
      (ν := sphereUniformMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E))
      (f := logRadialDistanceKernel (E := E) p)
      hkernel_integrable
  simpa [logRadialDistanceProfilePayoff] using hswap.symm

/--
Equations (23)--(24): after the Fubini swap, sphere symmetry makes the inner
integral constant and the probability profile integrates that constant to
itself.
-/
theorem logRadialDistanceProfilePayoff_sphereVolume_average_eq_anchorIntegral
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ) (anchor : UnitSphere E)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (hp : Continuous p)
    (hp_pos : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r) :
    (∫ u, logRadialDistanceProfilePayoff (E := E) p alpha u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ u, logRadialDistanceKernel p anchor u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E) := by
  calc
    (∫ u, logRadialDistanceProfilePayoff (E := E) p alpha u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)) =
        ∫ x, (∫ u, logRadialDistanceKernel p x u
            ∂sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))
          ∂(alpha : MeasureTheory.Measure (UnitSphere E)) :=
      logRadialDistanceProfilePayoff_sphereVolume_average_swap
        (E := E) p alpha hp hp_pos
    _ = ∫ _x : UnitSphere E,
          (∫ u, logRadialDistanceKernel p anchor u
            ∂sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))
          ∂(alpha : MeasureTheory.Measure (UnitSphere E)) := by
      apply integral_congr_ae
      filter_upwards with x
      exact
        logRadialDistanceKernel_sphereVolumeUniform_integral_eq_anchor
          (E := E) p anchor x
    _ = ∫ u, logRadialDistanceKernel p anchor u
          ∂sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E) := by
      simp

theorem logRadialDistanceProfilePayoff_continuous_of_kernel_continuous
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (hkernel :
      Continuous
        (Function.uncurry
          (fun u : UnitSphere E =>
            fun x : UnitSphere E => logRadialDistanceKernel p x u))) :
    Continuous (logRadialDistanceProfilePayoff (E := E) p alpha) := by
  unfold logRadialDistanceProfilePayoff
  simpa using
    (continuous_parametric_integral_of_continuous
      (μ := (alpha : MeasureTheory.Measure (UnitSphere E)))
      (f := fun u : UnitSphere E =>
        fun x : UnitSphere E => logRadialDistanceKernel p x u)
      hkernel (s := Set.univ) (isCompact_univ (X := UnitSphere E)))

theorem logRadialDistanceProfilePayoff_exists_max
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (anchor : UnitSphere E)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (hcont :
      Continuous (logRadialDistanceProfilePayoff (E := E) p alpha)) :
    ∃ u0 : UnitSphere E,
      ∀ u : UnitSphere E,
        logRadialDistanceProfilePayoff (E := E) p alpha u ≤
          logRadialDistanceProfilePayoff (E := E) p alpha u0 := by
  haveI : Nonempty (UnitSphere E) := ⟨anchor⟩
  rcases (isCompact_univ (X := UnitSphere E)).exists_isMaxOn
      Set.univ_nonempty hcont.continuousOn with
    ⟨u0, _hu0, hmax⟩
  exact ⟨u0, isMaxOn_univ_iff.mp hmax⟩

theorem logRadialDistanceProfileSupValue_eq_of_exists_max
    [MeasurableSpace E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    {u0 : UnitSphere E}
    (hmax :
      ∀ u : UnitSphere E,
        logRadialDistanceProfilePayoff (E := E) p alpha u ≤
          logRadialDistanceProfilePayoff (E := E) p alpha u0) :
    logRadialDistanceProfileSupValue (E := E) p alpha =
      logRadialDistanceProfilePayoff (E := E) p alpha u0 := by
  unfold logRadialDistanceProfileSupValue
  apply le_antisymm
  · exact
      csSup_le ⟨_, Set.mem_range_self u0⟩
        (by
          intro y hy
          rcases hy with ⟨u, rfl⟩
          exact hmax u)
  · exact
      le_csSup
        ⟨logRadialDistanceProfilePayoff (E := E) p alpha u0, by
          intro y hy
          rcases hy with ⟨u, rfl⟩
          exact hmax u⟩
        (Set.mem_range_self u0)

/--
Equation (26), normalized-measure form: the uniform profile gives every user
the same payoff, namely the normalized anchor integral.  In the source's
unnormalized notation this value is `C / m(S^d)`.
-/
theorem logRadialDistanceProfilePayoff_sphereVolumeUniform_eq_anchorIntegral
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ) (anchor u : UnitSphere E) :
    logRadialDistanceProfilePayoff (E := E) p
        (sphereVolumeUniformProbabilityMeasure (E := E)) u =
      ∫ x, logRadialDistanceKernel p anchor x
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E) := by
  change
    (∫ x, logRadialDistanceKernel p x u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ x, logRadialDistanceKernel p anchor x
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)
  calc
    (∫ x, logRadialDistanceKernel p x u
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E)) =
        ∫ x, logRadialDistanceKernel p u x
          ∂sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E) := by
      apply integral_congr_ae
      filter_upwards with x
      exact logRadialDistanceKernel_swap p x u
    _ = ∫ x, logRadialDistanceKernel p anchor x
          ∂sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E) :=
      logRadialDistanceKernel_sphereVolumeUniform_integral_eq_anchor
        (E := E) p anchor u

/--
Equation (26), objective form: since the uniform-profile payoff is constant,
its user supremum is the same normalized anchor integral.
-/
theorem logRadialDistanceProfileSupValue_sphereVolumeUniform_eq_anchorIntegral
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ) (anchor : UnitSphere E) :
    logRadialDistanceProfileSupValue (E := E) p
        (sphereVolumeUniformProbabilityMeasure (E := E)) =
      ∫ x, logRadialDistanceKernel p anchor x
        ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E) := by
  calc
    logRadialDistanceProfileSupValue (E := E) p
        (sphereVolumeUniformProbabilityMeasure (E := E)) =
        logRadialDistanceProfilePayoff (E := E) p
          (sphereVolumeUniformProbabilityMeasure (E := E)) anchor := by
      apply logRadialDistanceProfileSupValue_eq_of_exists_max
      intro u
      rw [logRadialDistanceProfilePayoff_sphereVolumeUniform_eq_anchorIntegral
          (E := E) p anchor u,
        logRadialDistanceProfilePayoff_sphereVolumeUniform_eq_anchorIntegral
          (E := E) p anchor anchor]
    _ = ∫ x, logRadialDistanceKernel p anchor x
          ∂sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E) :=
      logRadialDistanceProfilePayoff_sphereVolumeUniform_eq_anchorIntegral
        (E := E) p anchor anchor

/--
Equations (17) and (20): the normalized logarithm of the relaxed finite-`n`
failure integral converges to the user supremum of `rho`.  Lean retains the
source preference probability measure in every finite-`n` integral; its full
support and payoff continuity are exactly what make the positive-Laplace
limit equal to the pointwise supremum.
-/
theorem logRadialDistanceProfile_failureIntegral_normalizedLog_tendsto_supValue
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hp : Continuous p)
    (hp_pos : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * Real.log
          (∫ u, Real.exp
              ((n : ℝ) *
                logRadialDistanceProfilePayoff (E := E) p alpha u)
            ∂preferenceMeasure))
      atTop
      (nhds (logRadialDistanceProfileSupValue (E := E) p alpha)) := by
  have hkernel :
      Continuous
        (Function.uncurry
          (fun u : UnitSphere E =>
            fun x : UnitSphere E => logRadialDistanceKernel p x u)) :=
    logRadialDistanceKernel_continuous_of_continuous_positive
      (E := E) p hp hp_pos
  have hpayoff_cont :
      ∀ beta : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        Continuous (logRadialDistanceProfilePayoff (E := E) p beta) :=
    fun beta =>
      logRadialDistanceProfilePayoff_continuous_of_kernel_continuous
        (E := E) p beta hkernel
  let anchor : UnitSphere E := defaultUnitSpherePoint E
  let x0 :
      MeasureTheory.ProbabilityMeasure (UnitSphere E) → UnitSphere E :=
    fun beta =>
      Classical.choose
        (logRadialDistanceProfilePayoff_exists_max
          (E := E) p anchor beta (hpayoff_cont beta))
  have hmax_choose :
      ∀ beta : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        ∀ u : UnitSphere E,
          logRadialDistanceProfilePayoff (E := E) p beta u ≤
            logRadialDistanceProfilePayoff (E := E) p beta (x0 beta) := by
    intro beta
    exact
      Classical.choose_spec
        (logRadialDistanceProfilePayoff_exists_max
          (E := E) p anchor beta (hpayoff_cont beta))
  have hsSup_eq :
      ∀ beta : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        logRadialDistanceProfileSupValue (E := E) p beta =
          logRadialDistanceProfilePayoff (E := E) p beta (x0 beta) := by
    intro beta
    exact
      logRadialDistanceProfileSupValue_eq_of_exists_max
        (E := E) p beta (hmax_choose beta)
  have hF_int :
      ∀ beta : MeasureTheory.ProbabilityMeasure (UnitSphere E), ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                logRadialDistanceProfilePayoff (E := E) p beta u))
          preferenceMeasure := by
    intro beta n
    exact
      continuous_integrable_of_probability_compact
        (μ := preferenceMeasure)
        (Real.continuous_exp.comp
          (continuous_const.mul (hpayoff_cont beta)))
  have hcert :=
    Proposition4AveragingCertificate.positive_laplace_rate_of_attained_pointwise_max_unitWeight
      (fun _ : MeasureTheory.ProbabilityMeasure (UnitSphere E) =>
        preferenceMeasure)
      (logRadialDistanceProfileSupValue (E := E) p)
      (logRadialDistanceProfilePayoff (E := E) p)
      (fun _ => inferInstance)
      (fun _ => hopen)
      hF_int x0
      (by
        intro beta u
        exact (hmax_choose beta u).trans_eq (hsSup_eq beta).symm)
      (by
        intro beta
        exact (hsSup_eq beta).symm)
      (fun beta => (hpayoff_cont beta).continuousAt)
      alpha
  have hrate := hcert.has_rate
  rw [AppliedModelingLib.Probability.HasExponentialRate] at hrate
  have hrate_neg := hrate.neg
  simpa [AppliedModelingLib.Probability.logDecay] using hrate_neg

/--
Concrete Proposition 4 endpoint where the profile objective is the actual
supremum over users. The only analytic profile premise left here is continuity
of each profile payoff, used to attain the compact-sphere maximum required by
the positive-Laplace theorem.
-/
theorem
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_continuous_profileSup
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E), ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                logRadialDistanceProfilePayoff (E := E) p alpha u))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((alpha : MeasureTheory.Measure (UnitSphere E)).prod
            (sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))))
    (anchor : UnitSphere E)
    (hpayoff_cont :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        Continuous (logRadialDistanceProfilePayoff (E := E) p alpha)) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
      logRadialDistanceProfileSupValue (E := E) p
          (sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        logRadialDistanceProfileSupValue (E := E) p alpha := by
  let x0 : MeasureTheory.ProbabilityMeasure (UnitSphere E) → UnitSphere E :=
    fun alpha =>
      Classical.choose
        (logRadialDistanceProfilePayoff_exists_max
          (E := E) p anchor alpha (hpayoff_cont alpha))
  have hmax_choose :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        ∀ u : UnitSphere E,
          logRadialDistanceProfilePayoff (E := E) p alpha u ≤
            logRadialDistanceProfilePayoff (E := E) p alpha (x0 alpha) := by
    intro alpha
    exact
      Classical.choose_spec
        (logRadialDistanceProfilePayoff_exists_max
          (E := E) p anchor alpha (hpayoff_cont alpha))
  have hsSup_eq :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        logRadialDistanceProfileSupValue (E := E) p alpha =
          logRadialDistanceProfilePayoff (E := E) p alpha (x0 alpha) := by
    intro alpha
    exact
      logRadialDistanceProfileSupValue_eq_of_exists_max
        (E := E) p alpha (hmax_choose alpha)
  exact
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_laplace_defined_gamma
      (E := E) preferenceMeasure
      (logRadialDistanceProfileSupValue (E := E) p) p hopen hF_int
      kernel_integrable_uniform anchor x0
      (by
        intro alpha u
        exact (hmax_choose alpha u).trans_eq (hsSup_eq alpha).symm)
      (by
        intro alpha
        exact (hsSup_eq alpha).symm)
      (by
        intro alpha
        exact (hpayoff_cont alpha).continuousAt)

/--
Concrete Proposition 4 endpoint with the profile objective as the actual
supremum over users and the compact-max continuity premise discharged from
joint continuity of the log radial-distance kernel.
-/
theorem
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_kernel_continuous_profileSup
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E), ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                logRadialDistanceProfilePayoff (E := E) p alpha u))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((alpha : MeasureTheory.Measure (UnitSphere E)).prod
            (sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))))
    (anchor : UnitSphere E)
    (hkernel :
      Continuous
        (Function.uncurry
          (fun u : UnitSphere E =>
            fun x : UnitSphere E => logRadialDistanceKernel p x u))) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
      logRadialDistanceProfileSupValue (E := E) p
          (sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        logRadialDistanceProfileSupValue (E := E) p alpha :=
  radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_continuous_profileSup
    (E := E) preferenceMeasure p hopen hF_int kernel_integrable_uniform
    anchor
    (fun alpha =>
      logRadialDistanceProfilePayoff_continuous_of_kernel_continuous
        (E := E) p alpha hkernel)

/--
Concrete Proposition 4 endpoint where compactness and joint kernel continuity
also discharge the integrability hypotheses used by the positive-Laplace and
Fubini/symmetry layers.
-/
theorem
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_compact_kernel_continuous_profileSup
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (anchor : UnitSphere E)
    (hkernel :
      Continuous
        (Function.uncurry
          (fun u : UnitSphere E =>
            fun x : UnitSphere E => logRadialDistanceKernel p x u))) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
      logRadialDistanceProfileSupValue (E := E) p
          (sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        logRadialDistanceProfileSupValue (E := E) p alpha := by
  have hF_int :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E), ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : UnitSphere E =>
            Real.exp
              ((n : ℝ) *
                logRadialDistanceProfilePayoff (E := E) p alpha u))
          preferenceMeasure := by
    intro alpha n
    exact
      continuous_integrable_of_probability_compact
        (μ := preferenceMeasure)
        ((Real.continuous_exp.comp
          ((continuous_const.mul
            (logRadialDistanceProfilePayoff_continuous_of_kernel_continuous
              (E := E) p alpha hkernel)))))
  have kernel_integrable_uniform :
      ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
        MeasureTheory.Integrable
          (Function.uncurry (logRadialDistanceKernel (E := E) p))
          ((alpha : MeasureTheory.Measure (UnitSphere E)).prod
            (sphereUniformMeasure
              (MeasureTheory.volume : MeasureTheory.Measure E))) := by
    intro alpha
    haveI :
        MeasureTheory.IsProbabilityMeasure
          (sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E)) :=
      sphereUniformMeasure_isProbabilityMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)
    have hkernel_swap :
        Continuous
          (Function.uncurry (logRadialDistanceKernel (E := E) p)) := by
      simpa [Function.uncurry] using
        hkernel.comp (continuous_snd.prodMk continuous_fst)
    exact
      continuous_integrable_of_probability_compact
        (μ := (alpha : MeasureTheory.Measure (UnitSphere E)).prod
          (sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E)))
        hkernel_swap
  exact
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_kernel_continuous_profileSup
      (E := E) preferenceMeasure p hopen hF_int
      kernel_integrable_uniform anchor hkernel

/--
Source-shaped Proposition 4 endpoint: the radial function is continuous and
positive on the full unit-sphere distance range `[0, 2]`. This discharges the
joint kernel-continuity premise used by the compact sphere theorem above.
-/
theorem
    radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_continuous_positive_profileSup
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (anchor : UnitSphere E)
    (hp : Continuous p)
    (hp_pos : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E),
      logRadialDistanceProfileSupValue (E := E) p
          (sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        logRadialDistanceProfileSupValue (E := E) p alpha :=
  radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_compact_kernel_continuous_profileSup
    (E := E) preferenceMeasure p hopen anchor
    (logRadialDistanceKernel_continuous_of_continuous_positive
      (E := E) p hp hp_pos)

end Proposition4Sphere

end PRPKG24AccuracyDiversity
