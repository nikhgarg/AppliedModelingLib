import PZMH20PerformativePrediction.DomainExpectedRisk
import PZMH20PerformativePrediction.GradientStepContraction
import PZMH20PerformativePrediction.AffineDomainGeometry

/-!
# Domain-relative repeated-gradient contraction

The frozen-law expected gradient inherits the sharp smooth--strong
interpolation inequality on an arbitrary closed convex feasible domain.  The
ambient gradient may have unconstrained components normal to the affine hull;
only its tangent component occurs below, exactly as required by Euclidean
projection.
-/

namespace PZMH20PerformativePrediction.DomainRelative

open AppliedModelingLib MeasureTheory
open scoped InnerProductSpace

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [CompleteSpace Parameter] [FiniteDimensional ℝ Parameter]
variable [MeasurableSpace Data]

/-- The frozen-law expected gradient satisfies sharp interpolation in the
affine direction of any nonempty closed convex feasible domain.  The case of
equal smoothness and strong-convexity constants follows directly by squeezing
between strong monotonicity and the Lipschitz bound. -/
theorem tangent_frozenGradient_interpolation_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hclosed : IsClosed domain)
    (hconvex : Convex ℝ domain) (anchor deployed : domain)
    {smoothness modulus : ℝ} (hmodulus : 0 < modulus)
    (hmodulus_le : modulus ≤ smoothness)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (hintegrable : ∀ deployed evaluated : domain,
      Integrable (fun datum => gradient datum evaluated)
        (model.dataLaw deployed : Measure Data))
    (first second : domain) :
    smoothness * modulus * ‖(second : Parameter) - (first : Parameter)‖ ^ 2 +
        ‖AffineDomainGeometry.tangentComponent domain
          (frozenGradient model gradient deployed second -
            frozenGradient model gradient deployed first)‖ ^ 2 ≤
      (smoothness + modulus) *
        ⟪frozenGradient model gradient deployed second -
          frozenGradient model gradient deployed first,
          (second : Parameter) - (first : Parameter)⟫_ℝ := by
  classical
  let ambientGradient : Parameter → Parameter := fun parameter =>
    if hparameter : parameter ∈ domain then
      frozenGradient model gradient deployed ⟨parameter, hparameter⟩
    else 0
  have hsmoothness : 0 < smoothness := lt_of_lt_of_le hmodulus hmodulus_le
  have hambientGradient : ∀ parameter (hparameter : parameter ∈ domain),
      ambientGradient parameter =
        frozenGradient model gradient deployed ⟨parameter, hparameter⟩ := by
    intro parameter hparameter
    simp [ambientGradient, hparameter]
  have hcontinuous : ContinuousOn ambientGradient domain := by
    have hlipschitz : LipschitzOnWith ⟨smoothness, hsmoothness.le⟩
        ambientGradient domain := by
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro left hleft right hright
      rw [hambientGradient left hleft, hambientGradient right hright]
      simpa only [NNReal.coe_mk, dist_eq_norm] using
        frozen_gradient_parameter_lipschitz_on model gradient hparameter deployed
          ⟨left, hleft⟩ ⟨right, hright⟩
          (hintegrable deployed ⟨left, hleft⟩)
          (hintegrable deployed ⟨right, hright⟩)
    exact hlipschitz.continuousOn
  by_cases hgap : modulus < smoothness
  · have hinterpolation :=
      AffineDomainGeometry.tangentComponent_interpolation_on_closed_of_quadratic_models
        (measureDecoupledPerformativeRisk (model.extend anchor) deployed)
        ambientGradient domain hclosed hconvex anchor hcontinuous hgap
        (fun center hcenter candidate hcandidate => by
          let centerOn : domain := ⟨center, hcenter⟩
          let candidateOn : domain := ⟨candidate, hcandidate⟩
          rw [model.decoupledPerformativeRisk_extend anchor deployed centerOn,
            model.decoupledPerformativeRisk_extend anchor deployed candidateOn,
            hambientGradient center hcenter]
          exact frozen_risk_lower_model_on model gradient hstrong
            deployed centerOn candidateOn (hintegrable deployed centerOn))
        (fun center hcenter candidate hcandidate => by
          let centerOn : domain := ⟨center, hcenter⟩
          let candidateOn : domain := ⟨candidate, hcandidate⟩
          rw [model.decoupledPerformativeRisk_extend anchor deployed centerOn,
            model.decoupledPerformativeRisk_extend anchor deployed candidateOn,
            hambientGradient center hcenter]
          exact frozen_risk_upper_model_on model gradient hconvex hstrong hparameter
            deployed centerOn candidateOn (hintegrable deployed centerOn))
        first second first.property second.property
    simpa only [hambientGradient first first.property,
      hambientGradient second second.property] using hinterpolation
  · have heq : smoothness = modulus := le_antisymm (le_of_not_gt hgap) hmodulus_le
    have hparameterBound := frozen_gradient_parameter_lipschitz_on model gradient hparameter
      deployed second first (hintegrable deployed second) (hintegrable deployed first)
    have htangentBound := AffineDomainGeometry.norm_tangentComponent_le domain
      (frozenGradient model gradient deployed second -
        frozenGradient model gradient deployed first)
    have hlowerForward := frozen_risk_lower_model_on model gradient hstrong
      deployed first second (hintegrable deployed first)
    have hlowerBackward := frozen_risk_lower_model_on model gradient hstrong
      deployed second first (hintegrable deployed second)
    have hmonotone :
        modulus * ‖(second : Parameter) - (first : Parameter)‖ ^ 2 ≤
          ⟪frozenGradient model gradient deployed second -
              frozenGradient model gradient deployed first,
            (second : Parameter) - (first : Parameter)⟫_ℝ := by
      rw [show (first : Parameter) - (second : Parameter) =
        -((second : Parameter) - (first : Parameter)) by abel,
        inner_neg_right, norm_neg] at hlowerBackward
      rw [inner_sub_left]
      nlinarith only [hlowerForward, hlowerBackward]
    rw [heq] at hparameterBound ⊢
    have htangentSq :
        ‖AffineDomainGeometry.tangentComponent domain
          (frozenGradient model gradient deployed second -
            frozenGradient model gradient deployed first)‖ ^ 2 ≤
          (modulus * ‖(second : Parameter) - (first : Parameter)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hmodulus.le (norm_nonneg _))).mpr
        (htangentBound.trans hparameterBound)
    nlinarith only [hmonotone, htangentSq, hmodulus]

/-- Pairwise contraction of the raw projected-RGD update on the feasible
domain.  The fixed-law part uses only tangent gradients, since variational
projection discards normal components.  The change in deployed data law then
contributes the additive `stepSize * smoothness * sensitivity` term. -/
theorem norm_projected_frozenGradient_update_sub_le
    [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hclosed : IsClosed domain)
    (hconvex : Convex ℝ domain) (anchor : domain) {smoothness : NNReal}
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        (smoothness : ℝ) * ‖(first : Parameter) - (second : Parameter)‖)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    (hintegrable : ∀ deployed evaluated : domain,
      Integrable (fun datum => gradient datum evaluated)
        (model.dataLaw deployed : Measure Data))
    {sensitivity modulus : ℝ}
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 ≤ stepSize)
    (hstepSize_le : stepSize ≤ 2 / ((smoothness : ℝ) + modulus))
    (first second : domain) :
    ‖project ((first : Parameter) -
          stepSize • frozenGradient model gradient first first) -
        project ((second : Parameter) -
          stepSize • frozenGradient model gradient second second)‖ ≤
      (1 - stepSize * ((smoothness : ℝ) * modulus /
        ((smoothness : ℝ) + modulus) - (smoothness : ℝ) * sensitivity)) *
          ‖(first : Parameter) - (second : Parameter)‖ := by
  let firstGradient := frozenGradient model gradient first first
  let frozenSecondGradient := frozenGradient model gradient first second
  let secondGradient := frozenGradient model gradient second second
  have hinterpolation := tangent_frozenGradient_interpolation_on model gradient
    hclosed hconvex anchor first hmodulus hmodulus_le hstrong hparameter hintegrable first second
  have hinterpolationTangent :
      (smoothness : ℝ) * modulus *
            ‖(second : Parameter) - (first : Parameter)‖ ^ 2 +
          ‖AffineDomainGeometry.tangentComponent domain
            (frozenSecondGradient - firstGradient)‖ ^ 2 ≤
        ((smoothness : ℝ) + modulus) *
          ⟪AffineDomainGeometry.tangentComponent domain
              (frozenSecondGradient - firstGradient),
            (second : Parameter) - (first : Parameter)⟫_ℝ := by
    rw [AffineDomainGeometry.inner_tangentComponent_sub_eq
      (frozenSecondGradient - firstGradient) second.property first.property]
    simpa only [firstGradient, frozenSecondGradient] using hinterpolation
  have hsameStep := DomainGradient.norm_sub_smul_le_of_interpolation
    ((second : Parameter) - (first : Parameter))
    (AffineDomainGeometry.tangentComponent domain
      (frozenSecondGradient - firstGradient))
    (lt_of_lt_of_le hmodulus hmodulus_le) hmodulus hstepSize hstepSize_le
    hinterpolationTangent
  have hsameLaw :
      ‖project ((first : Parameter) - stepSize • firstGradient) -
          project ((second : Parameter) - stepSize • frozenSecondGradient)‖ ≤
        (1 - stepSize * ((smoothness : ℝ) * modulus /
          ((smoothness : ℝ) + modulus))) *
            ‖(first : Parameter) - (second : Parameter)‖ := by
    rw [norm_sub_rev]
    calc
      ‖project ((second : Parameter) - stepSize • frozenSecondGradient) -
          project ((first : Parameter) - stepSize • firstGradient)‖ =
          ‖project ((second : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain frozenSecondGradient) -
            project ((first : Parameter) - stepSize • firstGradient)‖ := by
        rw [AffineDomainGeometry.project_sub_smul_tangentComponent_eq hproject
          (second : Parameter) frozenSecondGradient stepSize]
      _ =
          ‖project ((second : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain frozenSecondGradient) -
            project ((first : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain firstGradient)‖ := by
        rw [AffineDomainGeometry.project_sub_smul_tangentComponent_eq hproject
          (first : Parameter) firstGradient stepSize]
      _ ≤ ‖((second : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain frozenSecondGradient) -
            ((first : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain firstGradient)‖ := by
        simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
          hproject_nonexpansive.dist_le_mul
            ((second : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain frozenSecondGradient)
            ((first : Parameter) - stepSize •
              AffineDomainGeometry.tangentComponent domain firstGradient)
      _ = ‖((second : Parameter) - (first : Parameter)) - stepSize •
          AffineDomainGeometry.tangentComponent domain
            (frozenSecondGradient - firstGradient)‖ := by
        rw [AffineDomainGeometry.tangentComponent_sub]
        congr 1
        module
      _ ≤ (1 - stepSize * ((smoothness : ℝ) * modulus /
          ((smoothness : ℝ) + modulus))) *
            ‖(second : Parameter) - (first : Parameter)‖ := hsameStep
      _ = (1 - stepSize * ((smoothness : ℝ) * modulus /
          ((smoothness : ℝ) + modulus))) *
            ‖(first : Parameter) - (second : Parameter)‖ := by
        rw [norm_sub_rev]
  have hlaw := frozen_gradient_law_lipschitz_on model gradient smoothness hdata hsensitive
    first second second (hintegrable first second) (hintegrable second second)
  have hlawShift :
      ‖project ((second : Parameter) - stepSize • frozenSecondGradient) -
          project ((second : Parameter) - stepSize • secondGradient)‖ ≤
        stepSize * (smoothness : ℝ) * sensitivity *
          ‖(first : Parameter) - (second : Parameter)‖ := by
    calc
      ‖project ((second : Parameter) - stepSize • frozenSecondGradient) -
          project ((second : Parameter) - stepSize • secondGradient)‖ ≤
          ‖((second : Parameter) - stepSize • frozenSecondGradient) -
            ((second : Parameter) - stepSize • secondGradient)‖ := by
        simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
          hproject_nonexpansive.dist_le_mul
            ((second : Parameter) - stepSize • frozenSecondGradient)
            ((second : Parameter) - stepSize • secondGradient)
      _ = stepSize * ‖frozenSecondGradient - secondGradient‖ := by
        rw [show ((second : Parameter) - stepSize • frozenSecondGradient) -
            ((second : Parameter) - stepSize • secondGradient) =
              stepSize • (secondGradient - frozenSecondGradient) by
                simp only [smul_sub]
                abel,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg hstepSize, norm_sub_rev]
      _ ≤ stepSize * ((smoothness : ℝ) *
          (sensitivity * ‖(first : Parameter) - (second : Parameter)‖)) := by
        apply mul_le_mul_of_nonneg_left _ hstepSize
        simpa only [frozenSecondGradient, secondGradient, dist_eq_norm] using hlaw
      _ = stepSize * (smoothness : ℝ) * sensitivity *
          ‖(first : Parameter) - (second : Parameter)‖ := by ring
  calc
    ‖project ((first : Parameter) - stepSize •
          frozenGradient model gradient first first) -
        project ((second : Parameter) - stepSize •
          frozenGradient model gradient second second)‖ =
        ‖(project ((first : Parameter) - stepSize • firstGradient) -
            project ((second : Parameter) - stepSize • frozenSecondGradient)) +
          (project ((second : Parameter) - stepSize • frozenSecondGradient) -
            project ((second : Parameter) - stepSize • secondGradient))‖ := by
      simp only [firstGradient, secondGradient]
      congr 1
      abel
    _ ≤ ‖project ((first : Parameter) - stepSize • firstGradient) -
          project ((second : Parameter) - stepSize • frozenSecondGradient)‖ +
        ‖project ((second : Parameter) - stepSize • frozenSecondGradient) -
          project ((second : Parameter) - stepSize • secondGradient)‖ := norm_add_le _ _
    _ ≤ (1 - stepSize * ((smoothness : ℝ) * modulus /
          ((smoothness : ℝ) + modulus))) *
            ‖(first : Parameter) - (second : Parameter)‖ +
        stepSize * (smoothness : ℝ) * sensitivity *
          ‖(first : Parameter) - (second : Parameter)‖ := add_le_add hsameLaw hlawShift
    _ = (1 - stepSize * ((smoothness : ℝ) * modulus /
        ((smoothness : ℝ) + modulus) - (smoothness : ℝ) * sensitivity)) *
          ‖(first : Parameter) - (second : Parameter)‖ := by ring

end PZMH20PerformativePrediction.DomainRelative
