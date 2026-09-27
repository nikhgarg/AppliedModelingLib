import PZMH20PerformativePrediction.DomainRelativeRRM
import PZMH20PerformativePrediction.DomainSmoothUpperModel

/-!
# Frozen expected risk on the feasible domain

Integrating the pointwise lower and upper quadratic models identifies the
first-order behavior of expected risk without differentiating an integral.
Only the explicitly supplied on-domain population gradient must be Bochner
integrable; no loss or gradient regularity is assumed away from the domain.
-/

namespace PZMH20PerformativePrediction.DomainRelative

open AppliedModelingLib MeasureTheory
open scoped InnerProductSpace

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [CompleteSpace Parameter] [MeasurableSpace Data]

/-- Expected pointwise gradient under a frozen deployed law. -/
noncomputable def frozenGradient
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (deployed evaluated : domain) : Parameter :=
  ∫ datum, gradient datum evaluated ∂(model.dataLaw deployed : Measure Data)

/-- An integrable affine gradient model commutes with expectation. -/
theorem integral_affine_gradient_model
    (law : ProbabilityMeasure Data) (loss : Data → ℝ) (gradient : Data → Parameter)
    (hloss : Integrable loss (law : Measure Data))
    (hgradient : Integrable gradient (law : Measure Data))
    (displacement : Parameter) (constant : ℝ) :
    (∫ datum, loss datum + ⟪gradient datum, displacement⟫_ℝ + constant
      ∂(law : Measure Data)) =
      (∫ datum, loss datum ∂(law : Measure Data)) +
        ⟪∫ datum, gradient datum ∂(law : Measure Data), displacement⟫_ℝ + constant := by
  have hpair : Integrable (fun datum => ⟪gradient datum, displacement⟫_ℝ)
      (law : Measure Data) := hgradient.inner_const displacement
  have hsum : Integrable (fun datum => loss datum + ⟪gradient datum, displacement⟫_ℝ)
      (law : Measure Data) := hloss.add hpair
  rw [integral_add hsum (integrable_const constant), integral_add hloss hpair,
    integral_const, probReal_univ, one_smul]
  congr 2
  simpa only [real_inner_comm] using integral_inner hgradient displacement

/-- The source's pointwise strong-convexity model averages on the domain. -/
theorem frozen_risk_lower_model_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) {modulus : ℝ}
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (deployed center candidate : domain)
    (hintegrable : Integrable (fun datum => gradient datum center)
      (model.dataLaw deployed : Measure Data)) :
    model.decoupledPerformativeRisk deployed center +
        ⟪frozenGradient model gradient deployed center,
          (candidate : Parameter) - (center : Parameter)⟫_ℝ +
        modulus / 2 * ‖(candidate : Parameter) - (center : Parameter)‖ ^ 2 ≤
      model.decoupledPerformativeRisk deployed candidate := by
  rw [MeasurePerformativeModelOn.decoupledPerformativeRisk, frozenGradient,
    ← integral_affine_gradient_model (model.dataLaw deployed) (fun datum => model.loss datum center)
      (fun datum => gradient datum center) (model.loss_integrable deployed center) hintegrable]
  exact integral_mono
    (((model.loss_integrable deployed center).add (hintegrable.inner_const _)).add
      (integrable_const _))
    (model.loss_integrable deployed candidate) (fun datum => hstrong.2 datum center candidate)

/-- The within-domain descent lemma gives a pointwise upper quadratic model. -/
theorem loss_upper_model_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {smoothness modulus : ℝ}
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (datum : Data) (center candidate : domain) :
    model.loss datum candidate ≤ model.loss datum center +
      ⟪gradient datum center, (candidate : Parameter) - (center : Parameter)⟫_ℝ +
      smoothness / 2 * ‖(candidate : Parameter) - (center : Parameter)‖ ^ 2 := by
  classical
  have hgrad : ∀ parameter ∈ domain,
      HasGradientWithinAt ((model.extend center).loss datum)
        (MeasurePerformativeModelOn.extendGradient gradient center datum parameter)
        domain parameter := by
    intro parameter hparameter
    simpa [HasGradientWithinAt, MeasurePerformativeModelOn.extend,
      MeasurePerformativeModelOn.extendGradient, hparameter] using
      hstrong.1 datum (⟨parameter, hparameter⟩ : domain)
  have hparameter' : ∀ first ∈ domain, ∀ second ∈ domain,
      ‖MeasurePerformativeModelOn.extendGradient gradient center datum first -
          MeasurePerformativeModelOn.extendGradient gradient center datum second‖ ≤
        smoothness * ‖first - second‖ := by
    intro first hfirst second hsecond
    simpa [MeasurePerformativeModelOn.extendGradient, hfirst, hsecond] using
      hparameter datum (⟨first, hfirst⟩ : domain) (⟨second, hsecond⟩ : domain)
  have h := DomainGradient.smooth_upper_model_bound_within_on_convex
    ((model.extend center).loss datum)
    (MeasurePerformativeModelOn.extendGradient gradient center datum) smoothness
    domain hconvex hparameter' hgrad center candidate center.property candidate.property
  simpa [MeasurePerformativeModelOn.extend, MeasurePerformativeModelOn.extendGradient,
    center.property, candidate.property] using h

/-- The upper quadratic model averages under each feasible deployed law. -/
theorem frozen_risk_upper_model_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {smoothness modulus : ℝ}
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (deployed center candidate : domain)
    (hintegrable : Integrable (fun datum => gradient datum center)
      (model.dataLaw deployed : Measure Data)) :
    model.decoupledPerformativeRisk deployed candidate ≤
      model.decoupledPerformativeRisk deployed center +
        ⟪frozenGradient model gradient deployed center,
          (candidate : Parameter) - (center : Parameter)⟫_ℝ +
        smoothness / 2 * ‖(candidate : Parameter) - (center : Parameter)‖ ^ 2 := by
  change (∫ datum, model.loss datum candidate ∂(model.dataLaw deployed : Measure Data)) ≤ _
  rw [MeasurePerformativeModelOn.decoupledPerformativeRisk, frozenGradient,
    ← integral_affine_gradient_model (model.dataLaw deployed) (fun datum => model.loss datum center)
      (fun datum => gradient datum center) (model.loss_integrable deployed center) hintegrable]
  exact integral_mono (model.loss_integrable deployed candidate)
    (((model.loss_integrable deployed center).add (hintegrable.inner_const _)).add
      (integrable_const _))
    (fun datum => loss_upper_model_on model gradient hconvex hstrong hparameter datum center candidate)

/-- Expected gradients inherit the parameter-coordinate Lipschitz bound. -/
theorem frozen_gradient_parameter_lipschitz_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) {smoothness : ℝ}
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (deployed first second : domain)
    (hfirst : Integrable (fun datum => gradient datum first)
      (model.dataLaw deployed : Measure Data))
    (hsecond : Integrable (fun datum => gradient datum second)
      (model.dataLaw deployed : Measure Data)) :
    ‖frozenGradient model gradient deployed first - frozenGradient model gradient deployed second‖ ≤
      smoothness * ‖(first : Parameter) - (second : Parameter)‖ := by
  unfold frozenGradient
  rw [← integral_sub hfirst hsecond]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (ae_of_all (model.dataLaw deployed : Measure Data) (fun datum => hparameter datum first second))

/-- W₁ sensitivity controls the distribution-coordinate change of the
expected gradient at any fixed feasible evaluation parameter. -/
theorem frozen_gradient_law_lipschitz_on
    [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (smoothness : NNReal)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {sensitivity : ℝ} (hsensitive : model.IsWassersteinSensitive sensitivity)
    (first second evaluated : domain)
    (hfirst : Integrable (fun datum => gradient datum evaluated)
      (model.dataLaw first : Measure Data))
    (hsecond : Integrable (fun datum => gradient datum evaluated)
      (model.dataLaw second : Measure Data)) :
    ‖frozenGradient model gradient first evaluated - frozenGradient model gradient second evaluated‖ ≤
      (smoothness : ℝ) * (sensitivity * dist (first : Parameter) (second : Parameter)) := by
  obtain ⟨hfinite, hW⟩ := hsensitive first second
  have hLip : LipschitzWith smoothness (fun datum => gradient datum evaluated) := by
    apply LipschitzWith.of_dist_le_mul
    intro left right
    simpa only [dist_eq_norm] using hdata left right evaluated
  exact (ProbabilityCoupling.norm_integral_sub_le_lipschitz_wassersteinOneReal
    hLip hfirst hsecond hfinite).trans
      (mul_le_mul_of_nonneg_left hW smoothness.coe_nonneg)

/-- The integrated quadratic models identify the derivative of expected risk
along the feasible domain. This is a derivation from the two scalar bounds,
not an assumption permitting differentiation under expectation. -/
theorem frozen_risk_hasFDerivWithinAt_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {smoothness modulus : ℝ} (hsmoothness : 0 ≤ smoothness) (hmodulus : 0 ≤ modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (anchor deployed center : domain)
    (hintegrable : Integrable (fun datum => gradient datum center)
      (model.dataLaw deployed : Measure Data)) :
    HasFDerivWithinAt (measureDecoupledPerformativeRisk (model.extend anchor) deployed)
      (innerSL ℝ (frozenGradient model gradient deployed center)) domain (center : Parameter) := by
  apply DomainGradient.hasFDerivWithinAt_of_nonneg_quadratic_remainder
    _ _ _ _ hsmoothness
  intro candidate hcandidate
  let candidateOn : domain := ⟨candidate, hcandidate⟩
  rw [model.decoupledPerformativeRisk_extend anchor deployed center,
    model.decoupledPerformativeRisk_extend anchor deployed candidateOn]
  have hlower := frozen_risk_lower_model_on model gradient hstrong
    deployed center candidateOn hintegrable
  have hupper := frozen_risk_upper_model_on model gradient hconvex hstrong hparameter
    deployed center candidateOn hintegrable
  constructor
  · nlinarith [mul_nonneg hmodulus (sq_nonneg ‖(candidateOn : Parameter) - (center : Parameter)‖)]
  · linarith

/-- A constrained frozen-risk minimizer is characterized by its feasible
first-order inequalities. The derivative used for necessity is derived from
the averaged quadratic models. -/
theorem frozen_risk_minimizer_iff_first_order_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {smoothness modulus : ℝ} (hsmoothness : 0 ≤ smoothness) (hmodulus : 0 ≤ modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (deployed minimizer : domain)
    (hintegrable : Integrable (fun datum => gradient datum minimizer)
      (model.dataLaw deployed : Measure Data)) :
    (∀ candidate, model.decoupledPerformativeRisk deployed minimizer ≤
      model.decoupledPerformativeRisk deployed candidate) ↔
    ∀ candidate : domain, 0 ≤ ⟪frozenGradient model gradient deployed minimizer,
      (candidate : Parameter) - (minimizer : Parameter)⟫_ℝ := by
  constructor
  · intro hmin candidate
    have hminOn : IsMinOn
        (measureDecoupledPerformativeRisk (model.extend minimizer) deployed)
        domain (minimizer : Parameter) := by
      intro alternative halternative
      change measureDecoupledPerformativeRisk (model.extend minimizer) deployed minimizer ≤
        measureDecoupledPerformativeRisk (model.extend minimizer) deployed alternative
      rw [model.decoupledPerformativeRisk_extend minimizer deployed minimizer,
        model.decoupledPerformativeRisk_extend minimizer deployed ⟨alternative, halternative⟩]
      exact hmin ⟨alternative, halternative⟩
    have htangent : (candidate : Parameter) - (minimizer : Parameter) ∈
        posTangentConeAt domain (minimizer : Parameter) :=
      sub_mem_posTangentConeAt_of_segment_subset
        (hconvex.segment_subset minimizer.property candidate.property)
    exact hminOn.localize.hasFDerivWithinAt_nonneg
      (frozen_risk_hasFDerivWithinAt_on model gradient hconvex hsmoothness hmodulus
        hstrong hparameter minimizer deployed minimizer hintegrable) htangent
  · intro hfirst candidate
    have hlower := frozen_risk_lower_model_on model gradient hstrong
      deployed minimizer candidate hintegrable
    have hcurvature : 0 ≤ modulus / 2 *
        ‖(candidate : Parameter) - (minimizer : Parameter)‖ ^ 2 := by positivity
    linarith [hfirst candidate]

end PZMH20PerformativePrediction.DomainRelative
