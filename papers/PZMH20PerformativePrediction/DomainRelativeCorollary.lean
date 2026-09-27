import PZMH20PerformativePrediction.DomainRelativeRRM

/-!
# Stable classifiers on the feasible parameter domain

Stability bounds the learner's risk by the loss of a performative optimum
under the stable law. Only the induced distribution changes in the remaining
comparison. Together with the optimal-to-stable distance estimate, this gives
the objective guarantee in Corollary 5.1 on the source domain.
-/

namespace PZMH20PerformativePrediction.DomainRelative

open AppliedModelingLib MeasureTheory

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [MeasurableSpace Data] [MetricSpace Data]

/-- Stability and transport give a quadratic-in-sensitivity objective gap.
This estimate is stronger than the displayed Corollary 5.1 bound. -/
theorem stable_risk_gap_le_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {modulus sensitivity : ℝ} (hmodulus : 0 < modulus) (hsensitivity : 0 ≤ sensitivity)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    {dataConstant : NNReal} (hdataLoss : model.IsDataLossLipschitz dataConstant)
    (optimal stable : domain) (hoptimal : model.IsPerformativelyOptimal optimal)
    (hstable : model.IsPerformativelyStable stable) :
    model.performativeRisk stable - model.performativeRisk optimal ≤
      2 * (dataConstant : ℝ) ^ 2 * sensitivity ^ 2 / modulus := by
  rcases hsensitive stable optimal with ⟨hfinite, hW⟩
  have htransport := ProbabilityCoupling.norm_integral_sub_le_lipschitz_wassersteinOneReal
    (μ := model.dataLaw stable) (ν := model.dataLaw optimal)
    (hdataLoss optimal) (model.loss_integrable stable optimal)
    (model.loss_integrable optimal optimal) hfinite
  have hshift : model.decoupledPerformativeRisk stable optimal -
      model.decoupledPerformativeRisk optimal optimal ≤
        (dataConstant : ℝ) * (sensitivity * dist (stable : Parameter) (optimal : Parameter)) := by
    have hupper := le_trans (le_abs_self _) htransport
    exact hupper.trans (mul_le_mul_of_nonneg_left hW dataConstant.coe_nonneg)
  have hdist := model.norm_optimal_sub_stable_le_of_strongConvex_wasserstein
    gradient hconvex hmodulus hstrong hdataLoss hsensitivity hsensitive
      optimal stable hoptimal hstable
  have hdist' : dist (stable : Parameter) (optimal : Parameter) ≤
      2 * (dataConstant : ℝ) * sensitivity / modulus := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  calc
    model.performativeRisk stable - model.performativeRisk optimal ≤
        model.decoupledPerformativeRisk stable optimal -
          model.decoupledPerformativeRisk optimal optimal :=
      sub_le_sub_right (hstable optimal) _
    _ ≤ (dataConstant : ℝ) *
        (sensitivity * dist (stable : Parameter) (optimal : Parameter)) := hshift
    _ ≤ (dataConstant : ℝ) *
        (sensitivity * (2 * (dataConstant : ℝ) * sensitivity / modulus)) := by
      gcongr
    _ = _ := by ring

/-- The source's objective-gap constant follows from the stronger stable-law
comparison, so no off-domain parameter-Lipschitz premise is needed. -/
theorem stable_risk_gap_le_source_bound_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {modulus sensitivity : ℝ} (hmodulus : 0 < modulus) (hsensitivity : 0 ≤ sensitivity)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    {dataConstant : NNReal} (hdataLoss : model.IsDataLossLipschitz dataConstant)
    (parameterConstant : NNReal)
    (optimal stable : domain) (hoptimal : model.IsPerformativelyOptimal optimal)
    (hstable : model.IsPerformativelyStable stable) :
    model.performativeRisk stable - model.performativeRisk optimal ≤
      2 * (dataConstant : ℝ) * sensitivity *
        ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus := by
  apply (stable_risk_gap_le_on model gradient hconvex hmodulus hsensitivity hstrong
    hsensitive hdataLoss optimal stable hoptimal hstable).trans
  apply div_le_div_of_nonneg_right _ hmodulus.le
  nlinarith [mul_nonneg (mul_nonneg dataConstant.coe_nonneg hsensitivity)
    parameterConstant.coe_nonneg]

/-- RRM convergence and the source's stable-versus-optimal risk bound, with
all model assumptions confined to the feasible parameter domain. -/
theorem rrm_converges_with_objective_gap_on
    [CompleteSpace Parameter]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hclosed : IsClosed domain)
    (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus sensitivity : ℝ} (hmodulus : 0 < modulus) (hsensitivity : 0 ≤ sensitivity)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    {dataConstant : NNReal} (hdataLoss : model.IsDataLossLipschitz dataConstant)
    (parameterConstant : NNReal) (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      model.decoupledPerformativeRisk deployed (update deployed) ≤
        model.decoupledPerformativeRisk deployed candidate)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial optimal : domain) (hoptimal : model.IsPerformativelyOptimal optimal) :
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      (∀ iteration, dist (update^[iteration] initial) stable ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * dist initial stable) ∧
      model.performativeRisk stable - model.performativeRisk optimal ≤
        2 * (dataConstant : ℝ) * sensitivity *
          ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus := by
  obtain ⟨stable, hstable, hunique, hlimit, hrate⟩ := rrm_converges_on
    model gradient hclosed hconvex smoothness hdata hmodulus hsensitivity
    hstrong hsensitive update hrrm hfactor initial
  exact ⟨stable, hstable, hunique, hlimit, hrate,
    stable_risk_gap_le_source_bound_on model gradient hconvex hmodulus hsensitivity
      hstrong hsensitive hdataLoss parameterConstant optimal stable hoptimal hstable⟩

end PZMH20PerformativePrediction.DomainRelative
