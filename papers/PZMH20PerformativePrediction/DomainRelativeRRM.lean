import AppliedModelingLib.GameTheory.PerformativePrediction
import Mathlib.Analysis.Calculus.MeanValue
import PZMH20PerformativePrediction.LogarithmicBurnIn

/-!
# Repeated risk minimization on the feasible parameter set

The loss increment between two feasible parameters is Lipschitz in the data
with constant `β` times their distance. Combining its transport bound with
quadratic growth at two constrained minimizers gives the RRM contraction
without differentiating an expectation. All gradient assumptions are within
the feasible set.
-/

namespace PZMH20PerformativePrediction.DomainRelative

open AppliedModelingLib MeasureTheory
open scoped InnerProductSpace

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [CompleteSpace Parameter] [MetricSpace Data]

/-- The data-Lipschitz gradient controls loss increments along a convex
parameter set, including its boundary. -/
theorem loss_increment_lipschitz
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {first second : Parameter} (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    LipschitzWith (smoothness * ‖second - first‖₊)
      (fun datum => loss datum second - loss datum first) := by
  refine LipschitzWith.of_dist_le_mul fun left right => ?_
  have hderiv : ∀ parameter ∈ domain,
      HasFDerivWithinAt (fun theta => loss left theta - loss right theta)
        ((InnerProductSpace.toDual ℝ Parameter)
          (gradient left parameter - gradient right parameter)) domain parameter := by
    intro parameter hparameter
    simpa only [map_sub] using
      (hgradient left parameter hparameter).hasFDerivWithinAt.sub
        (hgradient right parameter hparameter).hasFDerivWithinAt
  have hbound : ∀ parameter ∈ domain,
      ‖(InnerProductSpace.toDual ℝ Parameter)
          (gradient left parameter - gradient right parameter)‖ ≤
        (smoothness : ℝ) * dist left right := by
    intro parameter hparameter
    simpa only [LinearIsometryEquiv.norm_map] using hdata left right parameter hparameter
  have hmean := hconvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound hfirst hsecond
  rw [Real.norm_eq_abs] at hmean
  rw [Real.dist_eq]
  simpa only [NNReal.coe_mul, coe_nnnorm,
    show loss left second - loss right second - (loss left first - loss right first) =
      (loss left second - loss left first) - (loss right second - loss right first) by ring,
    mul_right_comm] using hmean

variable [MeasurableSpace Data]

/-- Transport of a loss increment needs integrability of losses, not of
gradients and not differentiation under the probability integral. -/
theorem abs_risk_increment_shift_le
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    (deployedLeft deployedRight first second : Parameter)
    (hfirst : first ∈ domain) (hsecond : second ∈ domain)
    (hfinite : (ProbabilityCoupling.expectedDistanceCosts
      (model.dataLaw deployedLeft) (model.dataLaw deployedRight)).Nonempty) :
    |(measureDecoupledPerformativeRisk model deployedLeft second -
        measureDecoupledPerformativeRisk model deployedLeft first) -
      (measureDecoupledPerformativeRisk model deployedRight second -
        measureDecoupledPerformativeRisk model deployedRight first)| ≤
      ((smoothness : ℝ) * ‖second - first‖) *
        ProbabilityCoupling.wassersteinOneReal
          (model.dataLaw deployedLeft) (model.dataLaw deployedRight) hfinite := by
  have htransport := ProbabilityCoupling.norm_integral_sub_le_lipschitz_wassersteinOneReal
    (μ := model.dataLaw deployedLeft) (ν := model.dataLaw deployedRight)
    (loss_increment_lipschitz model.loss gradient domain hconvex smoothness
      hgradient hdata hfirst hsecond)
    ((model.loss_integrable deployedLeft second).sub
      (model.loss_integrable deployedLeft first))
    ((model.loss_integrable deployedRight second).sub
      (model.loss_integrable deployedRight first)) hfinite
  simpa only [measureDecoupledPerformativeRisk, integral_sub
    (model.loss_integrable deployedLeft second) (model.loss_integrable deployedLeft first),
    integral_sub (model.loss_integrable deployedRight second)
      (model.loss_integrable deployedRight first),
    Real.norm_eq_abs, NNReal.coe_mul, coe_nnnorm] using htransport

/-- Two frozen-risk minimizers are `β/γ`-Lipschitz in their data laws in W₁.
The proof uses only on-domain A1/A2 and therefore also covers constrained
empirical minimizers. -/
theorem norm_minimizers_sub_le_wasserstein
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : AppliedModelingLib.IsMeasurePointwiseGradientStronglyConvexOn
      model gradient domain modulus)
    (deployedLeft deployedRight first second : Parameter)
    (hfirst : first ∈ domain) (hsecond : second ∈ domain)
    (hminLeft : ∀ candidate ∈ domain,
      measureDecoupledPerformativeRisk model deployedLeft first ≤
        measureDecoupledPerformativeRisk model deployedLeft candidate)
    (hminRight : ∀ candidate ∈ domain,
      measureDecoupledPerformativeRisk model deployedRight second ≤
        measureDecoupledPerformativeRisk model deployedRight candidate)
    (hfinite : (ProbabilityCoupling.expectedDistanceCosts
      (model.dataLaw deployedLeft) (model.dataLaw deployedRight)).Nonempty) :
    ‖first - second‖ ≤ (smoothness : ℝ) / modulus *
      ProbabilityCoupling.wassersteinOneReal
        (model.dataLaw deployedLeft) (model.dataLaw deployedRight) hfinite := by
  have hleft :=
    (strongConvexOn_measureDecoupledPerformativeRisk_of_pointwiseGradientStronglyConvexOn
      model gradient domain hconvex hstrong deployedLeft).quadratic_gap_le_of_isMinOn
        hfirst hsecond hminLeft
  have hright :=
    (strongConvexOn_measureDecoupledPerformativeRisk_of_pointwiseGradientStronglyConvexOn
      model gradient domain hconvex hstrong deployedRight).quadratic_gap_le_of_isMinOn
        hsecond hfirst hminRight
  have hshift := abs_risk_increment_shift_le model gradient domain hconvex smoothness
    hgradient hdata deployedLeft deployedRight first second hfirst hsecond hfinite
  rw [norm_sub_rev second first] at hleft hshift
  have hquad : modulus * ‖first - second‖ ^ 2 ≤
      ((smoothness : ℝ) * ‖first - second‖) *
        ProbabilityCoupling.wassersteinOneReal
          (model.dataLaw deployedLeft) (model.dataLaw deployedRight) hfinite := by
    have hupper := (abs_le.mp hshift).2
    linarith
  have hw : 0 ≤ ProbabilityCoupling.wassersteinOneReal
      (model.dataLaw deployedLeft) (model.dataLaw deployedRight) hfinite := by
    apply le_csInf hfinite
    rintro cost ⟨coupling, _, rfl⟩
    exact integral_nonneg fun _ => dist_nonneg
  by_cases heq : ‖first - second‖ = 0
  · rw [heq]
    positivity
  have hpos : 0 < ‖first - second‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm heq)
  have hcancel : modulus * ‖first - second‖ ≤ (smoothness : ℝ) *
      ProbabilityCoupling.wassersteinOneReal
        (model.dataLaw deployedLeft) (model.dataLaw deployedRight) hfinite := by
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hquad]
  calc
    ‖first - second‖ ≤ ((smoothness : ℝ) *
        ProbabilityCoupling.wassersteinOneReal
          (model.dataLaw deployedLeft) (model.dataLaw deployedRight) hfinite) / modulus :=
      (le_div_iff₀ hmodulus).2 (by nlinarith only [hcancel])
    _ = _ := by ring

/-- Theorem 3.5(a) for laws and losses defined only on the source parameter
set. Parameter-coordinate gradient smoothness is not needed for this bound. -/
theorem norm_rrm_sub_le_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    (smoothness : NNReal)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus sensitivity : ℝ} (hmodulus : 0 < modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      model.decoupledPerformativeRisk deployed (update deployed) ≤
        model.decoupledPerformativeRisk deployed candidate)
    (first second : domain) :
    ‖(update first : Parameter) - (update second : Parameter)‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) *
        ‖(first : Parameter) - (second : Parameter)‖ := by
  classical
  rcases hsensitive first second with ⟨hfinite, htransport⟩
  have hgrad : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt ((model.extend first).loss datum)
        (MeasurePerformativeModelOn.extendGradient gradient first datum parameter)
        domain parameter := by
    intro datum parameter hparameter
    simpa [HasGradientWithinAt, MeasurePerformativeModelOn.extend,
      MeasurePerformativeModelOn.extendGradient, hparameter] using
      hstrong.1 datum (⟨parameter, hparameter⟩ : domain)
  have hdata' : ∀ left right parameter, parameter ∈ domain →
      ‖MeasurePerformativeModelOn.extendGradient gradient first left parameter -
        MeasurePerformativeModelOn.extendGradient gradient first right parameter‖ ≤
        (smoothness : ℝ) * dist left right := by
    intro left right parameter hparameter
    simpa [MeasurePerformativeModelOn.extendGradient, hparameter] using
      hdata left right (⟨parameter, hparameter⟩ : domain)
  have hminimum : ∀ deployed : domain, ∀ candidate ∈ domain,
      measureDecoupledPerformativeRisk (model.extend first) deployed (update deployed) ≤
        measureDecoupledPerformativeRisk (model.extend first) deployed candidate := by
    intro deployed candidate hcandidate
    simpa only [model.decoupledPerformativeRisk_extend first deployed (update deployed),
      model.decoupledPerformativeRisk_extend first deployed ⟨candidate, hcandidate⟩] using
      hrrm deployed ⟨candidate, hcandidate⟩
  have hfinite' : (ProbabilityCoupling.expectedDistanceCosts
      ((model.extend first).dataLaw first) ((model.extend first).dataLaw second)).Nonempty := by
    simpa [MeasurePerformativeModelOn.extend, first.property, second.property] using hfinite
  have hbound := norm_minimizers_sub_le_wasserstein (model.extend first)
    (MeasurePerformativeModelOn.extendGradient gradient first) domain hconvex smoothness
    hgrad hdata' hmodulus
    (model.isMeasurePointwiseGradientStronglyConvexOn_extend gradient first hstrong)
    first second (update first) (update second) (update first).property (update second).property
    (hminimum first) (hminimum second) hfinite'
  have hbound' : ‖(update first : Parameter) - (update second : Parameter)‖ ≤
      (smoothness : ℝ) / modulus *
        ProbabilityCoupling.wassersteinOneReal (model.dataLaw first) (model.dataLaw second)
          hfinite := by
    simpa [MeasurePerformativeModelOn.extend, first.property, second.property] using hbound
  calc
    ‖(update first : Parameter) - (update second : Parameter)‖ ≤
        (smoothness : ℝ) / modulus *
          ProbabilityCoupling.wassersteinOneReal (model.dataLaw first) (model.dataLaw second)
            hfinite := hbound'
    _ ≤ (smoothness : ℝ) / modulus *
        (sensitivity * dist (first : Parameter) (second : Parameter)) :=
      mul_le_mul_of_nonneg_left htransport (by positivity)
    _ = _ := by rw [dist_eq_norm]; ring

omit [CompleteSpace Parameter] [MetricSpace Data] in
/-- Strong convexity identifies stability with the fixed points of any exact
constrained risk-minimization selection. -/
theorem rrm_fixedPoint_iff_stable_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hconvex : Convex ℝ domain)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      model.decoupledPerformativeRisk deployed (update deployed) ≤
        model.decoupledPerformativeRisk deployed candidate)
    (parameter : domain) :
    update parameter = parameter ↔ model.IsPerformativelyStable parameter := by
  constructor
  · intro hfixed candidate
    simpa only [hfixed] using hrrm parameter candidate
  · intro hstable
    have hstrongRisk :=
      strongConvexOn_measureDecoupledPerformativeRisk_of_pointwiseGradientStronglyConvexOn
        (model.extend parameter) (MeasurePerformativeModelOn.extendGradient gradient parameter)
        domain hconvex
        (model.isMeasurePointwiseGradientStronglyConvexOn_extend gradient parameter hstrong)
        parameter
    have hmin : IsMinOn
        (measureDecoupledPerformativeRisk (model.extend parameter) parameter)
        domain (update parameter) := by
      intro candidate hcandidate
      change measureDecoupledPerformativeRisk (model.extend parameter) parameter
        (update parameter) ≤
          measureDecoupledPerformativeRisk (model.extend parameter) parameter candidate
      simpa only [model.decoupledPerformativeRisk_extend parameter parameter (update parameter),
        model.decoupledPerformativeRisk_extend parameter parameter ⟨candidate, hcandidate⟩] using
        hrrm parameter ⟨candidate, hcandidate⟩
    have hstable' := model.isMeasurePerformativelyStableOn_extend parameter parameter hstable
    exact Subtype.ext ((hstrongRisk.strictConvexOn hmodulus).eq_of_isMinOn
      hmin hstable'.2 (update parameter).property parameter.property)

/-- Theorem 3.5(b) on the source domain: the exact RRM iteration converges
geometrically to its unique stable point. No off-domain hypothesis or
differentiation-under-expectation premise is used. -/
theorem rrm_converges_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hclosed : IsClosed domain)
    (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus sensitivity : ℝ} (hmodulus : 0 < modulus) (hsensitivity : 0 ≤ sensitivity)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      model.decoupledPerformativeRisk deployed (update deployed) ≤
        model.decoupledPerformativeRisk deployed candidate)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : domain) :
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, dist (update^[iteration] initial) stable ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * dist initial stable := by
  let factor : NNReal := ⟨sensitivity * (smoothness : ℝ) / modulus, by positivity⟩
  have hcontract : ContractingWith factor update := by
    refine ⟨hfactor, LipschitzWith.of_dist_le_mul ?_⟩
    intro first second
    simpa only [Subtype.dist_eq, dist_eq_norm] using
      norm_rrm_sub_le_on model gradient hconvex smoothness hdata hmodulus hstrong
        hsensitive update hrrm first second
  letI : IsClosed domain := hclosed
  letI : Nonempty domain := ⟨initial⟩
  let stable := hcontract.fixedPoint update
  have hfixed : Function.IsFixedPt update stable := hcontract.fixedPoint_isFixedPt
  refine ⟨stable,
    (rrm_fixedPoint_iff_stable_on model gradient hconvex hmodulus hstrong update hrrm stable).mp
      hfixed.eq, ?_, hcontract.tendsto_iterate_fixedPoint initial, ?_⟩
  · intro other hother
    exact hcontract.fixedPoint_unique'
      ((rrm_fixedPoint_iff_stable_on model gradient hconvex hmodulus hstrong
        update hrrm other).mpr hother) hfixed
  · intro iteration
    have hrate := (hcontract.toLipschitzWith.iterate iteration).dist_le_mul initial stable
    rw [(hfixed.iterate iteration).eq] at hrate
    simpa only [NNReal.coe_pow] using hrate

/-- The full RRM conclusion includes the source's explicit logarithmic
iteration threshold in addition to its geometric estimate. -/
theorem rrm_converges_on_with_log_bound
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hclosed : IsClosed domain)
    (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus sensitivity : ℝ} (hmodulus : 0 < modulus) (hsensitivity : 0 ≤ sensitivity)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      model.decoupledPerformativeRisk deployed (update deployed) ≤
        model.decoupledPerformativeRisk deployed candidate)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : domain) :
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      (∀ iteration, dist (update^[iteration] initial) stable ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * dist initial stable) ∧
      ∀ radius > 0, ∀ iteration : ℕ,
        Real.log (dist initial stable / radius) /
            (1 - sensitivity * (smoothness : ℝ) / modulus) ≤ (iteration : ℝ) →
          dist (update^[iteration] initial) stable ≤ radius := by
  obtain ⟨stable, hstable, hunique, hlimit, hrate⟩ := rrm_converges_on
    model gradient hclosed hconvex smoothness hdata hmodulus hsensitivity
    hstrong hsensitive update hrrm hfactor initial
  refine ⟨stable, hstable, hunique, hlimit, hrate, ?_⟩
  intro radius hradius iteration hiteration
  exact (hrate iteration).trans (pow_mul_le_of_log_div_one_sub_le
    (by positivity) hfactor dist_nonneg hradius hiteration)

end PZMH20PerformativePrediction.DomainRelative
