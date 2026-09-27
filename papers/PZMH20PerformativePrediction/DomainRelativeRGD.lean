import PZMH20PerformativePrediction.DomainExpectedRisk
import PZMH20PerformativePrediction.GradientStepContraction
import PZMH20PerformativePrediction.AffineDomainGeometry
import PZMH20PerformativePrediction.DomainRGDContraction

/-!
# Repeated gradient descent on the source parameter domain

The update uses the expected pointwise gradient at the deployed parameter
and the actual Euclidean projection onto the closed convex feasible set.
Projection feasibility and nonexpansiveness are proved by the shared Hilbert
projection implementation, not supplied as additional model assumptions.
-/

namespace PZMH20PerformativePrediction.DomainRelative

open AppliedModelingLib MeasureTheory
open scoped InnerProductSpace

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [CompleteSpace Parameter] [MeasurableSpace Data]

/-- Projected repeated gradient descent with a domain-relative law and loss. -/
noncomputable def rgdUpdateOn
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) (stepSize : ℝ) : domain → domain :=
  fun deployed =>
    ⟨hilbertProjection domain hnonempty hclosed hconvex
      ((deployed : Parameter) - stepSize • frozenGradient model gradient deployed deployed),
      hilbertProjection_mem domain hnonempty hclosed hconvex _⟩

/-- Fixed points of the projected update are exactly the performatively
stable parameters. Both directions use the derived feasible derivative and
the variational characterization of the actual Euclidean projection. -/
theorem rgd_fixedPoint_iff_stable_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    {smoothness modulus : ℝ} (hsmoothness : 0 ≤ smoothness) (hmodulus : 0 ≤ modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (stepSize : ℝ) (hstepSize : 0 < stepSize) (parameter : domain)
    (hintegrable : Integrable (fun datum => gradient datum parameter)
      (model.dataLaw parameter : Measure Data)) :
    rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize parameter = parameter ↔
      model.IsPerformativelyStable parameter := by
  have hproject := isVariationalEuclideanProjectionOn_hilbertProjection
    domain hnonempty hclosed hconvex
  have hfirstOrder := frozen_risk_minimizer_iff_first_order_on model gradient hconvex
    hsmoothness hmodulus hstrong hparameter parameter parameter hintegrable
  constructor
  · intro hfixed
    apply hfirstOrder.mpr
    intro candidate
    apply projectedGradient_fixedPoint_firstOrder domain _ hproject
      (frozenGradient model gradient parameter parameter) parameter stepSize hstepSize
      (candidate := candidate) (hcandidate := candidate.property)
    exact congrArg Subtype.val hfixed
  · intro hstable
    apply Subtype.ext
    apply projectedGradient_fixedPoint_of_firstOrder domain _ hproject
      (frozenGradient model gradient parameter parameter) parameter parameter.property
      stepSize hstepSize
    intro candidate hcandidate
    exact hfirstOrder.mp hstable ⟨candidate, hcandidate⟩

/-- The contraction theorem for the actual projected update gives the unique
stable point, geometric convergence, and an explicit logarithmic entry time.
The analytic hypotheses here identify update fixed points with stability;
the model-specific contraction estimate is supplied separately. -/
theorem rgd_converges_of_contraction_on
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    {smoothness modulus : ℝ} (hsmoothness : 0 ≤ smoothness) (hmodulus : 0 ≤ modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        smoothness * ‖(first : Parameter) - (second : Parameter)‖)
    (hintegrable : ∀ parameter,
      Integrable (fun datum => gradient datum parameter) (model.dataLaw parameter : Measure Data))
    (stepSize : ℝ) (hstepSize : 0 < stepSize) {factor : NNReal}
    (hcontract : ContractingWith factor
      (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize))
    (initial : domain) :
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto
        (fun iteration => (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
          initial) Filter.atTop (nhds stable) ∧
      (∀ iteration,
        dist ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration] initial)
            stable ≤ (factor : ℝ) ^ iteration * dist initial stable) ∧
      ∀ radius > 0, ∀ iteration : ℕ,
        Real.log (dist initial stable / radius) / (1 - (factor : ℝ)) ≤ (iteration : ℝ) →
        dist ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration] initial)
          stable ≤ radius := by
  let update := rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize
  letI : IsClosed domain := hclosed
  letI : Nonempty domain := ⟨initial⟩
  let stable := hcontract.fixedPoint update
  have hfixed : Function.IsFixedPt update stable := hcontract.fixedPoint_isFixedPt
  have hstable : model.IsPerformativelyStable stable :=
    (rgd_fixedPoint_iff_stable_on model gradient hnonempty hclosed hconvex hsmoothness
      hmodulus hstrong hparameter stepSize hstepSize stable (hintegrable stable)).mp hfixed.eq
  have hunique : ∀ other, model.IsPerformativelyStable other → other = stable := by
    intro other hother
    exact hcontract.fixedPoint_unique'
      ((rgd_fixedPoint_iff_stable_on model gradient hnonempty hclosed hconvex hsmoothness
        hmodulus hstrong hparameter stepSize hstepSize other (hintegrable other)).mpr hother) hfixed
  have hrate : ∀ iteration, dist (update^[iteration] initial) stable ≤
      (factor : ℝ) ^ iteration * dist initial stable := by
    intro iteration
    have h := (hcontract.toLipschitzWith.iterate iteration).dist_le_mul initial stable
    rw [(hfixed.iterate iteration).eq] at h
    simpa only [NNReal.coe_pow] using h
  refine ⟨stable, hstable, hunique, hcontract.tendsto_iterate_fixedPoint initial, hrate, ?_⟩
  intro radius hradius iteration hiteration
  exact (hrate iteration).trans (pow_mul_le_of_log_div_one_sub_le factor.coe_nonneg
    hcontract.1 dist_nonneg hradius hiteration)

/-- On a nontrivial source domain, the pointwise A1 gradient bound and A2
lower model force the usual `gamma ≤ beta` compatibility.  The source does
not need to list it separately: a probability law supplies a datum at which
the two pointwise inequalities can be compared. -/
theorem modulus_le_smoothness_of_nontrivial_domain
    [MetricSpace Data] {domain : Set Parameter}
    (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) {smoothness : NNReal}
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        (smoothness : ℝ) * ‖(first : Parameter) - (second : Parameter)‖)
    {modulus : ℝ} (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hnot_subsingleton : ¬ Subsingleton domain) :
    modulus ≤ (smoothness : ℝ) := by
  classical
  letI : Nontrivial domain := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
  obtain ⟨first, second, hne⟩ := exists_pair_ne domain
  letI : IsProbabilityMeasure (model.dataLaw first : Measure Data) :=
    (model.dataLaw first).property
  obtain ⟨datum⟩ := nonempty_of_isProbabilityMeasure (model.dataLaw first : Measure Data)
  have hforward := hstrong.2 datum first second
  have hbackward := hstrong.2 datum second first
  have hmonotone :
      modulus * ‖(second : Parameter) - (first : Parameter)‖ ^ 2 ≤
        ⟪gradient datum second - gradient datum first,
          (second : Parameter) - (first : Parameter)⟫_ℝ := by
    rw [show (first : Parameter) - (second : Parameter) =
      -((second : Parameter) - (first : Parameter)) by abel,
      inner_neg_right, norm_neg] at hbackward
    rw [inner_sub_left]
    nlinarith only [hforward, hbackward]
  have hparameterBound := hparameter datum second first
  have hinner :
      ⟪gradient datum second - gradient datum first,
          (second : Parameter) - (first : Parameter)⟫_ℝ ≤
        (smoothness : ℝ) * ‖(second : Parameter) - (first : Parameter)‖ ^ 2 := by
    calc
      _ ≤ ‖gradient datum second - gradient datum first‖ *
          ‖(second : Parameter) - (first : Parameter)‖ :=
        real_inner_le_norm _ _
      _ ≤ ((smoothness : ℝ) * ‖(second : Parameter) - (first : Parameter)‖) *
          ‖(second : Parameter) - (first : Parameter)‖ :=
        mul_le_mul_of_nonneg_right hparameterBound (norm_nonneg _)
      _ = _ := by ring
  have hparameter_ne : (second : Parameter) ≠ (first : Parameter) := by
    intro heq
    exact hne (Subtype.ext heq.symm)
  have hnorm_pos : 0 < ‖(second : Parameter) - (first : Parameter)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hparameter_ne)
  nlinarith only [hmonotone, hinner, sq_pos_of_pos hnorm_pos]

/-- The source RGD conclusion is immediate on a singleton feasible domain.
This is the exceptional case in which A1/A2 do not themselves compare the
displayed smoothness and strong-convexity constants. -/
theorem rgd_converges_on_subsingleton
    [FiniteDimensional ℝ Parameter] [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) {smoothness : NNReal}
    {sensitivity modulus stepSize : ℝ} (initial : domain) [Subsingleton domain] :
    let factor := 1 - stepSize * (modulus * (smoothness : ℝ) /
      (modulus + (smoothness : ℝ)) -
        sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))
    (∀ first second,
      dist (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize first)
        (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize second) ≤
          factor * dist first second) ∧
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto
        (fun iteration => (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
          initial) Filter.atTop (nhds stable) ∧
      (∀ iteration,
        dist ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration] initial)
          stable ≤ factor ^ iteration * dist initial stable) ∧
      ∀ radius > 0, ∀ iteration : ℕ,
        Real.log (dist initial stable / radius) / (1 - factor) ≤ (iteration : ℝ) →
        dist ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration] initial)
          stable ≤ radius := by
  classical
  dsimp
  constructor
  · intro first second
    rw [Subsingleton.elim first second]
    simp
  refine ⟨initial, ?_, ?_, ?_, ?_, ?_⟩
  · intro candidate
    rw [Subsingleton.elim candidate initial]
  · intro other _
    exact Subsingleton.elim _ _
  · have hconstant :
        (fun iteration => (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
          initial) = fun _ => initial := by
        funext iteration
        exact Subsingleton.elim _ _
    rw [hconstant]
    exact tendsto_const_nhds
  · intro iteration
    rw [Subsingleton.elim ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
      initial) initial]
    simp
  · intro radius hradius iteration _
    rw [Subsingleton.elim ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
      initial) initial]
    simpa using hradius.le

/-- Theorem 3.8 on an arbitrary nonempty closed convex finite-dimensional
parameter domain. Its displayed factor and logarithmic iteration threshold
are obtained from a stronger tangent-gradient contraction estimate. -/
theorem rgd_converges_on
    [FiniteDimensional ℝ Parameter] [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) (hnonempty : domain.Nonempty)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) {smoothness : NNReal}
    (hparameter : ∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        (smoothness : ℝ) * ‖(first : Parameter) - (second : Parameter)‖)
    (hdata : ∀ first second parameter,
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    (hintegrable : ∀ deployed evaluated : domain,
      Integrable (fun datum => gradient datum evaluated) (model.dataLaw deployed : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (hmodulus : 0 < modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (initial : domain) :
    let factor := 1 - stepSize * (modulus * (smoothness : ℝ) /
      (modulus + (smoothness : ℝ)) -
        sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))
    (∀ first second,
      dist (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize first)
        (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize second) ≤
          factor * dist first second) ∧
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto
        (fun iteration => (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
          initial) Filter.atTop (nhds stable) ∧
      (∀ iteration,
        dist ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration] initial)
          stable ≤ factor ^ iteration * dist initial stable) ∧
      ∀ radius > 0, ∀ iteration : ℕ,
        Real.log (dist initial stable / radius) / (1 - factor) ≤ (iteration : ℝ) →
        dist ((rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration] initial)
          stable ≤ radius := by
  classical
  by_cases hsubsingleton : Subsingleton domain
  · letI : Subsingleton domain := hsubsingleton
    exact rgd_converges_on_subsingleton model gradient hnonempty hclosed hconvex initial
  have hmodulus_le := modulus_le_smoothness_of_nontrivial_domain
    model gradient hparameter hstrong hsubsingleton
  have hsmoothness : 0 < (smoothness : ℝ) := lt_of_lt_of_le hmodulus hmodulus_le
  have hfactor := DomainGradient.rgd_source_factor_bounds hsmoothness hmodulus
    hsensitivity hstepSize hstepSize_le hsensitivity_small
  let factor : NNReal := ⟨1 - stepSize * (modulus * (smoothness : ℝ) /
    (modulus + (smoothness : ℝ)) -
      sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ))), hfactor.1.1⟩
  have hcontract : ContractingWith factor
      (rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize) := by
    refine ⟨hfactor.1.2, LipschitzWith.of_dist_le_mul ?_⟩
    intro first second
    have hraw := norm_projected_frozenGradient_update_sub_le model gradient hclosed hconvex
      initial hparameter hdata hintegrable hsensitive hmodulus hmodulus_le hstrong
      (hilbertProjection domain hnonempty hclosed hconvex)
      (isVariationalEuclideanProjectionOn_hilbertProjection domain hnonempty hclosed hconvex)
      (hilbertProjection_lipschitzWith_one domain hnonempty hclosed hconvex)
      stepSize hstepSize.le (by simpa only [add_comm] using hstepSize_le) first second
    have hbound := hraw.trans (mul_le_mul_of_nonneg_right hfactor.2
      (norm_nonneg ((first : Parameter) - (second : Parameter))))
    simpa only [Subtype.dist_eq, dist_eq_norm, rgdUpdateOn] using hbound
  refine ⟨fun first second => hcontract.toLipschitzWith.dist_le_mul first second, ?_⟩
  exact rgd_converges_of_contraction_on model gradient hnonempty hclosed hconvex
    smoothness.coe_nonneg hmodulus.le hstrong hparameter (fun parameter => hintegrable parameter parameter)
    stepSize hstepSize hcontract initial

end PZMH20PerformativePrediction.DomainRelative
