import PZMH20PerformativePrediction.DomainRelativeRRM
import AppliedModelingLib.Foundations.Probability.EmpiricalMeasure

/-!
# Empirical minimizer perturbation under Wasserstein error

For two arbitrary probability laws, constrained minimizers of the corresponding
expected losses differ by at most `β / γ` times their `W₁` distance.  The proof
uses the source A1 data-coordinate gradient bound and A2 strong convexity on
the feasible domain.  It transports a *loss increment* between the laws, so it
does not differentiate an expectation and does not replace the linear bound
by a loss-Lipschitz square-root estimate.
-/

namespace PZMH20PerformativePrediction.EmpiricalMinimizerPerturbation

open AppliedModelingLib MeasureTheory
open scoped InnerProductSpace ENNReal

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]

/-- Expected loss under an arbitrary probability law. -/
noncomputable def expectedRisk (law : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (parameter : Parameter) : ℝ :=
  ∫ datum, loss datum parameter ∂(law : Measure Data)

/-- The source A2 quadratic lower model, restricted to the feasible domain. -/
def IsPointwiseGradientStronglyConvexOn
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (modulus : ℝ) : Prop :=
  ∀ datum, ∀ center ∈ domain, ∀ candidate ∈ domain,
    loss datum candidate ≥
      loss datum center + ⟪gradient datum center, candidate - center⟫_ℝ +
        modulus / 2 * ‖candidate - center‖ ^ 2

omit [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data] in
/-- The A2 lower model yields ordinary pointwise strong convexity on the same
convex feasible domain. -/
theorem strongConvexOn_loss_of_pointwiseGradientStronglyConvexOn
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) {modulus : ℝ}
    (hstrong : IsPointwiseGradientStronglyConvexOn loss gradient domain modulus)
    (datum : Data) : StrongConvexOn domain modulus (loss datum) := by
  refine ⟨hconvex, ?_⟩
  intro first hfirst second hsecond a b ha hb hab
  let center := a • first + b • second
  have hcenter : center ∈ domain := hconvex hfirst hsecond ha hb hab
  have hfirst_lower := hstrong datum center hcenter first hfirst
  have hsecond_lower := hstrong datum center hcenter second hsecond
  have hfirst_weighted := mul_le_mul_of_nonneg_left hfirst_lower ha
  have hsecond_weighted := mul_le_mul_of_nonneg_left hsecond_lower hb
  have hfirst_sub : first - center = b • (first - second) := by
    dsimp [center]
    have : 1 - a = b := by linarith
    rw [← this]
    module
  have hsecond_sub : second - center = -a • (first - second) := by
    dsimp [center]
    have : 1 - b = a := by linarith
    rw [← this]
    module
  rw [hfirst_sub, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hb] at hfirst_weighted
  rw [hsecond_sub, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg ha] at hsecond_weighted
  simp only [smul_eq_mul]
  change loss datum center ≤
    a * loss datum first + b * loss datum second -
      a * b * (modulus / 2 * ‖first - second‖ ^ 2)
  have hsum := add_le_add hfirst_weighted hsecond_weighted
  have halgebra :
      a * (loss datum center +
          b * ⟪gradient datum center, first - second⟫_ℝ +
          modulus / 2 * (b * ‖first - second‖) ^ 2) +
        b * (loss datum center -
          a * ⟪gradient datum center, first - second⟫_ℝ +
          modulus / 2 * (a * ‖first - second‖) ^ 2) =
        loss datum center +
          a * b * (modulus / 2 * ‖first - second‖ ^ 2) := by
    have : b = 1 - a := by linarith
    rw [this]
    ring
  have hsum' :
      loss datum center + a * b * (modulus / 2 * ‖first - second‖ ^ 2) ≤
        a * loss datum first + b * loss datum second := by
    rw [← halgebra]
    convert hsum using 1
    ring
  linarith

omit [CompleteSpace Parameter] [MetricSpace Data] in
/-- Pointwise A2 remains strongly convex after expectation.  Only loss
integrability is used; the gradient terms already canceled pointwise. -/
theorem strongConvexOn_expectedRisk
    (law : ProbabilityMeasure Data) (loss : Data → Parameter → ℝ)
    (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) {modulus : ℝ}
    (hstrong : IsPointwiseGradientStronglyConvexOn loss gradient domain modulus)
    (hintegrable : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (law : Measure Data)) :
    StrongConvexOn domain modulus (expectedRisk law loss) := by
  refine ⟨hconvex, ?_⟩
  intro first hfirst second hsecond a b ha hb hab
  let curvature := a * b * (modulus / 2 * ‖first - second‖ ^ 2)
  have hcombined : a • first + b • second ∈ domain :=
    hconvex hfirst hsecond ha hb hab
  have hfirst_integrable := hintegrable first hfirst
  have hsecond_integrable := hintegrable second hsecond
  have hcombined_integrable := hintegrable (a • first + b • second) hcombined
  have hconstant_integrable : Integrable (fun _ : Data => curvature) (law : Measure Data) :=
    integrable_const _
  have hright_integrable : Integrable (fun datum =>
      a * loss datum first + b * loss datum second - curvature) (law : Measure Data) :=
    ((hfirst_integrable.const_mul a).add
      (hsecond_integrable.const_mul b)).sub hconstant_integrable
  have haverage := integral_mono_ae hcombined_integrable hright_integrable
    (ae_of_all (law : Measure Data) fun datum => by
      simpa only [smul_eq_mul, curvature] using
        (strongConvexOn_loss_of_pointwiseGradientStronglyConvexOn
          loss gradient domain hconvex hstrong datum).2 hfirst hsecond ha hb hab)
  change ∫ datum, loss datum (a • first + b • second) ∂(law : Measure Data) ≤
    a * (∫ datum, loss datum first ∂(law : Measure Data)) +
      b * (∫ datum, loss datum second ∂(law : Measure Data)) - curvature
  calc
    ∫ datum, loss datum (a • first + b • second) ∂(law : Measure Data) ≤
        ∫ datum, a * loss datum first + b * loss datum second - curvature
          ∂(law : Measure Data) := haverage
    _ = a * (∫ datum, loss datum first ∂(law : Measure Data)) +
          b * (∫ datum, loss datum second ∂(law : Measure Data)) - curvature := by
      have hsplit_sub :
          (∫ datum, a * loss datum first + b * loss datum second - curvature
              ∂(law : Measure Data)) =
            (∫ datum, a * loss datum first + b * loss datum second
              ∂(law : Measure Data)) -
              ∫ _ : Data, curvature ∂(law : Measure Data) :=
        integral_sub ((hfirst_integrable.const_mul a).add
          (hsecond_integrable.const_mul b)) hconstant_integrable
      have hsplit_add :
          (∫ datum, a * loss datum first + b * loss datum second
              ∂(law : Measure Data)) =
            (∫ datum, a * loss datum first ∂(law : Measure Data)) +
              ∫ datum, b * loss datum second ∂(law : Measure Data) :=
        integral_add (hfirst_integrable.const_mul a) (hsecond_integrable.const_mul b)
      rw [hsplit_sub, hsplit_add, integral_const_mul, integral_const_mul,
        integral_const, probReal_univ, one_smul]

/-- A1 transports the loss increment between two arbitrary laws. -/
theorem abs_expectedRisk_increment_shift_le
    (firstLaw secondLaw : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    (hintegrableFirst : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (firstLaw : Measure Data))
    (hintegrableSecond : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (secondLaw : Measure Data))
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain)
    (hfinite : (ProbabilityCoupling.expectedDistanceCosts firstLaw secondLaw).Nonempty) :
    |(expectedRisk firstLaw loss second - expectedRisk firstLaw loss first) -
      (expectedRisk secondLaw loss second - expectedRisk secondLaw loss first)| ≤
      ((smoothness : ℝ) * ‖second - first‖) *
        ProbabilityCoupling.wassersteinOneReal firstLaw secondLaw hfinite := by
  have htransport := ProbabilityCoupling.norm_integral_sub_le_lipschitz_wassersteinOneReal
    (PZMH20PerformativePrediction.DomainRelative.loss_increment_lipschitz
      loss gradient domain hconvex smoothness hgradient hdata hfirst hsecond)
    ((hintegrableFirst second hsecond).sub (hintegrableFirst first hfirst))
    ((hintegrableSecond second hsecond).sub (hintegrableSecond first hfirst)) hfinite
  simpa only [expectedRisk,
    integral_sub (hintegrableFirst second hsecond) (hintegrableFirst first hfirst),
    integral_sub (hintegrableSecond second hsecond) (hintegrableSecond first hfirst),
    Real.norm_eq_abs, NNReal.coe_mul, coe_nnnorm] using htransport

/--
Constrained minimizers under arbitrary probability laws are `β / γ`-Lipschitz
in `W₁`.  No gradient expectation or differentiation under the integral is
used.
-/
theorem norm_minimizers_sub_le_wasserstein
    (firstLaw secondLaw : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvexOn loss gradient domain modulus)
    (hintegrableFirst : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (firstLaw : Measure Data))
    (hintegrableSecond : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (secondLaw : Measure Data))
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain)
    (hminFirst : ∀ candidate ∈ domain,
      expectedRisk firstLaw loss first ≤ expectedRisk firstLaw loss candidate)
    (hminSecond : ∀ candidate ∈ domain,
      expectedRisk secondLaw loss second ≤ expectedRisk secondLaw loss candidate)
    (hfinite : (ProbabilityCoupling.expectedDistanceCosts firstLaw secondLaw).Nonempty) :
    ‖first - second‖ ≤ (smoothness : ℝ) / modulus *
      ProbabilityCoupling.wassersteinOneReal firstLaw secondLaw hfinite := by
  have hleft := (strongConvexOn_expectedRisk firstLaw loss gradient domain hconvex hstrong
    hintegrableFirst).quadratic_gap_le_of_isMinOn hfirst hsecond hminFirst
  have hright := (strongConvexOn_expectedRisk secondLaw loss gradient domain hconvex hstrong
    hintegrableSecond).quadratic_gap_le_of_isMinOn hsecond hfirst hminSecond
  have hshift := abs_expectedRisk_increment_shift_le firstLaw secondLaw loss gradient domain
    hconvex smoothness hgradient hdata hintegrableFirst hintegrableSecond
    first second hfirst hsecond hfinite
  rw [norm_sub_rev second first] at hleft hshift
  have hquad : modulus * ‖first - second‖ ^ 2 ≤
      ((smoothness : ℝ) * ‖first - second‖) *
        ProbabilityCoupling.wassersteinOneReal firstLaw secondLaw hfinite := by
    have hupper := (abs_le.mp hshift).2
    linarith
  have hw : 0 ≤ ProbabilityCoupling.wassersteinOneReal firstLaw secondLaw hfinite := by
    apply le_csInf hfinite
    rintro cost ⟨coupling, _, rfl⟩
    exact integral_nonneg fun _ => dist_nonneg
  by_cases heq : ‖first - second‖ = 0
  · rw [heq]
    positivity
  have hpos : 0 < ‖first - second‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm heq)
  have hcancel : modulus * ‖first - second‖ ≤ (smoothness : ℝ) *
      ProbabilityCoupling.wassersteinOneReal firstLaw secondLaw hfinite := by
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hquad]
  calc
    ‖first - second‖ ≤ ((smoothness : ℝ) *
        ProbabilityCoupling.wassersteinOneReal firstLaw secondLaw hfinite) / modulus :=
      (le_div_iff₀ hmodulus).2 (by nlinarith only [hcancel])
    _ = _ := by ring

/-- The arbitrary-law theorem specialized to the empirical probability measure
of a nonempty finite sample. -/
theorem norm_empiricalMinimizer_sub_populationMinimizer_le_wasserstein
    {sampleCount : ℕ} (hcount : 0 < sampleCount) (sample : Fin sampleCount → Data)
    (population : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvexOn loss gradient domain modulus)
    (hempirical_integrable : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter)
        (empiricalSampleProbabilityMeasureOfPos hcount sample : Measure Data))
    (hpopulation_integrable : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (population : Measure Data))
    (empiricalMinimizer populationMinimizer : Parameter)
    (hempirical_mem : empiricalMinimizer ∈ domain)
    (hpopulation_mem : populationMinimizer ∈ domain)
    (hempirical_min : ∀ candidate ∈ domain,
      expectedRisk (empiricalSampleProbabilityMeasureOfPos hcount sample) loss
          empiricalMinimizer ≤
        expectedRisk (empiricalSampleProbabilityMeasureOfPos hcount sample) loss candidate)
    (hpopulation_min : ∀ candidate ∈ domain,
      expectedRisk population loss populationMinimizer ≤
        expectedRisk population loss candidate)
    (hfinite : (ProbabilityCoupling.expectedDistanceCosts
      (empiricalSampleProbabilityMeasureOfPos hcount sample) population).Nonempty) :
    ‖empiricalMinimizer - populationMinimizer‖ ≤ (smoothness : ℝ) / modulus *
      ProbabilityCoupling.wassersteinOneReal
        (empiricalSampleProbabilityMeasureOfPos hcount sample) population hfinite :=
  norm_minimizers_sub_le_wasserstein
    (empiricalSampleProbabilityMeasureOfPos hcount sample) population loss gradient
    domain hconvex smoothness hgradient hdata hmodulus hstrong
    hempirical_integrable hpopulation_integrable
    empiricalMinimizer populationMinimizer hempirical_mem hpopulation_mem
    hempirical_min hpopulation_min hfinite

section ExtendedWasserstein

variable [OpensMeasurableSpace Data] [SecondCountableTopology Data]

/-- An extended-real `W₁` bound transports the loss increment between two
laws.  This is the direct interface to the empirical-Wasserstein concentration
event; no identification of the real and extended infima is needed. -/
theorem abs_expectedRisk_increment_shift_le_of_wassersteinOne
    (firstLaw secondLaw : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hsmoothness : smoothness ≠ 0)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    (hintegrableFirst : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (firstLaw : Measure Data))
    (hintegrableSecond : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (secondLaw : Measure Data))
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain)
    {wassersteinBound : ℝ} (hboundNonneg : 0 ≤ wassersteinBound)
    (hWasserstein : ProbabilityCoupling.wassersteinOne firstLaw secondLaw ≤
      ENNReal.ofReal wassersteinBound) :
    |(expectedRisk firstLaw loss second - expectedRisk firstLaw loss first) -
      (expectedRisk secondLaw loss second - expectedRisk secondLaw loss first)| ≤
      ((smoothness : ℝ) * ‖second - first‖) * wassersteinBound := by
  by_cases hzero : ‖second - first‖ = 0
  · have heq : second = first := sub_eq_zero.mp (norm_eq_zero.mp hzero)
    subst second
    simp
  let incrementLipschitz : NNReal := smoothness * ‖second - first‖₊
  have hincrementLipschitz : incrementLipschitz ≠ 0 := by
    apply mul_ne_zero hsmoothness
    exact nnnorm_ne_zero_iff.mpr fun hsub => hzero (by rw [hsub, norm_zero])
  have htransport :=
    ProbabilityCoupling.ofReal_norm_integral_sub_le_lipschitz_wassersteinOne
      (PZMH20PerformativePrediction.DomainRelative.loss_increment_lipschitz
        loss gradient domain hconvex smoothness
        hgradient hdata hfirst hsecond)
      hincrementLipschitz
      ((hintegrableFirst second hsecond).sub (hintegrableFirst first hfirst))
      ((hintegrableSecond second hsecond).sub (hintegrableSecond first hfirst))
  have hproduct :
      (incrementLipschitz : ℝ≥0∞) *
          ProbabilityCoupling.wassersteinOne firstLaw secondLaw ≤
        ENNReal.ofReal ((incrementLipschitz : ℝ) * wassersteinBound) := by
    calc
      (incrementLipschitz : ℝ≥0∞) *
          ProbabilityCoupling.wassersteinOne firstLaw secondLaw ≤
          (incrementLipschitz : ℝ≥0∞) * ENNReal.ofReal wassersteinBound :=
        mul_le_mul_right hWasserstein _
      _ = ENNReal.ofReal ((incrementLipschitz : ℝ) * wassersteinBound) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg incrementLipschitz)]
        rw [ENNReal.ofReal_coe_nnreal]
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (NNReal.coe_nonneg smoothness) (norm_nonneg _))
      hboundNonneg)).mp
  simpa only [expectedRisk,
    integral_sub (hintegrableFirst second hsecond) (hintegrableFirst first hfirst),
    integral_sub (hintegrableSecond second hsecond) (hintegrableSecond first hfirst),
    Real.norm_eq_abs, incrementLipschitz, NNReal.coe_mul, coe_nnnorm] using
    htransport.trans hproduct

/-- Constrained minimizers under laws separated by an extended-real `W₁`
upper bound differ by at most `β / γ` times that bound. -/
theorem norm_minimizers_sub_le_of_wassersteinOne
    (firstLaw secondLaw : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hsmoothness : smoothness ≠ 0)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvexOn loss gradient domain modulus)
    (hintegrableFirst : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (firstLaw : Measure Data))
    (hintegrableSecond : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (secondLaw : Measure Data))
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain)
    (hminFirst : ∀ candidate ∈ domain,
      expectedRisk firstLaw loss first ≤ expectedRisk firstLaw loss candidate)
    (hminSecond : ∀ candidate ∈ domain,
      expectedRisk secondLaw loss second ≤ expectedRisk secondLaw loss candidate)
    {wassersteinBound : ℝ} (hboundNonneg : 0 ≤ wassersteinBound)
    (hWasserstein : ProbabilityCoupling.wassersteinOne firstLaw secondLaw ≤
      ENNReal.ofReal wassersteinBound) :
    ‖first - second‖ ≤ (smoothness : ℝ) / modulus * wassersteinBound := by
  have hleft := (strongConvexOn_expectedRisk firstLaw loss gradient domain hconvex hstrong
    hintegrableFirst).quadratic_gap_le_of_isMinOn hfirst hsecond hminFirst
  have hright := (strongConvexOn_expectedRisk secondLaw loss gradient domain hconvex hstrong
    hintegrableSecond).quadratic_gap_le_of_isMinOn hsecond hfirst hminSecond
  have hshift := abs_expectedRisk_increment_shift_le_of_wassersteinOne
    firstLaw secondLaw loss gradient domain hconvex smoothness hsmoothness
    hgradient hdata hintegrableFirst hintegrableSecond first second hfirst hsecond
    hboundNonneg hWasserstein
  rw [norm_sub_rev second first] at hleft hshift
  have hquad : modulus * ‖first - second‖ ^ 2 ≤
      ((smoothness : ℝ) * ‖first - second‖) * wassersteinBound := by
    have hupper := (abs_le.mp hshift).2
    linarith
  by_cases heq : ‖first - second‖ = 0
  · rw [heq]
    positivity
  have hpos : 0 < ‖first - second‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm heq)
  have hcancel : modulus * ‖first - second‖ ≤
      (smoothness : ℝ) * wassersteinBound := by
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hquad]
  calc
    ‖first - second‖ ≤ ((smoothness : ℝ) * wassersteinBound) / modulus :=
      (le_div_iff₀ hmodulus).2 (by nlinarith only [hcancel])
    _ = _ := by ring

/-- The extended-real perturbation theorem for a nonempty empirical sample. -/
theorem norm_empiricalMinimizer_sub_populationMinimizer_le_of_wassersteinOne
    {sampleCount : ℕ} (hcount : 0 < sampleCount) (sample : Fin sampleCount → Data)
    (population : ProbabilityMeasure Data)
    (loss : Data → Parameter → ℝ) (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hsmoothness : smoothness ≠ 0)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvexOn loss gradient domain modulus)
    (hempirical_integrable : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter)
        (empiricalSampleProbabilityMeasureOfPos hcount sample : Measure Data))
    (hpopulation_integrable : ∀ parameter ∈ domain,
      Integrable (fun datum => loss datum parameter) (population : Measure Data))
    (empiricalMinimizer populationMinimizer : Parameter)
    (hempirical_mem : empiricalMinimizer ∈ domain)
    (hpopulation_mem : populationMinimizer ∈ domain)
    (hempirical_min : ∀ candidate ∈ domain,
      expectedRisk (empiricalSampleProbabilityMeasureOfPos hcount sample) loss
          empiricalMinimizer ≤
        expectedRisk (empiricalSampleProbabilityMeasureOfPos hcount sample) loss candidate)
    (hpopulation_min : ∀ candidate ∈ domain,
      expectedRisk population loss populationMinimizer ≤
        expectedRisk population loss candidate)
    {wassersteinBound : ℝ} (hboundNonneg : 0 ≤ wassersteinBound)
    (hWasserstein : ProbabilityCoupling.wassersteinOne
      (empiricalSampleProbabilityMeasureOfPos hcount sample) population ≤
        ENNReal.ofReal wassersteinBound) :
    ‖empiricalMinimizer - populationMinimizer‖ ≤
      (smoothness : ℝ) / modulus * wassersteinBound :=
  norm_minimizers_sub_le_of_wassersteinOne
    (empiricalSampleProbabilityMeasureOfPos hcount sample) population loss gradient
    domain hconvex smoothness hsmoothness hgradient hdata hmodulus hstrong
    hempirical_integrable hpopulation_integrable
    empiricalMinimizer populationMinimizer hempirical_mem hpopulation_mem
    hempirical_min hpopulation_min hboundNonneg hWasserstein

end ExtendedWasserstein

end PZMH20PerformativePrediction.EmpiricalMinimizerPerturbation
