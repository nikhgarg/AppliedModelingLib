import PZMH20PerformativePrediction.Definitions

/-!
# Paper-Facing Theorems: Performative Prediction

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib
open MeasureTheory
open scoped InnerProductSpace

/--
The Banach-contraction part of Theorem 3.5: once the RRM update is known to be
contracting, repeated retraining converges to its fixed point.  The source
paper's sensitivity/smoothness calculation establishing contraction is a
separate pending obligation.
-/
theorem rrmIteratesTendstoFixedPoint
    {Parameter : Type*} [MetricSpace Parameter] [CompleteSpace Parameter] [Nonempty Parameter]
    (update : Parameter → Parameter) {K : NNReal} (hcontract : ContractingWith K update)
    (initial : Parameter) :
    Filter.Tendsto (fun n => update^[n] initial) Filter.atTop
      (nhds (hcontract.fixedPoint update)) :=
  hcontract.tendsto_iterate_fixedPoint initial

/--
The arbitrary-law compact-convex fixed-point route for Proposition 4.1.  It
derives convex frozen risks from the source pointwise loss-convexity condition;
the joint-risk continuity/Berge bridge remains explicit.
-/
theorem measureCompactConvexStablePointExists
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [FiniteDimensional ℝ Parameter] [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (hcompact : IsCompact domain) (hne : domain.Nonempty) (hconvex : Convex ℝ domain)
    (hjoint : Continuous (fun point : Parameter × Parameter =>
      measureDecoupledPerformativeRisk model point.1 point.2))
    (hlossConvex : ∀ datum, ConvexOn ℝ domain (model.loss datum)) :
    ∃ parameter ∈ domain, IsMeasurePerformativelyStableOn model domain parameter :=
  exists_isMeasurePerformativelyStableOn_of_compact_convex_of_lossConvex model domain hcompact hne
    hconvex hjoint hlossConvex

/--
A reusable sufficient continuity bridge for Proposition 4.1.  This strengthens
the source's bare joint-continuity loss hypothesis to uniform coordinate-wise
loss Lipschitz bounds, under which W₁ sensitivity proves joint continuity of
the decoupled population risk before the best-response/Kakutani argument.
-/
theorem measureCompactConvexStablePointExistsOfWassersteinLossLipschitz
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [FiniteDimensional ℝ Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (hcompact : IsCompact domain) (hne : domain.Nonempty) (hconvex : Convex ℝ domain)
    (hlossConvex : ∀ datum, ConvexOn ℝ domain (model.loss datum))
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : IsMeasureDataLossLipschitz model dataConstant)
    (hparameterLoss : IsMeasureParameterLossLipschitz model parameterConstant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity) :
    ∃ parameter ∈ domain, IsMeasurePerformativelyStableOn model domain parameter :=
  exists_isMeasurePerformativelyStableOn_of_compact_convex_of_lossConvex_of_wassersteinLossLipschitz
    model domain hcompact hne hconvex hlossConvex hdataLoss hparameterLoss hsensitivity hsensitive

/--
Candidate arbitrary-law Wasserstein endpoint for Theorem 4.3 on the source
parameter domain, pending source-fidelity review. The input model is defined
only on that domain; an explicit anchored extension lets A2 give strong
convexity of the frozen risk by pointwise gradient cancellation before
integration, without A1 or differentiation under expectation.
-/
theorem measureWassersteinOptimumStableDistance
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [MeasurableSpace Data] [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter)
    (_hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    {constant : NNReal} (hloss : model.IsDataLossLipschitz constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (optimal stable : domain)
    (hoptimal : model.IsPerformativelyOptimal optimal)
    (hstable : model.IsPerformativelyStable stable) :
    ‖(optimal : Parameter) - (stable : Parameter)‖ ≤
      2 * (constant : ℝ) * sensitivity / modulus :=
  model.norm_optimal_sub_stable_le_of_strongConvex_wasserstein gradient hconvex
    hmodulus hstrong hloss hsensitivity hsensitive optimal stable hoptimal hstable

/--
Arbitrary-law Wasserstein realization of Corollary 5.1.  The source's
objective-gap constant follows from the preceding Theorem 4.3 endpoint and
the two coordinate-wise loss Lipschitz conditions.
-/
theorem measureWassersteinStableObjectiveGap
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : IsMeasureDataLossLipschitz model dataConstant)
    (hparameterLoss : IsMeasureParameterLossLipschitz model parameterConstant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsMeasurePerformativelyOptimal model optimal)
    (hstable : IsMeasurePerformativelyStable model stable) :
    measurePerformativeRisk model stable - measurePerformativeRisk model optimal ≤
      2 * (dataConstant : ℝ) * sensitivity *
        ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus := by
  apply measurePerformativeRisk_sub_measurePerformativelyOptimal_le_of_stable_wasserstein
    model gradient ?_ hmodulus hstrong hintegrable hdataLoss hparameterLoss hsensitivity hsensitive
      optimal stable hoptimal hstable
  intro distributionParameter evaluatedParameter
  exact hasGradientAt_measureDecoupledPerformativeRisk_of_jointSmooth model gradient hjoint
    distributionParameter evaluatedParameter (hloss_meas distributionParameter evaluatedParameter)
    (hintegrable distributionParameter evaluatedParameter) hpointwise 1 zero_lt_one

/--
The finite primal transport consequence of Definition 3.1: sensitivity bounds
the change in the expectation of every Lipschitz data statistic.  This is the
transport estimate used in the source proof of Theorem 3.5, before its
strong-convexity and gradient calculation.
-/
theorem finiteTransportSensitive_lipschitzStatistic
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) {sensitivity : ℝ}
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    {L : NNReal} {statistic : Data → ℝ} (hstatistic : LipschitzWith L statistic)
    (first second : Parameter) :
    |pmfExp (model.dataLaw first) statistic - pmfExp (model.dataLaw second) statistic| ≤
      (L : ℝ) * (sensitivity * dist first second) :=
  abs_pmfExp_dataLaw_sub_le_of_finiteTransportSensitive model hsensitive hstatistic first second

/--
The finite-PMF W₁ consequence of Definition 3.1: the finite Wasserstein
sensitivity condition controls every Lipschitz data statistic.
-/
theorem finiteWassersteinSensitive_lipschitzStatistic
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) {sensitivity : ℝ}
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    {L : NNReal} {statistic : Data → ℝ} (hstatistic : LipschitzWith L statistic)
    (first second : Parameter) :
    |pmfExp (model.dataLaw first) statistic - pmfExp (model.dataLaw second) statistic| ≤
      (L : ℝ) * (sensitivity * dist first second) :=
  abs_pmfExp_dataLaw_sub_le_of_finiteWassersteinSensitive model hsensitive hstatistic first second

/--
The distribution-shift estimate in Appendix E.1 of the source: joint
smoothness in the data coordinate makes the gradient paired with any fixed
displacement a Lipschitz test statistic, so finite transport sensitivity bounds
the corresponding change in expected gradient pairing.
-/
theorem finiteTransportSensitive_gradientPairing
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness) {sensitivity : ℝ}
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (displacement evaluated first second : Parameter) :
    |pmfExp (model.dataLaw first) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ) -
        pmfExp (model.dataLaw second) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ)| ≤
      ((smoothness * ‖displacement‖₊ : NNReal) : ℝ) *
        (sensitivity * dist first second) :=
  finiteTransportSensitive_lipschitzStatistic model hsensitive
    (gradientPairing_lipschitz gradient hgradient displacement evaluated) first second

/--
The finite-W₁ version of the distribution-shift estimate in Appendix E.1.
It uses the finite Kantorovich--Rubinstein direction just proved in the
reusable probability layer.
-/
theorem finiteWassersteinSensitive_gradientPairing
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness) {sensitivity : ℝ}
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (displacement evaluated first second : Parameter) :
    |pmfExp (model.dataLaw first) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ) -
        pmfExp (model.dataLaw second) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ)| ≤
      ((smoothness * ‖displacement‖₊ : NNReal) : ℝ) *
        (sensitivity * dist first second) :=
  finiteWassersteinSensitive_lipschitzStatistic model hsensitive
    (gradientPairing_lipschitz gradient hgradient displacement evaluated) first second

/--
A source-shaped finite-PMF and unconstrained-parameter specialization of
Theorem 3.5(a).  The complete source assumption (A1) is visible, while the
proof uses its data-coordinate component exactly as Appendix E.1 does.
-/
theorem finiteUnconstrainedRRMContraction
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (update : Parameter → Parameter) (hrrm : IsRRM model update)
    (first second : Parameter) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖ :=
  rrm_distance_le_of_hasGradientAt_univ model gradient hgradientAt hjoint.2
    hsensitivity hmodulus hsensitive hstrong update hrrm first second

/--
Finite-PMF W₁ realization of the whole-parameter-space Theorem 3.5(a)
contraction.  It keeps the source's W₁-style sensitivity premise while making
the finite data-carrier restriction explicit.
-/
theorem finiteWassersteinUnconstrainedRRMContraction
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (update : Parameter → Parameter) (hrrm : IsRRM model update)
    (first second : Parameter) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖ :=
  rrm_distance_le_of_hasGradientAt_univ_finiteWasserstein model gradient hgradientAt hjoint.2
    hsensitivity hmodulus hsensitive hstrong update hrrm first second

/--
The arbitrary-measure A2 bridge used by Theorem 3.5: integrating the
pointwise strong-convexity inequality gives inner-product strong monotonicity
of each frozen expected gradient.  Thus this part of the source assumption is
not an additional general-law premise.
-/
theorem measurePointwiseStrongConvex_expectedGradientStrongMonotone
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {modulus : ℝ}
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data)) :
    AppliedModelingLib.IsMeasureFrozenGradientStronglyMonotoneInner model gradient modulus :=
  AppliedModelingLib.isMeasureFrozenGradientStronglyMonotoneInner_of_pointwiseStronglyConvex
    model gradient hstrong hintegrable

/--
General probability-measure source-to-model bridge for Theorem 3.5(a).  The
finite-first-moment, gradient-representation, and strong-monotonicity
conditions are visible because they make the paper's arbitrary-distribution
W₁ and first-order argument mathematically defined in Lean.
-/
theorem measureWassersteinUnconstrainedRRMContraction
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRM model update)
    (hgradientAt : ∀ distributionParameter evaluatedParameter,
      HasGradientAt
        (fun parameter => measureDecoupledPerformativeRisk model distributionParameter parameter)
        (measureFrozenPopulationGradient model gradient distributionParameter evaluatedParameter)
        evaluatedParameter)
    (hstrong : IsMeasureFrozenGradientStronglyMonotone model gradient modulus)
    (first second : Parameter) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * dist first second := by
  calc
    ‖update first - update second‖ ≤
        ((smoothness : ℝ) * (sensitivity * dist first second)) / modulus :=
      norm_measureRRM_sub_le_of_wassersteinSensitive_hasGradientAt
        model gradient hgradient hintegrable hmodulus hsensitive update hrrm hgradientAt hstrong
          first second
    _ = (sensitivity * (smoothness : ℝ) / modulus) * dist first second := by ring

/--
General probability-measure realization of the convergence conclusion in
Theorem 3.5(b).  This is the whole-parameter-space branch of the source
argument: a strict general W₁ RRM contraction yields a unique performatively
stable point and its geometric iterate bound.  The Bochner-integrability,
gradient-representation, and strong-monotonicity bridges are deliberately
explicit rather than hidden behind the paper's informal regularity language.
-/
theorem measureWassersteinUnconstrainedRRMConvergesLinearly
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Nonempty Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRM model update)
    (hgradientAt : ∀ distributionParameter evaluatedParameter,
      HasGradientAt
        (fun parameter => measureDecoupledPerformativeRisk model distributionParameter parameter)
        (measureFrozenPopulationGradient model gradient distributionParameter evaluatedParameter)
        evaluatedParameter)
    (hstrong : IsMeasureFrozenGradientStronglyMonotone model gradient modulus)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) :
    ∃ stable, IsMeasureStable model stable ∧
      (∀ other, IsMeasureStable model other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖ :=
  measureRRM_convergesLinearly_of_wassersteinSensitive_hasGradientAt
    model gradient hgradient hintegrable hsensitivity hmodulus hsensitive update hrrm hgradientAt hstrong
      hfactor initial

/--
General probability-measure, closed-convex-domain realization of Theorem
3.5(a).  It uses the source-shaped W₁ sensitivity condition directly and the
variational first-order condition at each domain-constrained frozen minimizer.
-/
theorem measureWassersteinConvexRRMContraction
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hgradientAt : ∀ distributionParameter evaluatedParameter,
      HasGradientAt
        (fun parameter => measureDecoupledPerformativeRisk model distributionParameter parameter)
        (measureFrozenPopulationGradient model gradient distributionParameter evaluatedParameter)
        evaluatedParameter)
    (hstrong : IsMeasureFrozenGradientStronglyMonotoneInner model gradient modulus)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖ :=
  norm_measureRRMOn_sub_le_of_wassersteinSensitive_hasGradientAt
    model gradient hgradient hintegrable hsensitivity hmodulus hsensitive domain hconvex update hrrm
      hgradientAt hstrong first second hfirst hsecond

/--
Source-shaped arbitrary-measure Theorem 3.5(a) endpoint.  A1 is supplied in
its full jointly-smooth form and A2 is supplied in its pointwise
strong-convexity form; the latter is discharged through the preceding Bochner
expectation theorem.  The frozen-risk derivative representation is derived
through Mathlib's dominated parametric-integral theorem: A1 supplies its
local derivative domination, while loss measurability and pointwise
differentiability remain explicit analytic hypotheses.
-/
theorem measureWassersteinConvexRRMContraction_of_A1_A2
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖ :=
  measureWassersteinConvexRRMContraction model gradient hjoint.2 hintegrable hsensitivity hmodulus
    hsensitive domain hconvex update hrrm
    (fun distributionParameter evaluatedParameter =>
      hasGradientAt_measureDecoupledPerformativeRisk_of_jointSmooth model gradient hjoint
        distributionParameter evaluatedParameter (hloss_meas distributionParameter evaluatedParameter)
        (hintegrable distributionParameter evaluatedParameter) hpointwise 1 (by norm_num))
    (measurePointwiseStrongConvex_expectedGradientStrongMonotone model gradient hstrong hintegrable)
    first second hfirst hsecond

/--
General probability-measure realization of Theorem 3.5(b) on the source's
closed convex parameter domain.  Its W₁, integrability, frozen-risk gradient,
and expected-gradient strong-monotonicity requirements remain visible pending
a direct derivation from the paper's informal regularity assumptions.
-/
theorem measureWassersteinConvexRRMConvergesLinearly
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hgradientAt : ∀ distributionParameter evaluatedParameter,
      HasGradientAt
        (fun parameter => measureDecoupledPerformativeRisk model distributionParameter parameter)
        (measureFrozenPopulationGradient model gradient distributionParameter evaluatedParameter)
        evaluatedParameter)
    (hstrong : IsMeasureFrozenGradientStronglyMonotoneInner model gradient modulus)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsMeasureStableOn model domain stable ∧
      (∀ other ∈ domain, IsMeasureStableOn model domain other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖ :=
  measureRRMOn_convergesLinearly_of_wassersteinSensitive_hasGradientAt
    model gradient hgradient hintegrable hsensitivity hmodulus hsensitive domain hclosed hconvex update hrrm
      hgradientAt hstrong hfactor initial hinitial

/--
Source-shaped arbitrary-measure Theorem 3.5(b) endpoint.  The same A1--A2
bridge as part (a) supplies the strict RRM contraction; Banach then gives the
unique stable point and stated geometric rate on the closed convex domain.
The dominated differentiation bridge keeps local loss measurability and
pointwise differentiability explicit, while deriving its domination from A1.
-/
theorem measureWassersteinConvexRRMConvergesLinearly_of_A1_A2
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsMeasureStableOn model domain stable ∧
      (∀ other ∈ domain, IsMeasureStableOn model domain other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖ :=
  measureWassersteinConvexRRMConvergesLinearly model gradient hjoint.2 hintegrable hsensitivity
    hmodulus hsensitive domain hclosed hconvex update hrrm
    (fun distributionParameter evaluatedParameter =>
      hasGradientAt_measureDecoupledPerformativeRisk_of_jointSmooth model gradient hjoint
        distributionParameter evaluatedParameter (hloss_meas distributionParameter evaluatedParameter)
        (hintegrable distributionParameter evaluatedParameter) hpointwise 1 (by norm_num))
    (measurePointwiseStrongConvex_expectedGradientStrongMonotone model gradient hstrong hintegrable)
    hfactor initial hinitial

/--
Source-shaped arbitrary-measure Theorem 3.8(a)--(b) endpoint.  The general
W₁ `T₂`/`T₃` calculation, its exact displayed projected-RGD contraction, and
Banach's fixed-point conclusion are proved in the reusable core.  As in the
general Theorem 3.5 wrapper, A1 supplies derivative domination while local
loss measurability and pointwise differentiability remain explicit.
-/
theorem measureWassersteinConvexRGDConvergesLinearly_of_A1_A2
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hnonempty : domain.Nonempty)
    (hconvex : Convex ℝ domain) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsMeasureStableOn model domain stable ∧
      (∀ other ∈ domain, IsMeasureStableOn model domain other → other = stable) ∧
      Filter.Tendsto
        (fun iteration => (measureRepeatedGradientDescentUpdate model gradient project stepSize)^[iteration]
          initial)
        Filter.atTop (nhds stable) ∧
      ∀ iteration,
        ‖(measureRepeatedGradientDescentUpdate model gradient project stepSize)^[iteration] initial -
            stable‖ ≤
          (1 - stepSize * (modulus * (smoothness : ℝ) /
            (modulus + (smoothness : ℝ)) -
              sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 +
                (smoothness : ℝ)))) ^ iteration * ‖initial - stable‖ := by
  simpa only [IsMeasureStableOn] using
    measureRepeatedGradientDescent_convergesLinearly_of_interpolation
      model gradient hjoint hintegrable
      (fun distributionParameter evaluatedParameter =>
        hasGradientAt_measureDecoupledPerformativeRisk_of_jointSmooth model gradient hjoint
          distributionParameter evaluatedParameter (hloss_meas distributionParameter evaluatedParameter)
          (hintegrable distributionParameter evaluatedParameter) hpointwise 1 (by norm_num))
      hsensitivity hsensitive hmodulus hmodulus_le hstrong domain hclosed hnonempty hconvex
      project hproject hproject_nonexpansive stepSize hstepSize hstepSize_le hsensitivity_small
      initial hinitial

/--
Theorem 3.8(a)--(b) with its Euclidean projection constructed from the source
closed-convex parameter domain.  The construction directly reuses Mathlib's
Hilbert projection theorem; see
`AppliedModelingLib.Foundations.Optimization.EuclideanProjection` for the upstream
source and documentation attribution.
-/
theorem measureWassersteinConvexRGDConvergesLinearly_withHilbertProjection_of_A1_A2
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hnonempty : domain.Nonempty)
    (hconvex : Convex ℝ domain)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsMeasureStableOn model domain stable ∧
      (∀ other ∈ domain, IsMeasureStableOn model domain other → other = stable) ∧
      Filter.Tendsto
        (fun iteration =>
          (measureRepeatedGradientDescentUpdate model gradient
            (hilbertProjection domain hnonempty hclosed hconvex) stepSize)^[iteration] initial)
        Filter.atTop (nhds stable) ∧
      ∀ iteration,
        ‖(measureRepeatedGradientDescentUpdate model gradient
          (hilbertProjection domain hnonempty hclosed hconvex) stepSize)^[iteration] initial - stable‖ ≤
          (1 - stepSize * (modulus * (smoothness : ℝ) /
            (modulus + (smoothness : ℝ)) -
              sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 +
                (smoothness : ℝ)))) ^ iteration * ‖initial - stable‖ := by
  simpa only [IsMeasureStableOn] using
    measureRepeatedGradientDescent_convergesLinearly_withHilbertProjection_of_interpolation
      model gradient hjoint hintegrable
      (fun distributionParameter evaluatedParameter =>
        hasGradientAt_measureDecoupledPerformativeRisk_of_jointSmooth model gradient hjoint
          distributionParameter evaluatedParameter (hloss_meas distributionParameter evaluatedParameter)
          (hintegrable distributionParameter evaluatedParameter) hpointwise 1 (by norm_num))
      hsensitivity hsensitive hmodulus hmodulus_le hstrong domain hclosed hnonempty hconvex stepSize
      hstepSize hstepSize_le hsensitivity_small initial hinitial

/--
Finite-PMF W₁ realization of the convex-domain Theorem 3.5(a) contraction.
The finite carrier is explicit, but the sensitivity assumption is the finite
W₁ condition itself rather than a chosen coupling witness.
-/
theorem finiteWassersteinConvexRRMContraction
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖ :=
  rrm_distance_le_on_of_strongConvex_firstOrder_finiteWasserstein model gradient hjoint.2
    hsensitivity hmodulus hsensitive hstrong domain update hrrm
    (fun deployed hdeployed =>
      isFrozenFirstOrderOptimal_on_of_hasGradientAt model gradient hgradientAt domain hconvex
        deployed (update deployed) (hrrm deployed hdeployed))
    first second hfirst hsecond

/--
A finite-PMF, convex-domain specialization of Theorem 3.5(a).  The source
assumes that `Θ` is closed and convex.  This conditional theorem only needs
convexity because `IsRRMOn` already supplies the required minimizer in the
domain; closedness is relevant to existence, which is not asserted here.
-/
theorem finiteConvexRRMContraction
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    ‖update first - update second‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖ :=
  rrm_distance_le_on_of_strongConvex_firstOrder_transport model gradient hjoint.2
    hsensitivity hmodulus hsensitive hstrong domain update hrrm
    (fun deployed hdeployed =>
      isFrozenFirstOrderOptimal_on_of_hasGradientAt model gradient hgradientAt domain hconvex
        deployed (update deployed) (hrrm deployed hdeployed))
    first second hfirst hsecond

/--
Finite-PMF convex-domain realization of Theorem 3.5(b).  A strict
`εβ/γ < 1` contraction factor gives a unique domain-stable point, convergence
of RRM to it, and the source's geometric error estimate.  Closedness is used
here, unlike in part (a), to make the parameter-domain subtype complete for
Banach's fixed-point theorem.
-/
theorem finiteConvexRRMConvergesLinearly
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsPerformativelyStableOn model domain stable ∧
      (∀ other ∈ domain, IsPerformativelyStableOn model domain other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖ := by
  have hfactor_nonneg : 0 ≤ sensitivity * (smoothness : ℝ) / modulus := by positivity
  let factor : NNReal := ⟨sensitivity * (smoothness : ℝ) / modulus, hfactor_nonneg⟩
  have hfactor_lt : factor < 1 := by simpa [factor] using hfactor
  have hmaps : Set.MapsTo update domain domain :=
    repeatedRiskMinimizationOn_mapsTo model domain update hrrm
  let restricted : domain → domain := restrictedUpdate domain update hmaps
  have hbound : ∀ first ∈ domain, ∀ second ∈ domain,
      dist (update first) (update second) ≤ (factor : ℝ) * dist first second := by
    intro first hfirst second hsecond
    simpa only [dist_eq_norm, NNReal.coe_mk] using
      finiteConvexRRMContraction model gradient hgradientAt hjoint
      hsensitivity hmodulus hsensitive hstrong domain hconvex update hrrm first second hfirst hsecond
  have hcontract : ContractingWith factor restricted := by
    simpa [restricted] using contractingWith_restrictedUpdate_of_bound domain update hmaps
      hfactor_lt hbound
  letI : IsClosed domain := hclosed
  letI : Nonempty domain := ⟨⟨initial, hinitial⟩⟩
  let stableSub : domain := hcontract.fixedPoint restricted
  have hstableFixed : Function.IsFixedPt restricted stableSub :=
    hcontract.fixedPoint_isFixedPt
  have hstableFixedVal : update stableSub = stableSub := by
    exact_mod_cast congrArg Subtype.val hstableFixed
  have hstable : IsPerformativelyStableOn model domain stableSub :=
    isPerformativelyStableOn_of_retrainingOn_fixedPoint model domain update hrrm stableSub.2
      hstableFixedVal
  refine ⟨stableSub, stableSub.2, hstable, ?_, ?_, ?_⟩
  · intro other hother hotherStable
    have hunique : ∀ deployed ∈ domain, ∀ first second,
        IsPopulationRiskMinimizerOn model domain (model.dataLaw deployed) first →
          IsPopulationRiskMinimizerOn model domain (model.dataLaw deployed) second → first = second := by
      intro deployed hdeployed first second hfirst hsecond
      exact populationRiskMinimizerOn_unique_of_strongConvex_firstOrder model gradient hmodulus
        hstrong domain deployed first second hfirst hsecond
        (isFrozenFirstOrderOptimal_on_of_hasGradientAt model gradient hgradientAt domain hconvex
          deployed first hfirst).2
    have hotherFixed : update other = other :=
      retrainingOn_fixedPoint_of_isPerformativelyStableOn_of_uniqueMinimizer model domain update
        hrrm hunique hotherStable
    have hotherFixedSub : Function.IsFixedPt restricted ⟨other, hother⟩ := by
      apply Subtype.ext
      exact hotherFixed
    exact congrArg Subtype.val (hcontract.fixedPoint_unique' hotherFixedSub hstableFixed)
  · have hlimit := hcontract.tendsto_iterate_fixedPoint ⟨initial, hinitial⟩
    convert (continuous_subtype_val.tendsto _).comp hlimit using 1
    funext iteration
    change update^[iteration] initial =
      ((restricted^[iteration] ⟨initial, hinitial⟩ : domain) : Parameter)
    simp only [restricted, restrictedUpdate]
    rw [Set.MapsTo.coe_iterate_restrict]
  · intro iteration
    have hrate := (hcontract.toLipschitzWith.iterate iteration).dist_le_mul
      ⟨initial, hinitial⟩ stableSub
    rw [(hstableFixed.iterate iteration).eq] at hrate
    simpa only [restricted, restrictedUpdate, Set.MapsTo.iterate_restrict,
      Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm, NNReal.coe_pow] using hrate

/--
The Banach/fixed-point tail of Theorem 3.5(b), parameterized by the displayed
RRM distance bound on a closed convex finite-PMF domain.  This lets both the
primal-certificate and finite-W₁ forms of part (a) share the same stability,
uniqueness, and geometric-convergence argument.
-/
theorem finiteConvexRRMConvergesLinearly_of_distanceBound
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (hbound : ∀ first ∈ domain, ∀ second ∈ domain,
      ‖update first - update second‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsPerformativelyStableOn model domain stable ∧
      (∀ other ∈ domain, IsPerformativelyStableOn model domain other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖ := by
  have hfactor_nonneg : 0 ≤ sensitivity * (smoothness : ℝ) / modulus := by positivity
  let factor : NNReal := ⟨sensitivity * (smoothness : ℝ) / modulus, hfactor_nonneg⟩
  have hfactor_lt : factor < 1 := by simpa [factor] using hfactor
  have hmaps : Set.MapsTo update domain domain :=
    repeatedRiskMinimizationOn_mapsTo model domain update hrrm
  let restricted : domain → domain := restrictedUpdate domain update hmaps
  have hbound' : ∀ first ∈ domain, ∀ second ∈ domain,
      dist (update first) (update second) ≤ (factor : ℝ) * dist first second := by
    intro first hfirst second hsecond
    simpa only [dist_eq_norm, NNReal.coe_mk] using hbound first hfirst second hsecond
  have hcontract : ContractingWith factor restricted := by
    simpa [restricted] using contractingWith_restrictedUpdate_of_bound domain update hmaps
      hfactor_lt hbound'
  letI : IsClosed domain := hclosed
  letI : Nonempty domain := ⟨⟨initial, hinitial⟩⟩
  let stableSub : domain := hcontract.fixedPoint restricted
  have hstableFixed : Function.IsFixedPt restricted stableSub :=
    hcontract.fixedPoint_isFixedPt
  have hstableFixedVal : update stableSub = stableSub := by
    exact_mod_cast congrArg Subtype.val hstableFixed
  have hstable : IsPerformativelyStableOn model domain stableSub :=
    isPerformativelyStableOn_of_retrainingOn_fixedPoint model domain update hrrm stableSub.2
      hstableFixedVal
  refine ⟨stableSub, stableSub.2, hstable, ?_, ?_, ?_⟩
  · intro other hother hotherStable
    have hunique : ∀ deployed ∈ domain, ∀ first second,
        IsPopulationRiskMinimizerOn model domain (model.dataLaw deployed) first →
          IsPopulationRiskMinimizerOn model domain (model.dataLaw deployed) second → first = second := by
      intro deployed hdeployed first second hfirst hsecond
      exact populationRiskMinimizerOn_unique_of_strongConvex_firstOrder model gradient hmodulus
        hstrong domain deployed first second hfirst hsecond
        (isFrozenFirstOrderOptimal_on_of_hasGradientAt model gradient hgradientAt domain hconvex
          deployed first hfirst).2
    have hotherFixed : update other = other :=
      retrainingOn_fixedPoint_of_isPerformativelyStableOn_of_uniqueMinimizer model domain update
        hrrm hunique hotherStable
    have hotherFixedSub : Function.IsFixedPt restricted ⟨other, hother⟩ := by
      apply Subtype.ext
      exact hotherFixed
    exact congrArg Subtype.val (hcontract.fixedPoint_unique' hotherFixedSub hstableFixed)
  · have hlimit := hcontract.tendsto_iterate_fixedPoint ⟨initial, hinitial⟩
    convert (continuous_subtype_val.tendsto _).comp hlimit using 1
    funext iteration
    change update^[iteration] initial =
      ((restricted^[iteration] ⟨initial, hinitial⟩ : domain) : Parameter)
    simp only [restricted, restrictedUpdate]
    rw [Set.MapsTo.coe_iterate_restrict]
  · intro iteration
    have hrate := (hcontract.toLipschitzWith.iterate iteration).dist_le_mul
      ⟨initial, hinitial⟩ stableSub
    rw [(hstableFixed.iterate iteration).eq] at hrate
    simpa only [restricted, restrictedUpdate, Set.MapsTo.iterate_restrict,
      Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm, NNReal.coe_pow] using hrate

/--
Finite-PMF W₁ realization of Theorem 3.5(b).  The finite-W₁ convex-domain
contraction supplies Banach's hypothesis, yielding a unique domain-stable
point and the source's geometric RRM iterate bound.
-/
theorem finiteWassersteinConvexRRMConvergesLinearly
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    ∃ stable ∈ domain, IsPerformativelyStableOn model domain stable ∧
      (∀ other ∈ domain, IsPerformativelyStableOn model domain other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖ := by
  apply finiteConvexRRMConvergesLinearly_of_distanceBound model gradient hgradientAt hsensitivity hmodulus hstrong
    domain hclosed hconvex update hrrm hfactor ?_ initial hinitial
  intro first hfirst second hsecond
  exact finiteWassersteinConvexRRMContraction model gradient hgradientAt hjoint
    hsensitivity hmodulus hsensitive hstrong domain hconvex update hrrm first second hfirst hsecond

/--
Finite-PMF primal-transport specialization of Theorem 4.3.  Every
performative optimum and stable point are at most `2 L ε / γ` apart under the
source's data-Lipschitz and strong-convexity conditions.
-/
theorem finiteOptimumStableDistance
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {constant : NNReal} (hloss : IsDataLossLipschitz model constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) :
    ‖optimal - stable‖ ≤ 2 * (constant : ℝ) * sensitivity / modulus :=
  norm_performativelyOptimal_sub_stable_le_of_strongConvex_transport model gradient hgradientAt
    hmodulus hstrong hloss hsensitivity hsensitive optimal stable hoptimal hstable

/-- Finite-PMF W₁ specialization of Theorem 4.3. -/
theorem finiteWassersteinOptimumStableDistance
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {constant : NNReal} (hloss : IsDataLossLipschitz model constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) :
    ‖optimal - stable‖ ≤ 2 * (constant : ℝ) * sensitivity / modulus :=
  norm_performativelyOptimal_sub_stable_le_of_strongConvex_finiteWasserstein model gradient hgradientAt
    hmodulus hstrong hloss hsensitivity hsensitive optimal stable hoptimal hstable

/--
Finite-PMF primal-transport objective-value specialization of Corollary 5.1.
The result is conditional on the supplied stable point; the finite-PMF
Theorem 3.8 route separately constructs such a point under its assumptions.
-/
theorem finiteStableObjectiveGap
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : IsDataLossLipschitz model dataConstant)
    (hparameterLoss : IsParameterLossLipschitz model parameterConstant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) :
    performativeRisk model stable - performativeRisk model optimal ≤
      2 * (dataConstant : ℝ) * sensitivity *
        ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus :=
  performativeRisk_sub_performativelyOptimal_le_of_stable model gradient hgradientAt hmodulus hstrong
    hdataLoss hparameterLoss hsensitivity hsensitive optimal stable hoptimal hstable

/-- Finite-PMF W₁ specialization of Corollary 5.1. -/
theorem finiteWassersteinStableObjectiveGap
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : IsDataLossLipschitz model dataConstant)
    (hparameterLoss : IsParameterLossLipschitz model parameterConstant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) :
    performativeRisk model stable - performativeRisk model optimal ≤
      2 * (dataConstant : ℝ) * sensitivity *
        ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus :=
  performativeRisk_sub_performativelyOptimal_le_of_stable_finiteWasserstein model gradient hgradientAt
    hmodulus hstrong hdataLoss hparameterLoss hsensitivity hsensitive optimal stable hoptimal hstable

end PZMH20PerformativePrediction
