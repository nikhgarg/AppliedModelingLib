import PZMH20PerformativePrediction.PaperInterface

/-!
# Proof Interface: Performative Prediction

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib
open MeasureTheory
open scoped InnerProductSpace

theorem performativeOptimality {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (parameter : Parameter) :
    performativeOptimalitySpec model parameter :=
  Iff.rfl

theorem finitePerformativeOptimumExists {Parameter Data : Type*}
    [Fintype Parameter] [Nonempty Parameter]
    [Fintype Data] [DecidableEq Data] (model : FinitePerformativeModel Parameter Data) :
    finitePerformativeOptimumExistsSpec model :=
  exists_isPerformativelyOptimal model

theorem performativeStability {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (parameter : Parameter) :
    performativeStabilitySpec model parameter :=
  Iff.rfl

theorem rrmFixedPointStable {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (update : Parameter → Parameter)
    (parameter : Parameter) : rrmFixedPointStableSpec model update parameter := by
  intro hrrm hfixed
  exact isPerformativelyStable_of_retraining_fixedPoint model update hrrm hfixed

theorem proposition36aExactDiracCounterexample (epsilon beta _gamma : ℝ) :
    proposition36aExactDiracCounterexampleSpec epsilon beta _gamma := by
  intro hepsilon hbeta _hgamma
  refine ⟨proposition36a_isMeasureRepeatedRiskMinimizationOn hepsilon hbeta,
    hasGradientAt_proposition36aMeasureLoss beta, proposition36aMeasureLoss_convexOn beta,
    proposition36aMeasureGradient_jointSmooth hbeta.le,
    proposition36aMeasureModel_wassersteinSensitive hepsilon.le, ?_, ?_,
    proposition36aMeasureRRMUpdate_not_tendsto_from_one⟩
  · intro modulus hmodulus
    exact proposition36aMeasure_not_pointwiseGradientStronglyConvex hmodulus
  · intro theta
    exact proposition36a_isMeasurePerformativelyStableOn_iff hepsilon hbeta theta

theorem proposition36bExactDiracEndpointCounterexample (epsilon gamma penalty : ℝ) :
    proposition36bExactDiracEndpointCounterexampleSpec epsilon gamma penalty := by
  intro hepsilon hgamma hpenalty
  have hpenalty_pos : 0 < penalty := by
    nlinarith [hpenalty.2]
  refine ⟨proposition36bMeasureModel_wassersteinSensitive hepsilon.le,
    ?_, proposition36bMeasureLoss_not_differentiableAt_lowerEndpoint hepsilon hpenalty_pos,
    proposition36bRRMUpdate_isEndpointMeasureRRM hepsilon hgamma hpenalty,
    proposition36bRRMUpdate_not_tendsto_from_two hepsilon⟩
  intro datum
  exact proposition36bMeasureLoss_strongConvex gamma penalty datum hpenalty_pos.le

theorem proposition36bSourceUniformCounterexample (epsilon beta gamma : ℝ) :
    proposition36bSourceUniformCounterexampleSpec epsilon beta gamma := by
  intro hepsilon _ hgamma
  refine ⟨proposition36bSufficientPenalty epsilon gamma,
    proposition36b_sufficientPenalty_large hepsilon hgamma, ?_⟩
  exact proposition36bExactDiracEndpointCounterexample epsilon gamma
    (proposition36bSufficientPenalty epsilon gamma)

theorem proposition36cExactDiracCounterexample (epsilon initial : ℝ) :
    proposition36cExactDiracCounterexampleSpec epsilon initial := by
  refine ⟨proposition36c_isMeasureRepeatedRiskMinimization epsilon,
    proposition36cGradient_jointSmooth,
    proposition36cMeasureModel_pointwiseGradientStronglyConvex epsilon,
    hasGradientAt_proposition36cLoss, ?_, ?_, ?_, ?_, ?_⟩
  · intro hepsilon
    exact proposition36cMeasureModel_wassersteinSensitive hepsilon
  · intro hepsilon
    subst epsilon
    exact proposition36cMeasureModel_one_no_performativelyStablePoint
  · intro hepsilon theta
    exact proposition36c_isMeasurePerformativelyStable_iff hepsilon theta
  · intro hepsilon hinitial
    exact proposition36cRRMUpdate_tendsto_atTop_of_gt_stable hepsilon hinitial
  · intro hepsilon hinitial
    exact proposition36cRRMUpdate_tendsto_atBot_of_lt_stable hepsilon hinitial

theorem proposition36cFeasibleUniformCounterexample (epsilon beta gamma : ℝ) :
    proposition36cFeasibleUniformCounterexampleSpec epsilon beta gamma := by
  intro hepsilon hbeta hgamma hgamma_le_beta hthreshold
  refine ⟨proposition36cRegularity_isMeasureRepeatedRiskMinimization hgamma epsilon beta,
    proposition36cRegularityGradient_jointSmooth hbeta.le hgamma.le hgamma_le_beta,
    proposition36cRegularityMeasureModel_pointwiseGradientStronglyConvex epsilon beta gamma,
    fun datum candidate =>
      hasGradientAt_proposition36cRegularityLoss beta gamma datum candidate,
    proposition36cRegularityMeasureModel_wassersteinSensitive hepsilon.le, ?_⟩
  exact proposition36cRegularityRRMUpdate_exists_tendsto_atTop hbeta hgamma hthreshold

private theorem hasGradientAt_proposition42Loss
    (datum : Bool × Bool) (candidate : ℝ) :
    HasGradientAt (fun parameter => proposition42Loss parameter datum)
      (proposition42Gradient datum candidate) candidate := by
  rcases datum with ⟨feature, label⟩
  have hderiv :=
    (((hasDerivAt_const candidate (if label then (1 : ℝ) else 0)).sub
      (((hasDerivAt_id candidate).mul_const
        (if feature then (1 : ℝ) else -1)).add_const ((1 : ℝ) / 2))).pow 2).hasGradientAt'
  convert hderiv using 1
  fin_cases feature <;> simp [proposition42Gradient] <;> ring

theorem proposition42CorrectedFiniteWitness : proposition42CorrectedFiniteWitnessSpec := by
  obtain ⟨mu, epsilon, hepsilon, hepsilon_lt, hmu, hmuEpsilon⟩ :=
    proposition42_repaired_parameter_conditions_consistent
  have hepsilon_nonneg : 0 ≤ epsilon := by linarith
  refine ⟨mu, epsilon, hmu, hmuEpsilon, hepsilon, hepsilon_lt, ?_,
    hasGradientAt_proposition42Loss, ?_, proposition42Gradient_jointSmooth, ?_, ?_⟩
  · exact correctedProposition42Model_finiteWassersteinSensitive mu epsilon hmu hmuEpsilon
      hepsilon_nonneg
  · exact proposition42Loss_strongConvex
  · intro theta
    exact performativeRisk_correctedProposition42Model_eq mu epsilon hmu hmuEpsilon theta
  · exact concaveOn_proposition42_sourceQuadratic epsilon mu hepsilon.le

theorem rrmConvergence {Parameter : Type*} [MetricSpace Parameter]
    [CompleteSpace Parameter] [Nonempty Parameter]
    (update : Parameter → Parameter) {K : NNReal} (hcontract : ContractingWith K update)
    (initial : Parameter) : rrmConvergenceSpec update hcontract initial :=
  rrmIteratesTendstoFixedPoint update hcontract initial

theorem measureCompactConvexStablePointExistsProof
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [FiniteDimensional ℝ Parameter] [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (hcompact : IsCompact domain) (hne : domain.Nonempty) (hconvex : Convex ℝ domain)
    (hjoint : Continuous (fun point : Parameter × Parameter =>
      measureDecoupledPerformativeRisk model point.1 point.2))
    (hlossConvex : ∀ datum, ConvexOn ℝ domain (model.loss datum)) :
    measureCompactConvexStablePointExistsSpec model domain hcompact hne hconvex hjoint
      hlossConvex :=
  measureCompactConvexStablePointExists model domain hcompact hne hconvex hjoint hlossConvex

theorem measureWassersteinOptimumStableDistanceProof
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [MeasurableSpace Data] [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    {constant : NNReal} (hloss : model.IsDataLossLipschitz constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (optimal stable : domain)
    (hoptimal : model.IsPerformativelyOptimal optimal)
    (hstable : model.IsPerformativelyStable stable) :
    measureWassersteinOptimumStableDistanceSpec model gradient hclosed hconvex hmodulus
      hstrong hloss hsensitivity hsensitive optimal stable hoptimal hstable :=
  measureWassersteinOptimumStableDistance model gradient hclosed hconvex hmodulus
    hstrong hloss hsensitivity hsensitive optimal stable hoptimal hstable

theorem measureWassersteinStableObjectiveGapProof
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
    (update : Parameter → Parameter) (hrrm : IsMeasureRRM model update)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial optimal : Parameter)
    (hoptimal : IsMeasurePerformativelyOptimal model optimal)
    :
    measureWassersteinStableObjectiveGapSpec model gradient hjoint hintegrable hloss_meas
      hpointwise hmodulus hstrong hdataLoss hparameterLoss hsensitivity hsensitive update hrrm
      hfactor initial optimal hoptimal := by
  have hrrmOn : IsMeasureRRMOn model Set.univ update := by
    intro deployed _
    exact ⟨Set.mem_univ _, fun candidate _ => hrrm deployed candidate⟩
  obtain ⟨stable, _, hstableOn, huniqueOn, hconverges, hrate⟩ :=
    measureWassersteinConvexRRMConvergesLinearly_of_A1_A2 model gradient hjoint hintegrable
      hsensitivity hmodulus hsensitive hstrong Set.univ isClosed_univ convex_univ update hrrmOn
      hloss_meas hpointwise hfactor initial (Set.mem_univ initial)
  have hstable : IsMeasurePerformativelyStable model stable := fun candidate =>
    hstableOn.2 candidate (Set.mem_univ candidate)
  have hunique : ∀ other, IsMeasurePerformativelyStable model other → other = stable := by
    intro other hother
    exact huniqueOn other (Set.mem_univ other)
      ⟨Set.mem_univ other, fun candidate _ => hother candidate⟩
  have hgap := measureWassersteinStableObjectiveGap model gradient hjoint hintegrable hloss_meas
    hpointwise hmodulus hstrong hdataLoss hparameterLoss hsensitivity hsensitive optimal stable
    hoptimal hstable
  exact ⟨stable, hstable, hunique, hconverges, hrate, hgap⟩

theorem repeatedGradientDescent
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (project : Parameter → Parameter)
    (stepSize : ℝ) :
    repeatedGradientDescentSpec model gradient project stepSize := by
  intro deployed
  rfl

theorem repeatedEmpiricalRiskMinimization
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (domain : Set Parameter)
    {sampleCount : ℕ} (samples : Parameter → Fin sampleCount → Data)
    (update : Parameter → Parameter) :
    repeatedEmpiricalRiskMinimizationSpec model domain samples update :=
  Iff.rfl

theorem repeatedEmpiricalGradientDescent
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data]
    (gradient : Data → Parameter → Parameter) (project : Parameter → Parameter)
    (stepSize : ℝ) {sampleCount : ℕ} (sample : Fin sampleCount → Data) :
    repeatedEmpiricalGradientDescentSpec gradient project stepSize sample := by
  intro deployed
  rfl

theorem finiteTransportSensitivityLipschitzStatistic
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (sensitivity : ℝ)
    {L : NNReal} {statistic : Data → ℝ} (hstatistic : LipschitzWith L statistic)
    (first second : Parameter) :
    finiteTransportSensitivityLipschitzStatisticSpec model sensitivity hstatistic first second := by
  intro hsensitive
  exact finiteTransportSensitive_lipschitzStatistic model hsensitive hstatistic first second

theorem finiteWassersteinSensitivityLipschitzStatistic
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (sensitivity : ℝ)
    {L : NNReal} {statistic : Data → ℝ} (hstatistic : LipschitzWith L statistic)
    (first second : Parameter) :
    finiteWassersteinSensitivityLipschitzStatisticSpec model sensitivity hstatistic first second := by
  intro hsensitive
  exact finiteWassersteinSensitive_lipschitzStatistic model hsensitive hstatistic first second

theorem finiteTransportSensitivityGradientPairing
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (smoothness sensitivity : ℝ)
    (displacement evaluated first second : Parameter) :
    finiteTransportSensitivityGradientPairingSpec model gradient smoothness sensitivity
      displacement evaluated first second := by
  intro hsmoothness hgradient hsensitive
  let smoothnessNN : NNReal := ⟨smoothness, hsmoothness⟩
  have hgradientNN : IsDataGradientLipschitz gradient smoothnessNN := by
    intro left right parameter
    simpa [smoothnessNN] using hgradient left right parameter
  have hbound := finiteTransportSensitive_gradientPairing model gradient hgradientNN hsensitive
    displacement evaluated first second
  simpa [smoothnessNN, coe_nnnorm, mul_assoc] using hbound

theorem finiteWassersteinSensitivityGradientPairing
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (smoothness sensitivity : ℝ)
    (displacement evaluated first second : Parameter) :
    finiteWassersteinSensitivityGradientPairingSpec model gradient smoothness sensitivity
      displacement evaluated first second := by
  intro hsmoothness hgradient hsensitive
  let smoothnessNN : NNReal := ⟨smoothness, hsmoothness⟩
  have hgradientNN : IsDataGradientLipschitz gradient smoothnessNN := by
    intro left right parameter
    simpa [smoothnessNN] using hgradient left right parameter
  have hbound := finiteWassersteinSensitive_gradientPairing model gradient hgradientNN hsensitive
    displacement evaluated first second
  simpa [smoothnessNN, coe_nnnorm, mul_assoc] using hbound

theorem finiteUnconstrainedRRMContractionProof
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
    finiteUnconstrainedRRMContractionSpec model gradient hgradientAt hjoint hsensitivity hmodulus
      hsensitive hstrong update hrrm first second :=
  finiteUnconstrainedRRMContraction model gradient hgradientAt hjoint hsensitivity hmodulus
    hsensitive hstrong update hrrm first second

theorem finiteWassersteinUnconstrainedRRMContractionProof
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
    finiteWassersteinUnconstrainedRRMContractionSpec model gradient hgradientAt hjoint hsensitivity
      hmodulus hsensitive hstrong update hrrm first second :=
  finiteWassersteinUnconstrainedRRMContraction model gradient hgradientAt hjoint hsensitivity hmodulus
    hsensitive hstrong update hrrm first second

theorem finiteWassersteinConvexRRMContractionProof
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
    finiteWassersteinConvexRRMContractionSpec model gradient hgradientAt hjoint hsensitivity hmodulus
      hsensitive hstrong domain hconvex update hrrm first second hfirst hsecond :=
  finiteWassersteinConvexRRMContraction model gradient hgradientAt hjoint hsensitivity hmodulus
    hsensitive hstrong domain hconvex update hrrm first second hfirst hsecond

theorem finiteWassersteinConvexRRMConvergesLinearlyProof
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
    finiteWassersteinConvexRRMConvergesLinearlySpec model gradient hgradientAt hjoint hsensitivity
      hmodulus hsensitive hstrong domain hclosed hconvex update hrrm hfactor initial hinitial := by
  simpa [IsStableOn] using
    finiteWassersteinConvexRRMConvergesLinearly model gradient hgradientAt hjoint hsensitivity
      hmodulus hsensitive hstrong domain hclosed hconvex update hrrm hfactor initial hinitial

theorem measureWassersteinUnconstrainedRRMConvergesLinearlyProof
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
    measureWassersteinUnconstrainedRRMConvergesLinearlySpec model gradient hgradient hintegrable
      hsensitivity hmodulus hsensitive update hrrm hgradientAt hstrong hfactor initial := by
  exact measureWassersteinUnconstrainedRRMConvergesLinearly model gradient hgradient hintegrable
    hsensitivity hmodulus hsensitive update hrrm hgradientAt hstrong hfactor initial

theorem measureWassersteinConvexRRMContractionProof
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
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    measureWassersteinConvexRRMContractionSpec model gradient hjoint hintegrable hsensitivity
      hmodulus hsensitive domain hconvex update hrrm hloss_meas hpointwise hstrong first second hfirst hsecond :=
  measureWassersteinConvexRRMContraction_of_A1_A2 model gradient hjoint hintegrable hsensitivity
    hmodulus hsensitive hstrong domain hconvex update hrrm hloss_meas hpointwise first second hfirst hsecond

theorem measureWassersteinConvexRRMConvergesLinearlyProof
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
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) :
    measureWassersteinConvexRRMConvergesLinearlySpec model gradient hjoint hintegrable hsensitivity
      hmodulus hsensitive domain hclosed hconvex update hrrm hloss_meas hpointwise hstrong hfactor initial hinitial :=
  ⟨fun first hfirst second hsecond =>
      measureWassersteinConvexRRMContractionProof model gradient hjoint hintegrable hsensitivity
        hmodulus hsensitive domain hconvex update hrrm hloss_meas hpointwise hstrong first second
        hfirst hsecond,
    measureWassersteinConvexRRMConvergesLinearly_of_A1_A2 model gradient hjoint hintegrable
      hsensitivity hmodulus hsensitive hstrong domain hclosed hconvex update hrrm hloss_meas
      hpointwise hfactor initial hinitial⟩

theorem measureWassersteinConvexRGDConvergesLinearlyProof
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
    measureWassersteinConvexRGDConvergesLinearlySpec model gradient hjoint hintegrable hsensitivity
      hsensitive hmodulus hmodulus_le hstrong domain hclosed hnonempty hconvex project hproject
      hproject_nonexpansive stepSize hstepSize hstepSize_le hsensitivity_small hloss_meas hpointwise
      initial hinitial := by
  constructor
  · intro first _ second _
    simpa only [dist_eq_norm] using
      dist_measureRepeatedGradientDescentUpdate_sub_le_of_A1_A2_wassersteinSensitive
        model gradient hjoint hintegrable hsensitivity hsensitive hmodulus hmodulus_le hstrong
        project hproject_nonexpansive stepSize hstepSize.le hstepSize_le hsensitivity_small
        hloss_meas hpointwise first second
  · exact measureWassersteinConvexRGDConvergesLinearly_of_A1_A2
      model gradient hjoint hintegrable hsensitivity hsensitive hmodulus hmodulus_le hstrong domain
        hclosed hnonempty hconvex project hproject hproject_nonexpansive stepSize hstepSize
        hstepSize_le hsensitivity_small hloss_meas hpointwise initial hinitial

theorem finiteConvexRRMContractionProof
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
    finiteConvexRRMContractionSpec model gradient hgradientAt hjoint hsensitivity hmodulus
      hsensitive hstrong domain hconvex update hrrm first second hfirst hsecond :=
  finiteConvexRRMContraction model gradient hgradientAt hjoint hsensitivity hmodulus
    hsensitive hstrong domain hconvex update hrrm first second hfirst hsecond

theorem finiteConvexRRMConvergesLinearlyProof
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
    finiteConvexRRMConvergesLinearlySpec model gradient hgradientAt hjoint hsensitivity hmodulus
      hsensitive hstrong domain hclosed hconvex update hrrm hfactor initial hinitial := by
  simpa [IsStableOn] using finiteConvexRRMConvergesLinearly model gradient hgradientAt hjoint
    hsensitivity hmodulus hsensitive hstrong domain hclosed hconvex update hrrm hfactor initial hinitial

theorem finiteConvexRGDConvergesLinearlyProof
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hnonempty : domain.Nonempty)
    (hconvex : Convex ℝ domain) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (initial : Parameter) (hinitial : initial ∈ domain) :
    finiteConvexRGDConvergesLinearlySpec model gradient hjoint hgradientAt hsensitivity hsensitive
      hmodulus hmodulus_le hstrong domain hclosed hnonempty hconvex project hproject
      hproject_nonexpansive stepSize hstepSize hstepSize_le hsensitivity_small initial hinitial := by
  simpa [IsStableOn] using
    repeatedGradientDescent_convergesLinearly_of_interpolation_transport model gradient hjoint
      hgradientAt hsensitivity hsensitive hmodulus hmodulus_le hstrong domain hclosed hnonempty
      hconvex project hproject hproject_nonexpansive stepSize hstepSize hstepSize_le
      hsensitivity_small initial hinitial

theorem finiteWassersteinConvexRGDConvergesLinearlyProof
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hnonempty : domain.Nonempty)
    (hconvex : Convex ℝ domain) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (initial : Parameter) (hinitial : initial ∈ domain) :
    finiteWassersteinConvexRGDConvergesLinearlySpec model gradient hjoint hgradientAt hsensitivity
      hsensitive hmodulus hmodulus_le hstrong domain hclosed hnonempty hconvex project hproject
      hproject_nonexpansive stepSize hstepSize hstepSize_le hsensitivity_small initial hinitial := by
  simpa [IsStableOn] using
    repeatedGradientDescent_convergesLinearly_of_interpolation_finiteWasserstein model gradient hjoint
      hgradientAt hsensitivity hsensitive hmodulus hmodulus_le hstrong domain hclosed hnonempty
      hconvex project hproject hproject_nonexpansive stepSize hstepSize hstepSize_le
      hsensitivity_small initial hinitial

theorem finiteOptimumStableDistanceProof
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
    finiteOptimumStableDistanceSpec model gradient hgradientAt hmodulus hstrong hloss hsensitivity
      hsensitive optimal stable hoptimal hstable :=
  finiteOptimumStableDistance model gradient hgradientAt hmodulus hstrong hloss hsensitivity
    hsensitive optimal stable hoptimal hstable

theorem finiteWassersteinOptimumStableDistanceProof
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
    finiteWassersteinOptimumStableDistanceSpec model gradient hgradientAt hmodulus hstrong hloss
      hsensitivity hsensitive optimal stable hoptimal hstable :=
  finiteWassersteinOptimumStableDistance model gradient hgradientAt hmodulus hstrong hloss hsensitivity
    hsensitive optimal stable hoptimal hstable

theorem finiteStableObjectiveGapProof
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
    finiteStableObjectiveGapSpec model gradient hgradientAt hmodulus hstrong hdataLoss hparameterLoss
      hsensitivity hsensitive optimal stable hoptimal hstable :=
  finiteStableObjectiveGap model gradient hgradientAt hmodulus hstrong hdataLoss hparameterLoss
    hsensitivity hsensitive optimal stable hoptimal hstable

theorem finiteWassersteinStableObjectiveGapProof
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
    finiteWassersteinStableObjectiveGapSpec model gradient hgradientAt hmodulus hstrong hdataLoss
      hparameterLoss hsensitivity hsensitive optimal stable hoptimal hstable :=
  finiteWassersteinStableObjectiveGap model gradient hgradientAt hmodulus hstrong hdataLoss
    hparameterLoss hsensitivity hsensitive optimal stable hoptimal hstable

theorem theorem310RERMConstrainedPopulationData
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity_nonneg : 0 ≤ sensitivity)
    (hsmoothness_pos : 0 < (smoothness : ℝ)) (hmodulus_pos : 0 < modulus)
    (hsensitivity_lt : sensitivity < modulus / (2 * (smoothness : ℝ)))
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable) :
    theorem310RERMConstrainedPopulationDataSpec model gradient smoothness sensitivity modulus
      domain populationUpdate stable := by
  exact rermOn_theorem310PopulationData_of_A1_A2 model gradient hjoint hintegrable
    hsensitivity_nonneg hsmoothness_pos hmodulus_pos hsensitivity_lt hsensitive hstrong
      domain hconvex populationUpdate hpopulation hloss_meas hpointwise stable hstable

theorem theorem310RGDPopulationData
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity_nonneg : 0 ≤ sensitivity)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (hmodulus_pos : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (project : Parameter → Parameter) (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize_pos : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable) :
    theorem310RGDPopulationDataSpec model gradient smoothness sensitivity modulus stepSize project stable := by
  exact rgd_theorem310PopulationData_of_A1_A2 model gradient hjoint hintegrable
    hsensitivity_nonneg hsensitive hmodulus_pos hmodulus_le hstrong domain hconvex project hproject
      hproject_nonexpansive stepSize hstepSize_pos hstepSize_le hsensitivity_small hloss_meas
      hpointwise stable hstable

theorem theorem310CompactContinuousMomentEnvelope
    {Parameter : Type*} [TopologicalSpace Parameter]
    (dimension : ℕ)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (domain : Set Parameter) (alpha gamma : ℝ)
    (hcompact : IsCompact domain)
    (hmoment : ∀ parameter ∈ domain,
      Probability.HasExponentialRadialMoment (model.dataLaw parameter) alpha gamma)
    (hcontinuous : ContinuousOn (fun parameter =>
      ∫ datum : EuclideanSpace ℝ (Fin dimension),
        Real.exp (gamma * Real.rpow ‖datum‖ alpha) ∂(model.dataLaw parameter : Measure _))
        domain)
    (countSchedule : ℕ → ℕ)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun round => Fin (countSchedule round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hdeployed : ∀ iteration history, deployedOfHistory iteration history ∈ domain) :
    theorem310CompactContinuousMomentEnvelopeSpec dimension model domain alpha gamma hcompact
      hmoment hcontinuous countSchedule deployedOfHistory hdeployed := by
  exact exists_boundedExponentialRadialMoment_for_deployedHistory_of_compact_continuous
    dimension model domain alpha gamma hcompact hmoment hcontinuous countSchedule deployedOfHistory hdeployed

theorem theorem310CorrectedRGDAllRoundTrajectory
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (dimension cutoff : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment : tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (sampling : MeasurePerformativeSamplingKernel model)
    (gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hsmoothness : smoothness ≠ 0)
    (project : Parameter → Parameter) (hproject : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 ≤ stepSize)
    (hcountPositive : ∀ round,
      0 < pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : ∀ iteration history batch,
      deployedOfHistory (iteration + 1) (heterogeneousBatchTraceSnoc history batch) =
        measureSampledGradientDescentUpdate gradient project stepSize
          (hcountPositive iteration) batch (deployedOfHistory iteration history))
    (hintegrablePopulation : ∀ deployed,
      Integrable (fun datum => gradient datum deployed) (model.dataLaw deployed :
        Measure (EuclideanSpace ℝ (Fin dimension))))
    (hintegrableEmpirical : ∀ (iteration : ℕ)
      (history : HeterogeneousBatchTrace
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration)
      (batch : Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance iteration) →
        EuclideanSpace ℝ (Fin dimension)),
      Integrable (fun datum => gradient datum (deployedOfHistory iteration history))
        (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch :
          Measure (EuclideanSpace ℝ (Fin dimension))))
    (stable : Parameter) {contraction outerContraction wassersteinBound radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_le_outer : contraction ≤ outerContraction)
    (hstable : measureRepeatedGradientDescentUpdate model gradient project stepSize stable = stable)
    (hcontract : ∀ parameter,
      dist (measureRepeatedGradientDescentUpdate model gradient project stepSize parameter)
        (measureRepeatedGradientDescentUpdate model gradient project stepSize stable) ≤
        contraction * dist parameter stable)
    (hbound_nonneg : 0 ≤ wassersteinBound)
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤ wassersteinBound)
    (herror_outer : stepSize * (smoothness : ℝ) * wassersteinBound ≤
      (outerContraction - contraction) * radius)
    (herror_absorbed : stepSize * (smoothness : ℝ) * wassersteinBound ≤
      (1 - contraction) * radius)
    (initialDistance : ℝ)
    (houter_lt_one : outerContraction < 1)
    (hradius_pos : 0 < radius)
    (hinitialDistance : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      dist (deployedOfHistory 0 history) stable ≤ initialDistance)
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
          dimension cutoff eta
          (pOneFournierGuillinTheorem310CappedDeviation
            dimension eta alpha gamma momentBound scaledDeviation)
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
            dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
          (measurePerformativeDeployedLaw model
            (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
              dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
            deployedOfHistory)) iteration))
    : theorem310CorrectedRGDAllRoundTrajectorySpec dimension cutoff hdimension heta_pos heta_le_one
      halpha_pos hgamma_pos halpha_gap hscaled hscaled_pos hscaled_le_one htailBound_pos
      htailEnvelope p headTolerance hp hheadTolerance htailBound_moment model sampling gradient
      hjoint hsmoothness project hproject stepSize hstepSize hcountPositive deployedOfHistory
      hmeasurableDeployed hempirical hintegrablePopulation hintegrableEmpirical stable
      hcontraction_nonneg hcontraction_le_outer hstable hcontract hbound_nonneg hbudget
      herror_outer herror_absorbed initialDistance houter_lt_one hradius_pos hinitialDistance
      hmoment hevent := by
  obtain ⟨entryIteration, hentry⟩ :=
    exists_entryIteration_for_deployedHistory_of_uniformInitialDistance
      (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
      deployedOfHistory stable outerContraction initialDistance radius
      (hcontraction_nonneg.trans hcontraction_le_outer) houter_lt_one hradius_pos hinitialDistance
  refine ⟨entryIteration, ?_⟩
  simpa only [theorem310CorrectedRGDAllRoundTrajectorySpec] using
    one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateRGDState_le_radius_after_of_supercriticalCappedConcreteSchedule
      dimension cutoff hdimension heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap hscaled
        hscaled_pos hscaled_le_one htailBound_pos htailEnvelope p headTolerance hp hheadTolerance
        htailBound_moment model sampling gradient hjoint hsmoothness project hproject stepSize
        hstepSize hcountPositive deployedOfHistory hmeasurableDeployed hempirical
        hintegrablePopulation hintegrableEmpirical stable hcontraction_nonneg hcontraction_le_outer
        hstable hcontract hbound_nonneg hbudget herror_outer herror_absorbed entryIteration hentry
        hmoment hevent

/-- The source-facing record review surface is realized by the corrected RGD
endpoint without changing its mathematical assumptions or conclusion. -/
theorem theorem310CorrectedRGDAllRoundTrajectoryReview
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (data : Theorem310CorrectedRGDAllRoundTrajectoryData Parameter) :
    theorem310CorrectedRGDAllRoundTrajectoryReviewSpec data := by
  have hpopulation :=
    rgd_theorem310PopulationData_of_A1_A2 data.model data.gradient data.hjoint data.hintegrable
      data.hsensitivity_nonneg data.hsensitive data.hmodulus_pos data.hmodulus_le data.hstrong
      data.domain data.hconvex data.project data.hprojectVariational data.hproject data.stepSize
      data.hstepSize_pos data.hstepSize_le data.hsensitivity_small data.hloss_meas data.hpointwise
      data.stable data.hstablePerformative
  have hcontraction_nonneg : 0 ≤ data.contraction := by
    rw [data.hcontraction_eq]
    exact hpopulation.1.1
  have hcontract : ∀ parameter,
      dist (measureRepeatedGradientDescentUpdate data.model data.gradient data.project
        data.stepSize parameter)
        (measureRepeatedGradientDescentUpdate data.model data.gradient data.project
          data.stepSize data.stable) ≤ data.contraction * dist parameter data.stable := by
    intro parameter
    rw [data.hcontraction_eq]
    exact hpopulation.2.2 parameter
  obtain ⟨entryIteration, hentry⟩ :=
    exists_entryIteration_for_deployedHistory_of_uniformInitialDistance
      (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        data.dimension data.cutoff data.eta data.alpha data.gamma data.momentBound data.tailBound
          data.scaledDeviation data.p data.headTolerance)
      data.deployedOfHistory data.stable data.outerContraction data.initialDistance data.radius
      (hcontraction_nonneg.trans data.hcontraction_le_outer) data.houter_lt_one
      data.hradius_pos data.hinitialDistance
  refine ⟨entryIteration, ?_⟩
  simpa only [theorem310CorrectedRGDAllRoundTrajectoryReviewSpec] using
    one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateRGDState_le_radius_after_of_supercriticalCappedConcreteSchedule
      data.dimension data.cutoff data.hdimension data.heta_pos data.heta_le_one data.halpha_pos
        data.hgamma_pos data.halpha_gap data.hscaled data.hscaled_pos data.hscaled_le_one
        data.htailBound_pos data.htailEnvelope data.p data.headTolerance data.hp data.hheadTolerance
        data.htailBound_moment data.model data.sampling data.gradient data.hjoint data.hsmoothness
        data.project data.hproject data.stepSize data.hstepSize data.hcountPositive
        data.deployedOfHistory data.hmeasurableDeployed data.hempirical
        (fun deployed => data.hintegrable deployed deployed)
        data.hintegrableEmpirical data.stable hcontraction_nonneg data.hcontraction_le_outer
        hpopulation.2.1 hcontract data.hbound_nonneg data.hbudget data.herror_outer
        data.herror_absorbed entryIteration hentry data.hmoment data.hevent

theorem theorem310CorrectedRERMAllRoundTrajectory
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (dimension cutoff : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment : tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (sampling : MeasurePerformativeSamplingKernel model)
    {constant : NNReal} (hloss : IsMeasureDataLossLipschitz model constant)
    (hconstant : constant ≠ 0)
    (gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure (EuclideanSpace ℝ (Fin dimension))))
    (domain : Set Parameter)
    (hcountPositive : ∀ round,
      0 < pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn model domain
      (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
      hcountPositive deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (hfirstOrder : ∀ deployed ∈ domain,
      IsMeasureFrozenGradientFirstOrderOptimalOn model gradient domain deployed
        (populationUpdate deployed))
    (stable : Parameter) {contraction outerContraction wassersteinBound tolerance radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_le_outer : contraction ≤ outerContraction)
    (hstable : populationUpdate stable = stable)
    (hcontract : ∀ parameter ∈ domain,
      dist (populationUpdate parameter) (populationUpdate stable) ≤
        contraction * dist parameter stable)
    (htolerance_nonneg : 0 ≤ tolerance)
    (hinitial : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      deployedOfHistory 0 history ∈ domain)
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤ wassersteinBound)
    (herror_outer : Real.sqrt (4 * tolerance / modulus) ≤
      (outerContraction - contraction) * radius)
    (herror_absorbed : Real.sqrt (4 * tolerance / modulus) ≤ (1 - contraction) * radius)
    (initialDistance : ℝ)
    (houter_lt_one : outerContraction < 1)
    (hradius_pos : 0 < radius)
    (hinitialDistance : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      dist (deployedOfHistory 0 history) stable ≤ initialDistance)
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hintegrableEmpiricalLoss : ∀ (iteration : ℕ)
      (history : HeterogeneousBatchTrace
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration)
      (batch : Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance iteration) →
        EuclideanSpace ℝ (Fin dimension))
      candidate, candidate ∈ domain →
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch :
          Measure (EuclideanSpace ℝ (Fin dimension))))
    (hbound_nonneg : 0 ≤ wassersteinBound)
    (htolerance : (constant : ℝ) * wassersteinBound ≤ tolerance)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
          dimension cutoff eta
          (pOneFournierGuillinTheorem310CappedDeviation
            dimension eta alpha gamma momentBound scaledDeviation)
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
            dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
          (measurePerformativeDeployedLaw model
            (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
              dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
            deployedOfHistory)) iteration))
    : theorem310CorrectedRERMAllRoundTrajectorySpec dimension cutoff hdimension heta_pos heta_le_one
      halpha_pos hgamma_pos halpha_gap hscaled hscaled_pos hscaled_le_one htailBound_pos
      htailEnvelope p headTolerance hp hheadTolerance htailBound_moment model sampling hloss
      hconstant gradient hmodulus hstrong hintegrable domain hcountPositive deployedOfHistory
      hmeasurableDeployed hempirical populationUpdate hpopulation hfirstOrder stable
      hcontraction_nonneg hcontraction_le_outer hstable hcontract htolerance_nonneg hinitial
      hbudget herror_outer herror_absorbed initialDistance houter_lt_one hradius_pos
      hinitialDistance hmoment hintegrableEmpiricalLoss hbound_nonneg htolerance hevent := by
  obtain ⟨entryIteration, hentry⟩ :=
    exists_entryIteration_for_deployedHistory_of_uniformInitialDistance
      (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
      deployedOfHistory stable outerContraction initialDistance radius
      (hcontraction_nonneg.trans hcontraction_le_outer) houter_lt_one hradius_pos hinitialDistance
  refine ⟨entryIteration, ?_⟩
  simpa only [theorem310CorrectedRERMAllRoundTrajectorySpec] using
    one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateRERMState_le_radius_after_of_supercriticalCappedConcreteSchedule
      dimension cutoff hdimension heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap hscaled
        hscaled_pos hscaled_le_one htailBound_pos htailEnvelope p headTolerance hp hheadTolerance
        htailBound_moment model sampling hloss hconstant gradient hmodulus hstrong hintegrable domain
        hcountPositive deployedOfHistory hmeasurableDeployed hempirical populationUpdate hpopulation
        hfirstOrder stable hcontraction_nonneg hcontraction_le_outer hstable hcontract
        htolerance_nonneg hinitial hbudget herror_outer herror_absorbed entryIteration hentry
        hmoment hintegrableEmpiricalLoss hbound_nonneg htolerance hevent

/-- The source-facing record review surface is realized by the same corrected
RERM endpoint as the full public theorem above. -/
theorem theorem310CorrectedRERMAllRoundTrajectoryReview
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (data : Theorem310CorrectedRERMAllRoundTrajectoryData Parameter) :
    theorem310CorrectedRERMAllRoundTrajectoryReviewSpec data := by
  have hpopulation :=
    rermOn_theorem310PopulationData_of_A1_A2 data.model data.gradient data.hjoint data.hintegrable
      data.hsensitivity_nonneg data.hsmoothness_pos data.hmodulus data.hsensitivity_lt
      data.hsensitive data.hstrong data.domain data.hconvex data.populationUpdate data.hpopulation
      data.hloss_meas data.hpointwise data.stable data.hstablePerformative
  have hcontraction_nonneg : 0 ≤ data.contraction := by
    rw [data.hcontraction_eq]
    exact hpopulation.1.1
  have hcontract : ∀ parameter ∈ data.domain,
      dist (data.populationUpdate parameter) (data.populationUpdate data.stable) ≤
        data.contraction * dist parameter data.stable := by
    intro parameter hparameter
    rw [data.hcontraction_eq]
    exact hpopulation.2.2.1 parameter hparameter data.stable data.hstablePerformative.1
  obtain ⟨entryIteration, hentry⟩ :=
    exists_entryIteration_for_deployedHistory_of_uniformInitialDistance
      (theorem310CorrectedRERMCountSchedule data.dimension data.cutoff data.eta data.alpha
        data.gamma data.momentBound data.tailBound data.scaledDeviation data.p data.headTolerance)
      data.deployedOfHistory data.stable data.outerContraction data.initialDistance data.radius
      (hcontraction_nonneg.trans data.hcontraction_le_outer) data.houter_lt_one
      data.hradius_pos data.hinitialDistance
  refine ⟨entryIteration, ?_⟩
  simpa only [theorem310CorrectedRERMAllRoundTrajectoryReviewSpec,
    theorem310CorrectedRERMCountSchedule] using
    one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateRERMState_le_radius_after_of_supercriticalCappedConcreteSchedule
      data.dimension data.cutoff data.hdimension data.heta_pos data.heta_le_one data.halpha_pos
        data.hgamma_pos data.halpha_gap data.hscaled data.hscaled_pos data.hscaled_le_one
        data.htailBound_pos data.htailEnvelope data.p data.headTolerance data.hp data.hheadTolerance
        data.htailBound_moment data.model data.sampling data.hloss data.hconstant data.gradient
        data.hmodulus data.hstrong data.hintegrable data.domain data.hcountPositive
        data.deployedOfHistory data.hmeasurableDeployed data.hempirical data.populationUpdate
        data.hpopulation hpopulation.2.2.2 data.stable hcontraction_nonneg
        data.hcontraction_le_outer hpopulation.2.1 hcontract data.htolerance_nonneg data.hinitial
        data.hbudget data.herror_outer data.herror_absorbed entryIteration hentry
        data.hmoment data.hintegrableEmpiricalLoss data.hbound_nonneg data.htolerance data.hevent

end PZMH20PerformativePrediction
