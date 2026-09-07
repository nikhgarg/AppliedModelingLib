import LG21TestOptionalPolicies.ObservedAccessPolicySemantics
import LG21TestOptionalPolicies.MandatoryObservedAccessTheorem44FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessTheorem44FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredTheorem44FairnessBridge

/-!
# Semantic policy endpoints for LG21 Theorem 4.4

Theorem 4.4 is a claim about one policy with two observed-access branches.
For each requirement protocol, this module packages the literal access-side
output together with Definition 6's randomized no-access branch and proves
the semantic observable- and demographic-fairness predicates.  The branches
are deliberately independent: the aggregate theorem below does not require
one simultaneous equilibrium carrier for all three requirement regimes.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- The mandatory-given-access source carrier induces a literal Definition 6
two-branch policy that is observably fair up to null public-base fibres and
demographically fair.  Its Gaussian source factorization is selected from the
finite population model, rather than supplied as a policy premise. -/
theorem lg21ContinuousGaussianPopulation_mandatory_resampling_observedAccessFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (reportedPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       letI : IsProbabilityMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
       letI : IsFiniteMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
       LG21ObservedAccessFair M testFeature
        { accessOutput := lg21ObservedAccessActualOutput
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            mandatory.action reportedPayoff noReportPayoff,
          noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S,
          noAccessKernel_isMarkov := inferInstance }) := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := inferInstance
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  have hfair :=
    lg21ContinuousGaussianAccessPopulation_mandatoryObservedAccessOutput_observableAndDemographicFair_of_pbo
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization mandatory reportedPayoff
      noReportPayoff hreportedPBO
  exact lg21ObservedAccessFair_of_kernel_and_outputLaw M testFeature
    (lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      mandatory.action reportedPayoff noReportPayoff)
    (lg21D6NoAccessResamplingEstimateKernel S) hfair.1 hfair.2

/-- The literal source-timed optional carrier induces the same semantic
Definition 6 two-branch policy fairness certificate. -/
theorem lg21ContinuousGaussianPopulation_optional_sourceTimed_resampling_observedAccessFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       letI : IsProbabilityMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
       letI : IsFiniteMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
       LG21ObservedAccessFair M testFeature
        { accessOutput := lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions,
          noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S,
          noAccessKernel_isMarkov := inferInstance }) := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := inferInstance
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  have hactualOutput :=
    lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutput_eq_d6_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance optional baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization
  have hfair :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
      hactualOutput
  exact lg21ObservedAccessFair_of_kernel_and_outputLaw M testFeature
    (lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
    (lg21D6NoAccessResamplingEstimateKernel S) hfair.1 hfair.2

/-- The report-required source carrier has an independent semantic Definition
6 policy certificate.  The only behavioral input is the report-required
positive-mass stability carrier used by the report-required output bridge. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_resampling_observedAccessFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (htestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    ∀ (source : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (source.base_measurable.prodMk
          (source.score_measurable.prodMk source.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       LG21ObservedAccessFair M testFeature
       { accessOutput := lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired,
          noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S,
          noAccessKernel_isMarkov := inferInstance }) := by
  intro source hstable
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := inferInstance
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  have hactualOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance reportRequired htestLaw baseLaw baseMean hbaseMean
      baseVariance hbaseVariance hfactorization source hstable
  have hfair :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
      hactualOutput
  exact lg21ObservedAccessFair_of_kernel_and_outputLaw M testFeature
    (lg21ReportRequiredSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
    (lg21D6NoAccessResamplingEstimateKernel S) hfair.1 hfair.2

/-- Theorem 4.4's three requirement regimes, with one independently
universally quantified source branch for each regime.  This aggregation does
not assert or require a simultaneous mandatory, optional, and
report-required equilibrium. -/
theorem lg21ContinuousGaussianPopulation_allObservedAccessProtocols_resampling_observedAccessFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    (∀ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
        (reportedPayoff :
          (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
        (noReportPayoff :
          (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (hreportedPBO : LG21ObservedAccessAllReportPBO
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff),
      ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
          (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
          (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
          (hbaseLaw : IsProbabilityMeasure baseLaw)
          (hbaseVariance : 0 < baseVariance),
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
            (LG21NonTestFeature Feature testFeature -> ℝ) :=
          { baseLaw := baseLaw
            baseLaw_isProbability := inferInstance
            posteriorBaseMean := baseMean
            posteriorBaseMean_measurable := hbaseMean
            posteriorBaseVariance := baseVariance.toNNReal
            posteriorBaseVariance_pos := by
              rw [NNReal.coe_pos, Real.toNNReal_pos]
              exact hbaseVariance
            testNoiseVariance := M.noiseVariance testFeature
            testNoiseVariance_pos := htestNoiseVariance }
         letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw M) :=
            lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
         letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21ObservedAccessActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              mandatory.action reportedPayoff noReportPayoff
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance })) ∧
    (∀ (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
        M haccess testFeature),
      ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
          (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
          (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
          (hbaseLaw : IsProbabilityMeasure baseLaw)
          (hbaseVariance : 0 < baseVariance),
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
            (LG21NonTestFeature Feature testFeature -> ℝ) :=
          { baseLaw := baseLaw
            baseLaw_isProbability := inferInstance
            posteriorBaseMean := baseMean
            posteriorBaseMean_measurable := hbaseMean
            posteriorBaseVariance := baseVariance.toNNReal
            posteriorBaseVariance_pos := by
              rw [NNReal.coe_pos, Real.toNNReal_pos]
              exact hbaseVariance
            testNoiseVariance := M.noiseVariance testFeature
            testNoiseVariance_pos := htestNoiseVariance }
         letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw M) :=
            lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
         letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance })) ∧
    (∀ (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
          (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
        (htestLaw : ∀ latentSkill publicBase,
          reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
            ((M.noiseVariance testFeature : ℝ).toNNReal)),
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
      ∀ (source : LG21FullPublicReportRequiredSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
        LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          (source.base_measurable.prodMk
            (source.score_measurable.prodMk source.skill_measurable))
          (fun latentSkill publicBase =>
            reportRequired.takeDecision latentSkill publicBase) →
      ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
          (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
          (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
          (hbaseLaw : IsProbabilityMeasure baseLaw)
          (hbaseVariance : 0 < baseVariance),
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         let S : LG21GaussianPBOResamplingSource
            (LG21NonTestFeature Feature testFeature -> ℝ) :=
          { baseLaw := baseLaw
            baseLaw_isProbability := inferInstance
            posteriorBaseMean := baseMean
            posteriorBaseMean_measurable := hbaseMean
            posteriorBaseVariance := baseVariance.toNNReal
            posteriorBaseVariance_pos := by
              rw [NNReal.coe_pos, Real.toNNReal_pos]
              exact hbaseVariance
            testNoiseVariance := M.noiseVariance testFeature
            testNoiseVariance_pos := htestNoiseVariance }
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance })) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mandatory reportedPayoff noReportPayoff hreportedPBO
    exact
      lg21ContinuousGaussianPopulation_mandatory_resampling_observedAccessFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance mandatory reportedPayoff noReportPayoff hreportedPBO
  · intro optional
    exact
      lg21ContinuousGaussianPopulation_optional_sourceTimed_resampling_observedAccessFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional
  · intro reportRequired htestLaw
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    intro source hstable
    exact
      lg21ContinuousGaussianPopulation_reportRequired_resampling_observedAccessFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired htestLaw source hstable

/-- Theorem 4.4 with one fixed Definition 6 policy selected from the source
population before any protocol equilibrium is considered. In particular, the
Gaussian resampling source cannot vary with the mandatory, optional, or
report-required equilibrium quantified below. -/
theorem lg21ContinuousGaussianPopulation_allObservedAccessProtocols_resampling_observedAccessFair_fixedPolicy
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       letI : IsProbabilityMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
       letI : IsFiniteMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
       (∀ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
           (reportedPayoff :
             (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
           (noReportPayoff :
             (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
           (hreportedPBO : LG21ObservedAccessAllReportPBO
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousPopulationFeature testFeature)
             (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff),
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21ObservedAccessActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              mandatory.action reportedPayoff noReportPayoff
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance }) ∧
       (∀ (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
           M haccess testFeature),
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance }) ∧
       (∀ (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
           (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
           (htestLaw : ∀ latentSkill publicBase,
             reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
               ((M.noiseVariance testFeature : ℝ).toNNReal))
           (source : LG21FullPublicReportRequiredSourceEquilibrium
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousPopulationFeature testFeature)
             (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
         LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
           (lg21ContinuousGaussianAccessPopulationLaw M)
           (lg21ContinuousPopulationBase testFeature)
           (lg21ContinuousPopulationFeature testFeature)
           (lg21ContinuousPopulationSkill (Feature := Feature))
           (source.base_measurable.prodMk
             (source.score_measurable.prodMk source.skill_measurable))
           (fun latentSkill publicBase =>
             reportRequired.takeDecision latentSkill publicBase) →
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance })) := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := inferInstance
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro mandatory reportedPayoff noReportPayoff hreportedPBO
    have hfair :=
      lg21ContinuousGaussianAccessPopulation_mandatoryObservedAccessOutput_observableAndDemographicFair_of_pbo
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfactorization mandatory reportedPayoff
        noReportPayoff hreportedPBO
    exact lg21ObservedAccessFair_of_kernel_and_outputLaw M testFeature
      (lg21ObservedAccessActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        mandatory.action reportedPayoff noReportPayoff)
      (lg21D6NoAccessResamplingEstimateKernel S) hfair.1 hfair.2
  · intro optional
    have hactualOutput :=
      lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutput_eq_d6_ae
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional baseLaw baseMean hbaseMean baseVariance
        hbaseVariance hfactorization
    have hfair :=
      lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfactorization
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
        hactualOutput
    exact lg21ObservedAccessFair_of_kernel_and_outputLaw M testFeature
      (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
      (lg21D6NoAccessResamplingEstimateKernel S) hfair.1 hfair.2
  · intro reportRequired htestLaw source hstable
    have hactualOutput :=
      lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired htestLaw baseLaw baseMean hbaseMean
        baseVariance hbaseVariance hfactorization source hstable
    have hfair :=
      lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfactorization
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
        hactualOutput
    exact lg21ObservedAccessFair_of_kernel_and_outputLaw M testFeature
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
      (lg21D6NoAccessResamplingEstimateKernel S) hfair.1 hfair.2

end

end LG21TestOptionalPolicies
