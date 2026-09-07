import LG21TestOptionalPolicies.MandatoryObservedAccessProposition43FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessOptionalProposition43SourceTimedBridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredProposition43Bridge
import LG21TestOptionalPolicies.ObservedAccessPolicySemantics

/-!
# Total-policy Proposition 4.3 endpoints for LG21

The raw Gaussian bridges establish inequalities for the actual `Z = 1` and
`Z = 0` conditional populations. This module packages those two branches
into one literal policy output, dispatched by the source access indicator.
It then refutes the transparent RCD-a.e. observable-fairness and demographic
fairness predicates for that one policy. No value is prescribed on an
unattained conditioning fibre.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-! ## Generic transport from component outputs to a total policy -/

/-- A componentwise observable-law gap refutes observable fairness of the
single access-dispatched policy, provided its two branches agree almost
everywhere with the corresponding attained-population outputs. -/
theorem lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
    {Omega Base Estimate : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Estimate]
    [StandardBorelSpace Estimate] [Nonempty Estimate]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (base : Omega -> Base) (accessLaw noAccessLaw : Measure Omega)
    [IsFiniteMeasure accessLaw] [IsFiniteMeasure noAccessLaw]
    (hasAccess : Omega -> Bool) (accessOutput noAccessOutput : Omega -> Estimate)
    (haccessBranch : ∀ᵐ omega ∂accessLaw, hasAccess omega = true)
    (hnoAccessBranch : ∀ᵐ omega ∂noAccessLaw, hasAccess omega = false)
    (hgap : ∀ᵐ publicBase ∂baseLaw,
      condDistrib accessOutput base accessLaw publicBase ≠
        condDistrib noAccessOutput base noAccessLaw publicBase) :
    ¬ LG21ObservedAccessDeterministicObservableFairAE
      baseLaw base accessLaw noAccessLaw
      (lg21ObservedAccessDeterministicTwoBranchOutput
        hasAccess accessOutput noAccessOutput) := by
  intro hfair
  have haccessOutput :
      lg21ObservedAccessDeterministicTwoBranchOutput
        hasAccess accessOutput noAccessOutput =ᵐ[
        accessLaw] accessOutput :=
    lg21ObservedAccessDeterministicTwoBranchOutput_eq_access_ae
      accessLaw hasAccess accessOutput noAccessOutput haccessBranch
  have hnoAccessOutput :
      lg21ObservedAccessDeterministicTwoBranchOutput
        hasAccess accessOutput noAccessOutput =ᵐ[
        noAccessLaw] noAccessOutput :=
    lg21ObservedAccessDeterministicTwoBranchOutput_eq_noAccess_ae
      noAccessLaw hasAccess accessOutput noAccessOutput hnoAccessBranch
  have haccessKernel :
      condDistrib
          (lg21ObservedAccessDeterministicTwoBranchOutput
            hasAccess accessOutput noAccessOutput)
          base accessLaw =
        condDistrib accessOutput base accessLaw :=
    condDistrib_congr_left haccessOutput
  have hnoAccessKernel :
      condDistrib
          (lg21ObservedAccessDeterministicTwoBranchOutput
            hasAccess accessOutput noAccessOutput)
          base noAccessLaw =
        condDistrib noAccessOutput base noAccessLaw :=
    condDistrib_congr_left hnoAccessOutput
  have hfairConditional :
      condDistrib
          (lg21ObservedAccessDeterministicTwoBranchOutput
            hasAccess accessOutput noAccessOutput)
          base accessLaw =ᵐ[baseLaw]
        condDistrib
          (lg21ObservedAccessDeterministicTwoBranchOutput
            hasAccess accessOutput noAccessOutput)
          base noAccessLaw :=
    hfair.2.2
  have hfair' : ∀ᵐ publicBase ∂baseLaw,
      condDistrib accessOutput base accessLaw publicBase =
        condDistrib noAccessOutput base noAccessLaw publicBase := by
    simpa only [haccessKernel, hnoAccessKernel] using hfairConditional
  exact (hgap.and hfair').exists.elim fun _ h => h.1 h.2

/-- A componentwise demographic-law gap refutes demographic fairness of the
single access-dispatched policy. -/
theorem lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
    {Omega Estimate : Type*} [MeasurableSpace Omega] [MeasurableSpace Estimate]
    (accessLaw noAccessLaw : Measure Omega)
    (hasAccess : Omega -> Bool) (accessOutput noAccessOutput : Omega -> Estimate)
    (haccessBranch : ∀ᵐ omega ∂accessLaw, hasAccess omega = true)
    (hnoAccessBranch : ∀ᵐ omega ∂noAccessLaw, hasAccess omega = false)
    (hgap : accessLaw.map accessOutput ≠ noAccessLaw.map noAccessOutput) :
    ¬ LG21ObservedAccessDeterministicDemographicallyFair accessLaw noAccessLaw
      (lg21ObservedAccessDeterministicTwoBranchOutput
        hasAccess accessOutput noAccessOutput) := by
  intro hfair
  have haccessOutput :
      lg21ObservedAccessDeterministicTwoBranchOutput
        hasAccess accessOutput noAccessOutput =ᵐ[
        accessLaw] accessOutput :=
    lg21ObservedAccessDeterministicTwoBranchOutput_eq_access_ae
      accessLaw hasAccess accessOutput noAccessOutput haccessBranch
  have hnoAccessOutput :
      lg21ObservedAccessDeterministicTwoBranchOutput
        hasAccess accessOutput noAccessOutput =ᵐ[
        noAccessLaw] noAccessOutput :=
    lg21ObservedAccessDeterministicTwoBranchOutput_eq_noAccess_ae
      noAccessLaw hasAccess accessOutput noAccessOutput hnoAccessBranch
  apply hgap
  calc
    accessLaw.map accessOutput = accessLaw.map
        (lg21ObservedAccessDeterministicTwoBranchOutput
          hasAccess accessOutput noAccessOutput) :=
      (Measure.map_congr haccessOutput).symm
    _ = noAccessLaw.map
        (lg21ObservedAccessDeterministicTwoBranchOutput
          hasAccess accessOutput noAccessOutput) := hfair
    _ = noAccessLaw.map noAccessOutput := Measure.map_congr hnoAccessOutput

/-! ## Source support for the two literal access-status populations -/

/-- The literal `Z = 0` normalized population is supported on the no-access
branch. This is a source-law fact, independent of policy outputs. -/
theorem lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    ∀ᵐ student ∂lg21ContinuousGaussianNoAccessPopulationLaw M,
      lg21ContinuousPopulationAccess student = false := by
  unfold lg21ContinuousGaussianNoAccessPopulationLaw lg21NormalizedRestriction
  exact Measure.ae_smul_measure
    (ae_restrict_mem
      (MeasurableSet.preimage (MeasurableSet.singleton false) measurable_fst)) _

/-- The literal `Z = 1` normalized population is supported on the access
branch. This restates the existing source support result under the common
policy-semantics name. -/
theorem lg21ContinuousGaussianAccessPopulationLaw_ae_access_true
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      lg21ContinuousPopulationAccess student = true :=
  (lg21ContinuousGaussianAccessPopulationLaw_isProbability_and_ae_access
    M haccess).2

/-! ## Mandatory-given-access source endpoint -/

/-- Proposition 4.3 for mandatory testing, stated for one total realized PBO
policy. The `Z = 1` and `Z = 0` branches are dispatched by the literal
source access indicator; the two fairness failures are therefore failures of
that one policy rather than disconnected component comparisons. -/
theorem lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff)
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21ObservedAccessActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              mandatory.action reportedPayoff noReportPayoff)
            noAccessOutput)) ∧
        (¬ LG21ObservedAccessDeterministicDemographicallyFair
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21ObservedAccessActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              mandatory.action reportedPayoff noReportPayoff)
            noAccessOutput)) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  rcases
      lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_observableOrDemographicFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance mandatory reportedPayoff noReportPayoff hreportedPBO
        noAccessOutput hnoAccessPBO with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
        hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, hgap⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_, ?_⟩
  · exact
      lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
        baseLaw (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action reportedPayoff noReportPayoff)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.1
  · exact
      lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action reportedPayoff noReportPayoff)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2

/-! ## Optional source-timed source endpoint -/

/-- Proposition 4.3 for the source-timed optional protocol, stated for one
total realized PBO policy. The access branch is the attained optional output
and the no-access branch is the actual no-access PBO output. -/
theorem lg21ContinuousGaussianPopulation_optional_sourceTimed_actualPBO_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
            noAccessOutput)) ∧
        (¬ LG21ObservedAccessDeterministicDemographicallyFair
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
            noAccessOutput)) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  rcases
      lg21ContinuousGaussianPopulation_optional_sourceTimed_actualPBO_not_observableOrDemographicFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional noAccessOutput hnoAccessPBO with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
        hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, hgap⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_, ?_⟩
  · exact
      lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
        baseLaw (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.1
  · exact
      lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2

/-! ## Report-required source endpoint -/

/-- Proposition 4.3 for report-required testing, stated for one total
realized PBO policy. The source stability condition is the literal
positive-mass deviation refinement used by the report-required raw bridge;
it is not a fairness or output-law premise. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_actualPBO_not_fair
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
        ((M.noiseVariance testFeature : ℝ).toNNReal))
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
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
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
            noAccessOutput)) ∧
        (¬ LG21ObservedAccessDeterministicDemographicallyFair
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
            noAccessOutput)) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  intro source hstable
  rcases
      lg21ContinuousGaussianPopulation_reportRequired_actualPBO_not_observableOrDemographicFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired htestLaw noAccessOutput hnoAccessPBO
        source hstable with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
        hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, hgap⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_, ?_⟩
  · exact
      lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
        baseLaw (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.1
  · exact
      lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2

/-! ## Independent three-protocol source endpoint -/

/-- The Proposition 4.3 conclusion for each observed-access protocol. Each
conjunct quantifies its own literal protocol carrier and PBO branches, so the
statement does not require an artificial simultaneous equilibrium across the
three different protocols. -/
theorem lg21ContinuousGaussianPopulation_allObservedAccessProtocols_actualPBO_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    (∀ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
        (mandatoryReportedPayoff :
          (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
        (mandatoryNoReportPayoff :
          (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          mandatoryReportedPayoff)
        (mandatoryNoAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
        (hmandatoryNoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
          M hnoAccess testFeature mandatoryNoAccessOutput),
      ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
          (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
          (baseVariance baseMeanVariance : ℝ)
          (hbaseLaw : IsProbabilityMeasure baseLaw)
          (hbaseMean : Measurable baseMean)
          (hbaseVariance : 0 < baseVariance),
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
            baseLaw ⊗ₘ gaussianLocationKernel
              baseMean hbaseMean baseVariance.toNNReal ∧
          0 ≤ baseMeanVariance ∧
          (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousGaussianAccessPopulationLaw M)
            (lg21ContinuousGaussianNoAccessPopulationLaw M)
            (lg21ObservedAccessDeterministicTwoBranchOutput
              lg21ContinuousPopulationAccess
              (lg21ObservedAccessActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
              mandatoryNoAccessOutput)) ∧
          (¬ LG21ObservedAccessDeterministicDemographicallyFair
            (lg21ContinuousGaussianAccessPopulationLaw M)
            (lg21ContinuousGaussianNoAccessPopulationLaw M)
            (lg21ObservedAccessDeterministicTwoBranchOutput
              lg21ContinuousPopulationAccess
              (lg21ObservedAccessActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
              mandatoryNoAccessOutput))) ∧
      (∀ (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
          M haccess testFeature)
          (optionalNoAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
          (hoptionalNoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
            M hnoAccess testFeature optionalNoAccessOutput),
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousGaussianNoAccessPopulationLaw M)
              (lg21ObservedAccessDeterministicTwoBranchOutput
                lg21ContinuousPopulationAccess
                (lg21OptionalSourceTimedActualOutput
                  (lg21ContinuousPopulationBase testFeature)
                  (lg21ContinuousPopulationFeature testFeature)
                  (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
                optionalNoAccessOutput)) ∧
            (¬ LG21ObservedAccessDeterministicDemographicallyFair
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousGaussianNoAccessPopulationLaw M)
              (lg21ObservedAccessDeterministicTwoBranchOutput
                lg21ContinuousPopulationAccess
                (lg21OptionalSourceTimedActualOutput
                  (lg21ContinuousPopulationBase testFeature)
                  (lg21ContinuousPopulationFeature testFeature)
                  (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
                optionalNoAccessOutput))) ∧
      (∀ (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
          (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
          (hreportRequiredTestLaw : ∀ latentSkill publicBase,
            reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
              ((M.noiseVariance testFeature : ℝ).toNNReal))
          (reportRequiredNoAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
          (hreportRequiredNoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
            M hnoAccess testFeature reportRequiredNoAccessOutput),
        ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
          LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
            (lg21ContinuousGaussianAccessPopulationLaw M)
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            (reportRequiredSource.base_measurable.prodMk
              (reportRequiredSource.score_measurable.prodMk
                reportRequiredSource.skill_measurable))
            (fun latentSkill publicBase =>
              reportRequired.takeDecision latentSkill publicBase) →
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousGaussianNoAccessPopulationLaw M)
              (lg21ObservedAccessDeterministicTwoBranchOutput
                lg21ContinuousPopulationAccess
                (lg21ReportRequiredSequentialActualOutput
                  (lg21ContinuousPopulationBase testFeature)
                  (lg21ContinuousPopulationFeature testFeature)
                  (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
                reportRequiredNoAccessOutput)) ∧
            (¬ LG21ObservedAccessDeterministicDemographicallyFair
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousGaussianNoAccessPopulationLaw M)
              (lg21ObservedAccessDeterministicTwoBranchOutput
                lg21ContinuousPopulationAccess
                (lg21ReportRequiredSequentialActualOutput
                  (lg21ContinuousPopulationBase testFeature)
                  (lg21ContinuousPopulationFeature testFeature)
                  (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
                reportRequiredNoAccessOutput))) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  constructor
  · intro mandatory mandatoryReportedPayoff mandatoryNoReportPayoff
      hmandatoryReportedPBO mandatoryNoAccessOutput hmandatoryNoAccessPBO
    exact
      lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance mandatory mandatoryReportedPayoff mandatoryNoReportPayoff
        hmandatoryReportedPBO mandatoryNoAccessOutput hmandatoryNoAccessPBO
  constructor
  · intro optional optionalNoAccessOutput hoptionalNoAccessPBO
    exact
      lg21ContinuousGaussianPopulation_optional_sourceTimed_actualPBO_not_fair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional optionalNoAccessOutput hoptionalNoAccessPBO
  · intro reportRequired hreportRequiredTestLaw reportRequiredNoAccessOutput
      hreportRequiredNoAccessPBO reportRequiredSource hreportRequiredStable
    exact
      lg21ContinuousGaussianPopulation_reportRequired_actualPBO_not_fair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired hreportRequiredTestLaw
        reportRequiredNoAccessOutput hreportRequiredNoAccessPBO
        reportRequiredSource hreportRequiredStable

/-- Proposition 4.3 with one Gaussian source witness and one literal
no-access PBO branch fixed before quantifying over requirement protocols.
Only the realized access output varies with the protocol equilibrium. -/
theorem lg21ContinuousGaussianPopulation_allObservedAccessProtocols_actualPBO_not_fair_fixedSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        baseLaw.map baseMean =
          gaussianReal M.priorMean baseMeanVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         (∀ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
             (mandatoryReportedPayoff :
               (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
             (mandatoryNoReportPayoff :
               (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
             (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
               (lg21ContinuousGaussianAccessPopulationLaw M)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousPopulationFeature testFeature)
               (lg21ContinuousPopulationSkill (Feature := Feature))
               mandatoryReportedPayoff),
           (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ObservedAccessActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
               noAccessOutput)) ∧
           (¬ LG21ObservedAccessDeterministicDemographicallyFair
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ObservedAccessActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
               noAccessOutput))) ∧
         (∀ (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
             M haccess testFeature),
           (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
               noAccessOutput)) ∧
           (¬ LG21ObservedAccessDeterministicDemographicallyFair
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
               noAccessOutput))) ∧
         (∀ (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
             (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
             (hreportRequiredTestLaw : ∀ latentSkill publicBase,
               reportRequired.testLaw latentSkill publicBase =
                 gaussianReal latentSkill
                   ((M.noiseVariance testFeature : ℝ).toNNReal))
             (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
               (lg21ContinuousGaussianAccessPopulationLaw M)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousPopulationFeature testFeature)
               (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
           LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousPopulationFeature testFeature)
             (lg21ContinuousPopulationSkill (Feature := Feature))
             (reportRequiredSource.base_measurable.prodMk
               (reportRequiredSource.score_measurable.prodMk
                 reportRequiredSource.skill_measurable))
             (fun latentSkill publicBase =>
               reportRequired.takeDecision latentSkill publicBase) →
           (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
               noAccessOutput)) ∧
           (¬ LG21ObservedAccessDeterministicDemographicallyFair
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
               noAccessOutput)))) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hbaseMeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance,
    hbaseMeanLaw, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro mandatory mandatoryReportedPayoff mandatoryNoReportPayoff
      hmandatoryReportedPBO
    have hallMandatory : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
        mandatory.action student = LG21AccessAction.takeAndReport :=
      lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
        M haccess mandatory.action mandatory.feasible
    have hmandatoryOutput :=
      lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfactorization mandatory.action
        mandatoryReportedPayoff mandatoryNoReportPayoff hallMandatory
        hmandatoryReportedPBO
    have hgap :=
      lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
        htestNoiseVariance hfactorization
        (lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
        noAccessOutput hmandatoryOutput hnoAccessPBO
    exact ⟨
      lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
        baseLaw (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.1,
      lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2⟩
  · intro optional
    have hoptionalOutput :=
      lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutput_eq_d6_ae
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional baseLaw baseMean hbaseMean baseVariance
        hbaseVariance hfactorization
    have hgap :=
      lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
        htestNoiseVariance hfactorization
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
        noAccessOutput hoptionalOutput hnoAccessPBO
    exact ⟨
      lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
        baseLaw (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.1,
      lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2⟩
  · intro reportRequired hreportRequiredTestLaw reportRequiredSource
      hreportRequiredStable
    have hreportRequiredOutput :=
      lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired hreportRequiredTestLaw baseLaw baseMean
        hbaseMean baseVariance hbaseVariance hfactorization
        reportRequiredSource hreportRequiredStable
    have hgap :=
      lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
        htestNoiseVariance hfactorization
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
        noAccessOutput hreportRequiredOutput hnoAccessPBO
    exact ⟨
      lg21ObservedAccessDeterministicTwoBranchOutput_not_observableFairAE_of_component_gap
        baseLaw (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.1,
      lg21ObservedAccessDeterministicTwoBranchOutput_not_demographicallyFair_of_component_gap
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        lg21ContinuousPopulationAccess
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2⟩

end

end LG21TestOptionalPolicies
