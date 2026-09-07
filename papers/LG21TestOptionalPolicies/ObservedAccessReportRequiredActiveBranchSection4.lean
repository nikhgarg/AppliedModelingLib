import LG21TestOptionalPolicies.ObservedAccessReportRequiredPositiveMassRefinedOutputBridge
import LG21TestOptionalPolicies.ObservedAccessProposition43FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessOptionalSection4Bridge
import LG21TestOptionalPolicies.ObservedAccessProposition43PolicyEndpoints

/-!
# Report-required Section 4 bridges under active-branch selection

This module exposes the report-required Section 4 endpoints only under the
declared fibrewise active-branch/unravelling refinement.  That refinement is
separate from the paper's literal static conditional-mean requirements: it
selects an attained positive report branch, while the refined source record
supplies the PBO semantics on that branch.  In particular, none of the
results below infer a value for a null no-take branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the declared fibrewise active-branch selection, the selected
report-required profile has Definition 6's actual access-estimate law.  The
selection argument is tied to the refined source record, so raw action data
cannot be detached from its positive-branch PBO semantics. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutputLaw_eq_d6ActualAccessEstimateLaw_of_fibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hsource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature))
    (hselection : LG21ReportRequiredFibrewiseActiveBranchSelection
      M haccess testFeature E hsource)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
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
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E) =
      lg21D6ActualAccessEstimateLaw S := by
  intro S
  have houtput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutputLaw_eq_d6_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hsource hselection baseLaw baseMean hbaseMean
      baseVariance hbaseVariance hfullBaseFactorization
  have htestLaw :=
    lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  change accessLaw.map
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E) =
      lg21D6ActualAccessEstimateLaw S
  calc
    accessLaw.map
        (lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) E) =
        (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
          simpa [accessLaw, observation] using houtput
    _ = (lg21D6ActualAccessTestLaw S).map (lg21D6GaussianPBOEstimate S) := by
      rw [show accessLaw.map observation = lg21D6ActualAccessTestLaw S by
        simpa [accessLaw, observation] using htestLaw]
    _ = lg21D6ActualAccessEstimateLaw S := rfl

/-- Proposition 4.3 for the report-required protocol under the declared
active-branch/unravelling refinement.  The access side uses only the selected
positive report branch; the no-access side remains the separate literal PBO
specified by the proposition. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_activeBranchSelection_actualPBO_not_observableOrDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hsource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature))
    (hselection : LG21ReportRequiredFibrewiseActiveBranchSelection
      M haccess testFeature E hsource)
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
        ((∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) E)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ReportRequiredSequentialActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) E) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput)) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hbaseMeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_⟩
  have haccessOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hsource hselection baseLaw baseMean hbaseMean
      baseVariance hbaseVariance hfactorization
  simpa using
    (lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E)
      noAccessOutput haccessOutput hnoAccessPBO)

/-- Proposition 4.3's source-semantic endpoint for the selected
report-required active branch.  It packages the attained report PBO and the
literal no-access PBO as one access-dispatched deterministic policy before
refuting the two fairness definitions. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_activeBranchSelection_actualPBO_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hsource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature))
    (hselection : LG21ReportRequiredFibrewiseActiveBranchSelection
      M haccess testFeature E hsource)
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
            (lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) E)
            noAccessOutput)) ∧
        (¬ LG21ObservedAccessDeterministicDemographicallyFair
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) E)
            noAccessOutput)) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  rcases
      lg21ContinuousGaussianPopulation_reportRequired_activeBranchSelection_actualPBO_not_observableOrDemographicFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E hsource hselection noAccessOutput hnoAccessPBO with
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
          (lg21ContinuousPopulationSkill (Feature := Feature)) E)
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
          (lg21ContinuousPopulationSkill (Feature := Feature)) E)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2

/-- Theorem 4.4 for the report-required protocol under the declared
active-branch/unravelling refinement.  This derives the fairness endpoints
from the selected actual output's a.e. Definition 6 identity; it does not
assign a PBO to an empty no-take branch. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_activeBranchSelection_resampling_observableAndDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hsource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature))
    (hselection : LG21ReportRequiredFibrewiseActiveBranchSelection
      M haccess testFeature E hsource) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
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
       let actualOutput := lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) E
       (condDistrib actualOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map actualOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S))) := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  have hactualOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hsource hselection baseLaw baseMean hbaseMean
      baseVariance hbaseVariance hfactorization
  simpa using
    (lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E)
      hactualOutput)

end

end LG21TestOptionalPolicies
