import LG21TestOptionalPolicies.ObservedAccessOptionalActiveBranchD6OutputBridge
import LG21TestOptionalPolicies.ObservedAccessOptionalSection4Bridge
import LG21TestOptionalPolicies.ObservedAccessProposition43FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessConditionalOutputKernel
import LG21TestOptionalPolicies.ObservedAccessProposition43PolicyEndpoints

/-!
# Optional Section 4 bridges under active-branch selection

This module exposes the optional-protocol Section 4 endpoints after the
explicit fibrewise active-branch/unravelling selection has been declared.
The selection is a visible model refinement: it is not derived from the
paper's literal static RCD definition.  The underlying Gaussian calculations,
the Definition 6 estimator, and the no-access PBO comparison remain the
literal source-model arguments imported below.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the declared fibrewise active-branch selection, the selected
optional profile's actual PBO output is neither observably fair (outside null
base fibres) nor demographically fair against a literal no-access PBO.  The
selection is an explicit refinement, not a conclusion of Definition 1. -/
theorem lg21ContinuousGaussianPopulation_optional_activeBranchSelection_actualPBO_not_observableOrDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected)
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
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21OptionalSourceTimedActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions) ≠
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
    lg21_optional_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance baseLaw baseMean hbaseMean baseVariance
        hbaseVariance hfactorization selected hselection
  simpa using
    (lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
      noAccessOutput haccessOutput hnoAccessPBO)

/-- Proposition 4.3's source-semantic endpoint for the selected optional
active branch.  It dispatches the attained access PBO output and the literal
no-access PBO output into one deterministic policy before refuting each
fairness definition. -/
theorem lg21ContinuousGaussianPopulation_optional_activeBranchSelection_actualPBO_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected)
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
              (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
            noAccessOutput)) ∧
        (¬ LG21ObservedAccessDeterministicDemographicallyFair
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousGaussianNoAccessPopulationLaw M)
          (lg21ObservedAccessDeterministicTwoBranchOutput
            lg21ContinuousPopulationAccess
            (lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
            noAccessOutput)) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  rcases
      lg21ContinuousGaussianPopulation_optional_activeBranchSelection_actualPBO_not_observableOrDemographicFair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance selected hselection noAccessOutput hnoAccessPBO with
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
          (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
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
          (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
        noAccessOutput
        (lg21ContinuousGaussianAccessPopulationLaw_ae_access_true M haccess)
        (lg21ContinuousGaussianNoAccessPopulationLaw_ae_access_false M hnoAccess)
        hgap.2

/-- Under the declared fibrewise active-branch selection, the selected
optional profile's actual Definition 6 resampling output satisfies the two
fairness conclusions of Theorem 4.4.  The convention is stated as a premise
and is not claimed to follow from a static RCD. -/
theorem lg21ContinuousGaussianPopulation_optional_activeBranchSelection_resampling_observableAndDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected) :
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
       let actualOutput := lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions
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
    lg21_optional_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance baseLaw baseMean hbaseMean baseVariance
        hbaseVariance hfactorization selected hselection
  simpa using
    (lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions)
      hactualOutput)

end

end LG21TestOptionalPolicies
