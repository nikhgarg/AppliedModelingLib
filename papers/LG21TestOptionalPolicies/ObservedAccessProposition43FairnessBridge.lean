import LG21TestOptionalPolicies.ObservedAccessConditionalOutputKernel
import LG21TestOptionalPolicies.ObservedAccessNoAccessPBOBridge
import LG21TestOptionalPolicies.ObservedAccessOptionalSection4Bridge

/-!
# Literal Proposition 4.3 bridge for observed access

This module compares the actual access and no-access PBO outputs in the same
literal Gaussian population.  It does not take output laws, kernel gaps, or
fairness failures as hypotheses.  The access PBO is first transported to the
Definition 6 estimator, and the no-access PBO is first derived as the
base-only conditional mean.  The final Gaussian variance calculation then
proves the demographic difference.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- If literal access and no-access outputs satisfy their respective PBO
semantics, the PBO policy is neither observably fair (outside null base
fibres) nor demographically fair.  The access premise is an a.e. identity
proved from a concrete action/PBO route; the no-access premise is the
source-level PBO definition, not a supplied base-mean output law. -/
theorem lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance baseMeanVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hbaseMeanVariance : 0 ≤ baseMeanVariance)
    (hbaseMeanLaw : baseLaw.map baseMean =
      gaussianReal M.priorMean baseMeanVariance.toNNReal)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (accessOutput noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (haccessOutput : accessOutput =ᵐ[
      lg21ContinuousGaussianAccessPopulationLaw M]
      fun student =>
        lg21D6GaussianPBOEstimate
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
          (lg21ContinuousPopulationBase testFeature student,
            lg21ContinuousPopulationFeature testFeature student))
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
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
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    (∀ᵐ publicBase ∂baseLaw,
      condDistrib accessOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
        condDistrib noAccessOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
      ((lg21ContinuousGaussianAccessPopulationLaw M).map accessOutput ≠
        (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput) := by
  intro S
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student,
      lg21ContinuousPopulationFeature testFeature student)
  letI : IsProbabilityMeasure accessLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure noAccessLaw :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure noAccessLaw := ⟨by simp⟩
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact (measurable_fst.comp measurable_snd).add
      ((measurable_pi_apply testFeature).comp
        (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hbaseAccess : accessLaw.map base = baseLaw := by
    simpa [accessLaw, base] using
      (lg21ContinuousGaussianAccessPopulation_baseLaw_eq_of_factorization
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization)
  have hbaseNoAccess : noAccessLaw.map base = baseLaw := by
    calc
      noAccessLaw.map base = accessLaw.map base := by
        simpa [accessLaw, noAccessLaw, base] using
          (lg21ContinuousGaussianAccess_noAccess_baseLaw_eq
            M haccess hnoAccess testFeature).symm
      _ = baseLaw := hbaseAccess
  have haccessConditional :
      condDistrib accessOutput base accessLaw =ᵐ[accessLaw.map base]
        lg21D6ActualAccessEstimateKernel S := by
    simpa [accessLaw, base] using
      (lg21ContinuousGaussianAccessPopulation_actualOutput_conditionalKernel_eq_d6
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization accessOutput
        haccessOutput)
  have hnoAccessConditional :
      condDistrib noAccessOutput base noAccessLaw =ᵐ[noAccessLaw.map base]
        Kernel.deterministic baseMean hbaseMean := by
    simpa [noAccessLaw, base] using
      (lg21ContinuousGaussianNoAccessPopulation_pbo_conditionalKernel_eq_baseMean
        M hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        hfullBaseFactorization noAccessOutput hnoAccessPBO)
  have haccessConditional' :
      condDistrib accessOutput base accessLaw =ᵐ[baseLaw]
        lg21D6ActualAccessEstimateKernel S := by
    rw [← hbaseAccess]
    exact haccessConditional
  have hnoAccessConditional' :
      condDistrib noAccessOutput base noAccessLaw =ᵐ[baseLaw]
        Kernel.deterministic baseMean hbaseMean := by
    rw [← hbaseNoAccess]
    exact hnoAccessConditional
  refine ⟨?_, ?_⟩
  · filter_upwards [haccessConditional', hnoAccessConditional'] with
      publicBase haccessKernel hnoAccessKernel
    intro heq
    apply lg21D6ActualAccessEstimateKernel_ne_noAccessPBOEstimateKernel S publicBase
    calc
      lg21D6ActualAccessEstimateKernel S publicBase =
          condDistrib accessOutput base accessLaw publicBase := haccessKernel.symm
      _ = condDistrib noAccessOutput base noAccessLaw publicBase := heq
      _ = Kernel.deterministic baseMean hbaseMean publicBase := hnoAccessKernel
  · have hnoAccessOutput : noAccessOutput =ᵐ[noAccessLaw]
        fun student => baseMean (base student) := by
      simpa [noAccessLaw, base] using
        (lg21ContinuousGaussianNoAccessPopulation_pbo_eq_baseMean_ae_of_literalFactorization
          M hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
          hfullBaseFactorization noAccessOutput hnoAccessPBO)
    have haccessOutput' : accessOutput =ᵐ[accessLaw]
        fun student => lg21D6GaussianPBOEstimate S (observation student) := by
      simpa [accessLaw, base, observation] using haccessOutput
    have haccessOutputLaw : accessLaw.map accessOutput =
        lg21D6ActualAccessEstimateLaw S := by
      calc
        accessLaw.map accessOutput = accessLaw.map
            (fun student => lg21D6GaussianPBOEstimate S (observation student)) := by
              exact Measure.map_congr haccessOutput'
        _ = (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
              rw [Measure.map_map (lg21D6GaussianPBOEstimate_measurable S) hobservation]
              rfl
        _ = (lg21D6ActualAccessTestLaw S).map
            (lg21D6GaussianPBOEstimate S) := by
              rw [lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
                M haccess testFeature baseLaw baseMean hbaseMean baseVariance
                hbaseVariance htestNoiseVariance hfullBaseFactorization]
        _ = lg21D6ActualAccessEstimateLaw S := rfl
    intro heq
    apply (lg21D6ActualAccessEstimateLaw_ne_baseMeanLaw
      S M.priorMean baseMeanVariance hbaseMeanVariance hbaseMeanLaw)
    calc
      lg21D6ActualAccessEstimateLaw S = accessLaw.map accessOutput :=
        haccessOutputLaw.symm
      _ = noAccessLaw.map noAccessOutput := by simpa [accessLaw, noAccessLaw] using heq
      _ = noAccessLaw.map (fun student => baseMean (base student)) := by
        exact Measure.map_congr hnoAccessOutput
      _ = (noAccessLaw.map base).map baseMean := by
        rw [Measure.map_map hbaseMean hbase]
        rfl
      _ = baseLaw.map baseMean := by rw [hbaseNoAccess]

/-- Literal optional-protocol source endpoint for Proposition 4.3.  The
access output is obtained from the actual attained reporter PBO after Lemma
4.1's all-report conclusion; the no-access output is an independently
specified actual no-access PBO. -/
theorem lg21ContinuousGaussianPopulation_optional_actualPBO_not_observableOrDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
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
        ((∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21OptionalSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) E.data)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21OptionalSequentialActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) ≠
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
    lg21ContinuousGaussianAccessPopulation_optional_actualOutput_eq_d6_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization
  simpa using
    (lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21OptionalSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data)
      noAccessOutput haccessOutput hnoAccessPBO)

end

end LG21TestOptionalPolicies
