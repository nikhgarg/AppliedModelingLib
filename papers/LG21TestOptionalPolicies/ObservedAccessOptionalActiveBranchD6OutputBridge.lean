import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchSelection
import LG21TestOptionalPolicies.ObservedAccessOptionalPositiveMassRefinedOutputBridge

/-!
# Optional active-branch selection to Definition 6 output support

This support module composes two explicit ingredients:

* a positive-mass-refined optional action/PBO record; and
* the separately stated fibrewise active-branch selection convention.

It proves only the resulting conditional output transports.  It makes no
claim that the selection convention follows from the paper's literal static
RCD definition or that it is itself a source theorem.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- Under an explicit active-branch selection, the selected optional profile's
literal source-timed output is the Definition 6 Gaussian estimator almost
everywhere on the continuous access population. -/
theorem lg21_optional_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected) :
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
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions =ᵐ[law]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_allTakeAllReport_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance selected hselection
  exact
    lg21_optional_positiveMassRefined_actualOutput_eq_d6_ae_of_all_take_report
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization selected hall

/-- The a.e. output transport above induces the corresponding literal output
law.  The right side is the Definition 6 estimator pushed forward from the
actual full `(base, score)` observation law. -/
theorem lg21_optional_positiveMassRefined_actualOutputLaw_eq_d6_of_fibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected) :
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
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    law.map (lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions) =
      (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_allTakeAllReport_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance selected hselection
  have hreportedPBO :=
    selected.actual_report_pbo_of_all_take_and_report M haccess testFeature hall
  exact
    lg21_optional_sourceTimed_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization selected.actions
        hall hreportedPBO

/-- Section 4's packaged access-side Definition 6 output law for the selected
profile.  This is just the preceding pushforward identity combined with the
literal full-profile source law for `(base, score)`. -/
theorem lg21_optional_positiveMassRefined_actualOutputLaw_eq_d6ActualAccessEstimateLaw_of_fibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected) :
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
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    law.map (lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions) =
      lg21D6ActualAccessEstimateLaw S := by
  intro S law observation
  have houtput :=
    lg21_optional_positiveMassRefined_actualOutputLaw_eq_d6_of_fibrewiseActiveBranchSelection
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hfullBaseFactorization selected hselection
  have htestLaw :=
    lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization
  calc
    law.map (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) selected.actions) =
        (law.map observation).map (lg21D6GaussianPBOEstimate S) := houtput
    _ = (lg21D6ActualAccessTestLaw S).map (lg21D6GaussianPBOEstimate S) := by
      rw [htestLaw]
    _ = lg21D6ActualAccessEstimateLaw S := rfl

end

end LG21TestOptionalPolicies
