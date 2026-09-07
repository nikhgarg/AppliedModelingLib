import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchSelection
import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge

/-!
# On-path report-required output bridge for the positive-mass refinement

This module uses only the positive-branch report-required equilibrium carrier.
After fibrewise active-branch selection has made taking almost everywhere, the
attained reported PBO can be promoted to the full access law.  No value is
assigned to the null no-take branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The refined carrier's actual reported-branch PBO becomes the full
all-report PBO once taking holds almost everywhere. -/
theorem LG21ReportRequiredPositiveMassRefinedSourceEquilibrium.actual_report_pbo_of_all_take
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    {testNoiseVariance : NNReal}
    (S : LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      rawLaw base score skill E testNoiseVariance)
    (hall : ∀ᵐ omega ∂rawLaw,
      E.takeDecision (skill omega) (base omega) = true) :
    LG21ObservedAccessAllReportPBO rawLaw base score skill E.reportedPayoff := by
  let reporterEvent : Set Omega :=
    {omega | E.takeDecision (skill omega) (base omega) = true}
  have hreporterAE : ∀ᵐ omega ∂rawLaw, omega ∈ reporterEvent := by
    simpa [reporterEvent] using hall
  have hrestrict : rawLaw.restrict reporterEvent = rawLaw :=
    Measure.restrict_eq_self_of_ae_mem hreporterAE
  have hreporterMass : rawLaw reporterEvent = 1 := by
    calc
      rawLaw reporterEvent = rawLaw.restrict reporterEvent Set.univ := by
        rw [Measure.restrict_apply_univ]
      _ = rawLaw Set.univ := by rw [hrestrict]
      _ = 1 := IsProbabilityMeasure.measure_univ
  have hreporterPositive : 0 < rawLaw reporterEvent := by
    rw [hreporterMass]
    exact zero_lt_one
  have hreporterLaw : lg21NormalizedRestriction rawLaw reporterEvent = rawLaw := by
    rw [lg21NormalizedRestriction, hreporterMass, hrestrict]
    simp
  have hpbo := S.reported_pbo_if_positive
    (by simpa [reporterEvent] using hreporterPositive)
  change
    (fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
      lg21NormalizedRestriction rawLaw reporterEvent]
      (lg21NormalizedRestriction rawLaw reporterEvent)[skill |
        MeasurableSpace.comap (fun omega => (base omega, score omega))
          inferInstance] at hpbo
  rw [hreporterLaw] at hpbo
  simpa [LG21ObservedAccessAllReportPBO,
    LG21FullPublicReportRequiredReportedPBO] using hpbo

/-- With the explicit fibrewise active-branch selection, a refined
report-required equilibrium has the Definition 6 access-side output almost
everywhere.  This uses the actual positive report branch only. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
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
    let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    lg21ReportRequiredSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E =ᵐ[accessLaw]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  intro S accessLaw observation
  letI : IsProbabilityMeasure accessLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hallTake : ∀ᵐ student ∂accessLaw,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_fibrewiseActiveBranchSelection
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E hsource hselection)
  have hallAction : ∀ᵐ student ∂accessLaw,
      lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E student =
          LG21AccessAction.takeAndReport := by
    exact lg21ReportRequiredSequentialAccessAction_ae_takeAndReport_of_all_take
      accessLaw (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E hallTake
  have hreportedPBO : LG21ObservedAccessAllReportPBO accessLaw
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.reportedPayoff := by
    exact hsource.actual_report_pbo_of_all_take hallTake
  simpa [accessLaw, observation, lg21ReportRequiredSequentialActualOutput] using
    (lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization
      (lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E)
      E.reportedPayoff E.noReportPayoff hallAction hreportedPBO)

/-- The mapped actual-output law is the Definition 6 mapped estimator law
under the same positive-branch selection. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutputLaw_eq_d6_of_fibrewiseActiveBranchSelection
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
    let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    accessLaw.map (lg21ReportRequiredSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E) =
      (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
  intro S accessLaw observation
  letI : IsProbabilityMeasure accessLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hallTake : ∀ᵐ student ∂accessLaw,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_fibrewiseActiveBranchSelection
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E hsource hselection)
  have hallAction : ∀ᵐ student ∂accessLaw,
      lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E student =
          LG21AccessAction.takeAndReport := by
    exact lg21ReportRequiredSequentialAccessAction_ae_takeAndReport_of_all_take
      accessLaw (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E hallTake
  have hreportedPBO : LG21ObservedAccessAllReportPBO accessLaw
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.reportedPayoff := by
    exact hsource.actual_report_pbo_of_all_take hallTake
  simpa [accessLaw, observation, lg21ReportRequiredSequentialActualOutput] using
    (lg21ContinuousGaussianAccessPopulation_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization
      (lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E)
      E.reportedPayoff E.noReportPayoff hallAction hreportedPBO)

end

end LG21TestOptionalPolicies
