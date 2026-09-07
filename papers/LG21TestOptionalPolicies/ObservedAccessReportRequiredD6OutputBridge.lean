import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge

/-!
# Report-required observed-access output transport for LG21 Section 4

This module exposes the source-literal, almost-everywhere realized-output
identity for the report-required protocol.  The action conclusion comes from
the literal positive-mass stability proof; the PBO is used only on its now
attained reporter event.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- Under the literal report-required source carrier, positive-mass stability
forces all taking, so the attained reporter PBO identifies the actual school
output with the Definition 6 Gaussian estimator almost everywhere.  No value
is assigned to an unattained zero-mass branch. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (_hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∀ (source : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill E),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        lg21ContinuousPopulationSkill
        (source.base_measurable.prodMk
          (source.score_measurable.prodMk source.skill_measurable))
        (fun latentSkill publicBase => E.takeDecision latentSkill publicBase) →
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
      lg21ContinuousPopulationSkill E =ᵐ[accessLaw]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  intro source hstable
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hnoTakeZero : accessLaw
      {student | E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false} = 0 := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_literalSource
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E htestLaw source hstable)
  have htakeBad :
      {student | ¬ E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true} =
        {student | E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false} := by
    ext student
    cases htake : E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) <;>
      simp [htake]
  have hallTake : ∀ᵐ student ∂accessLaw,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true := by
    rw [ae_iff, htakeBad]
    exact hnoTakeZero
  have hallAction : ∀ᵐ student ∂accessLaw,
      lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        lg21ContinuousPopulationSkill E student =
          LG21AccessAction.takeAndReport := by
    exact lg21ReportRequiredSequentialAccessAction_ae_takeAndReport_of_all_take
      accessLaw (lg21ContinuousPopulationBase testFeature)
      lg21ContinuousPopulationSkill E hallTake
  have hreportedPBO : LG21ObservedAccessAllReportPBO accessLaw
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill E.reportedPayoff := by
    exact source.reported_pbo_of_all_take hallTake
  simpa [accessLaw, lg21ReportRequiredSequentialActualOutput] using
    (lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization
      (lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        lg21ContinuousPopulationSkill E)
      E.reportedPayoff E.noReportPayoff hallAction hreportedPBO)

end

end LG21TestOptionalPolicies
