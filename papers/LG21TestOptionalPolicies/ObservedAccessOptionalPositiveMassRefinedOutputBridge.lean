import LG21TestOptionalPolicies.ObservedAccessOptionalPositiveMassRefinedEquilibrium
import LG21TestOptionalPolicies.ObservedAccessOptionalD6OutputBridge

/-!
# On-path output bridge for the optional positive-mass refinement

This module is deliberately conditional on an independently established
all-take/all-report action conclusion.  The current positive-mass entry
predicates do not themselves certify every deviation direction, so this file
does not assert equilibrium existence.  It only transports an attained PBO to
the full access law after the action conclusion is supplied.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- An actual positive-branch PBO becomes the all-report PBO after an
independent all-take/all-report conclusion makes the report event full mass. -/
theorem LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium.actual_report_pbo_of_all_take_and_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.actions.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.actions.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true) :
    LG21OptionalSourceTimedAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let reportEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21OptionalSourceReportEvent
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      E.actions.takeDecision E.actions.reportDecision
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have hreporterAE : ∀ᵐ student ∂law, student ∈ reportEvent := by
    simpa [law, reportEvent, lg21OptionalSourceReportEvent] using hall
  have hrestrict : law.restrict reportEvent = law :=
    Measure.restrict_eq_self_of_ae_mem hreporterAE
  have hreporterMass : law reportEvent = 1 := by
    calc
      law reportEvent = law.restrict reportEvent Set.univ := by
        rw [Measure.restrict_apply_univ]
      _ = law Set.univ := by rw [hrestrict]
      _ = 1 := IsProbabilityMeasure.measure_univ
  have hreporterPositive : 0 < law reportEvent := by
    rw [hreporterMass]
    exact zero_lt_one
  have hreporterLaw : lg21NormalizedRestriction law reportEvent = law := by
    rw [lg21NormalizedRestriction, hreporterMass, hrestrict]
    simp
  have hpbo := E.actual_report_pbo
    (by simpa [law, reportEvent] using hreporterPositive)
  rw [hreporterLaw] at hpbo
  simpa [LG21OptionalSourceTimedAllReportPBO, law, reportEvent] using hpbo

/-- The refined optional carrier's literal output equals the Definition 6
access-side estimator once all taking/reporting has been proved elsewhere. -/
theorem lg21_optional_positiveMassRefined_actualOutput_eq_d6_ae_of_all_take_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.actions.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.actions.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true) :
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
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions =ᵐ[law]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  have hreportedPBO :=
    E.actual_report_pbo_of_all_take_and_report M haccess testFeature hall
  exact lg21_optional_sourceTimed_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
    M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization E.actions hall hreportedPBO

end

end LG21TestOptionalPolicies
