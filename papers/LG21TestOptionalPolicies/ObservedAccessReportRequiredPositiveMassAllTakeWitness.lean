import LG21TestOptionalPolicies.ReportRequiredPositiveMassRefinedEquilibrium
import LG21TestOptionalPolicies.ObservedAccessOptionalPositiveMassAllReportWitness

/-!
# All-take witness for the report-required positive-mass refinement

This module constructs the source-timed all-take profile for the
report-required-after-taking protocol.  The reported branch has the literal
full-profile Gaussian conditional mean.  The no-take branch is unattained,
so the positive-mass refinement deliberately asks for no numerical PBO there.

The result is a nonvacuous witness for the stated positive-mass carrier, not
by itself a proof that every static-RCD completion selects that carrier.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The source-timed all-take report-required action data.  It shares the
literal D6 reported estimator with the optional all-report witness. -/
def lg21ObservedAccessReportRequiredAllTakeData
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) :
    LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ where
  testLaw := fun latentSkill _ => gaussianReal latentSkill S.testNoiseVariance
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  takeDecision := fun _ _ => true
  reportedPayoff := fun publicBase score =>
    lg21D6GaussianPBOEstimate S (publicBase, score)
  noReportPayoff := fun _ => 0
  reportedPayoff_integrable := by
    intro latentSkill publicBase
    exact (lg21ObservedAccessOptionalAllTakeAllReportActions S).continuationPayoff_integrable
      latentSkill publicBase
  estimationConsistent := True

@[simp] theorem lg21ObservedAccessReportRequiredAllTakeData_takeDecision
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) (latentSkill : ℝ) (publicBase : Base) :
    (lg21ObservedAccessReportRequiredAllTakeData S).takeDecision
      latentSkill publicBase = true := rfl

/-- With everyone currently taking, a local entry requiring a positive region
with zero current takers has contradictory mass premises. -/
theorem lg21_reportRequired_allTake_positive_mass_recalibrated_stable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega)))) :
    LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic (fun _ _ => true) := by
  intro region candidate hentry
  rcases hentry with ⟨hregion, hregionPositive, hzeroTakers, _⟩
  have htakeEvent :
      {omega | (fun _ _ => true : ℝ -> Base -> Bool) (skill omega) (base omega) = true} =
        Set.univ := by
    ext omega
    simp
  have hregionZero : sourceLaw (base ⁻¹' region) = 0 := by
    simpa [htakeEvent] using hzeroTakers
  exact (ne_of_gt hregionPositive) hregionZero

/-- The all-take source profile is a nonvacuous witness of the
report-required positive-mass refinement.  Its reported PBO is derived from
the full-profile Gaussian source law; both no-take obligations are eliminated
only after the literal no-take event is proved empty. -/
def lg21ReportRequiredPositiveMassRefinedSourceEquilibrium_allTake_of_fullBaseGaussianFactorization
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
          baseMean hbaseMean baseVariance.toNNReal) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∃ E : LG21ReportRequiredSequentialEquilibriumData ℝ
        (LG21NonTestFeature Feature testFeature -> ℝ) ℝ,
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature) ∧
      (∀ latentSkill publicBase,
        E.takeDecision latentSkill publicBase = true) := by
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
  let E := lg21ObservedAccessReportRequiredAllTakeData S
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, score student)
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable score := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hpublic : Measurable (fun student =>
      (base student, (score student, skill student))) :=
    hbase.prodMk (hscore.prodMk hskill)
  have hobservation : Measurable observation := hbase.prodMk hscore
  have htakeEvent :
      {student | E.takeDecision (skill student) (base student) = true} = Set.univ := by
    ext student
    simp [E, lg21ObservedAccessReportRequiredAllTakeData]
  have hnoTakeEvent :
      {student | E.takeDecision (skill student) (base student) = false} = ∅ := by
    ext student
    simp [E, lg21ObservedAccessReportRequiredAllTakeData]
  have htakeLaw : lg21NormalizedRestriction law
      {student | E.takeDecision (skill student) (base student) = true} = law := by
    rw [htakeEvent]
    simp [lg21NormalizedRestriction]
  have hskillIntegrable : Integrable skill law := by
    simpa [law, skill] using
      (lg21ContinuousGaussianAccessPopulation_skill_integrable M haccess)
  have hcondExp :
      law[skill | MeasurableSpace.comap observation inferInstance] =ᵐ[law]
        fun student => ∫ latentSkill, latentSkill ∂condDistrib
          skill observation law (observation student) := by
    exact condExp_ae_eq_integral_condDistrib' hobservation hskillIntegrable
  have hd6Observation :=
    lg21ContinuousGaussianAccessPopulation_d6Estimate_eq_condDistribMean_ae
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  have hd6Pullback : ∀ᵐ student ∂law,
      lg21D6GaussianPBOEstimate S (observation student) =
        ∫ latentSkill, latentSkill ∂condDistrib
          skill observation law (observation student) := by
    exact ae_of_ae_map hobservation.aemeasurable hd6Observation
  have hreportedMeasurable : Measurable (fun publicScore :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      E.reportedPayoff publicScore.1 publicScore.2) := by
    simpa [E, lg21ObservedAccessReportRequiredAllTakeData] using
      (lg21D6GaussianPBOEstimate_measurable S)
  refine ⟨E, ?_, ?_⟩
  · refine
      { base_measurable := hbase
        score_measurable := hscore
        skill_measurable := hskill
        action_measurable := by
          simpa [E, lg21ObservedAccessReportRequiredAllTakeData] using
            (measurable_const : Measurable (fun _ :
              (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => true))
        reportedPayoff_measurable := hreportedMeasurable
        noReportPayoff_measurable := by
          simpa [E, lg21ObservedAccessReportRequiredAllTakeData] using
            (measurable_const : Measurable (fun _ :
              LG21NonTestFeature Feature testFeature -> ℝ => (0 : ℝ)))
        test_law_gaussian := by
          intro publicBase latentSkill
          rfl
        reported_integrable := by
          intro hpositive
          rw [htakeLaw]
          exact hskillIntegrable
        reported_pbo := by
          intro hpositive
          change (fun student => E.reportedPayoff (base student) (score student)) =ᵐ[
              lg21NormalizedRestriction law
                {student | E.takeDecision (skill student) (base student) = true}]
            (lg21NormalizedRestriction law
              {student | E.takeDecision (skill student) (base student) = true})[
                skill | MeasurableSpace.comap observation inferInstance]
          rw [htakeLaw]
          filter_upwards [hd6Pullback, hcondExp] with student hd6 hmean
          change lg21D6GaussianPBOEstimate S (observation student) =
            law[skill | MeasurableSpace.comap observation inferInstance] student
          rw [hd6, ← hmean]
        noTake_integrable := by
          intro hpositive
          have hpositive' : 0 < law
              {student | E.takeDecision (skill student) (base student) = false} := by
            simpa [law, base, skill] using hpositive
          rw [hnoTakeEvent] at hpositive'
          exfalso
          simpa using hpositive'
        noTake_pbo := by
          intro hpositive
          have hpositive' : 0 < law
              {student | E.takeDecision (skill student) (base student) = false} := by
            simpa [law, base, skill] using hpositive
          rw [hnoTakeEvent] at hpositive'
          exfalso
          simpa using hpositive'
        positive_mass_recalibrated_stable := by
          intro region candidate _hfixedLaw hentry
          exact (lg21_reportRequired_allTake_positive_mass_recalibrated_stable
            law base score skill hpublic) region candidate hentry }
  · intro latentSkill publicBase
    rfl

/-- The finite-coordinate Gaussian source supplies a report-required all-take
witness under the positive-mass refinement. -/
theorem lg21ContinuousGaussianAccessPopulation_exists_reportRequiredPositiveMassRefined_allTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∃ E : LG21ReportRequiredSequentialEquilibriumData ℝ
        (LG21NonTestFeature Feature testFeature -> ℝ) ℝ,
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature) ∧
      (∀ latentSkill publicBase,
        E.takeDecision latentSkill publicBase = true) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        M testFeature hpriorVariance hnonTestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hfullBaseFactorization⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  exact
    lg21ReportRequiredPositiveMassRefinedSourceEquilibrium_allTake_of_fullBaseGaussianFactorization
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization

end

end LG21TestOptionalPolicies
