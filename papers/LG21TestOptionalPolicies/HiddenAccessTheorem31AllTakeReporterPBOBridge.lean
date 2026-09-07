import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterFibreBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeTransport

/-!
# All-taking reporter PBO bridge for LG21 Theorem 3.1

Once literal access/no-take mass has been eliminated, the selected taker law
is the actual access law.  This module transports the literal on-path reporter
PBO to the unselected Gaussian posterior only on the attained reporter
base-score law.  It does not assign a value to an unreported action history.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- After literal all taking, the on-path reporter payoff is the conditional
mean under the raw Gaussian access population, almost everywhere on the
actual reporter `(base, score)` law. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportedPayoff_eq_rawGaussianPosterior_ae_of_allTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ)) :
    let posteriorKernel : Kernel
        ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ℝ :=
      gaussianSignalPosteriorBaseKernel baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ)
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ)
    let reporterLaw := lg21NormalizedRestriction
      (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    (fun publicScore => E.reportedPayoff publicScore.1 publicScore.2) =ᵐ[
      reporterLaw.map baseScore]
      fun publicScore => ∫ latentSkill, latentSkill ∂posteriorKernel publicScore := by
  intro posteriorKernel reporterLaw baseScore
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let sourceTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | E.takeDecision (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = true}
  let reportSet : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    lg21HiddenAccessReportSet testFeature E.reportDecision
  let takerLaw := lg21NormalizedRestriction accessLaw sourceTakeEvent
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let rawObservation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
    fun student => (base student, (score student, skill student))
  let observationSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    fun student => (baseScore student, skill student)
  let association : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ≃ᵐ
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov baseMean hbaseMean priorVariance
      (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.access_positive)
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hbase : Measurable base :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable score :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hskill : Measurable skill := measurable_fst.comp measurable_snd
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hrawObservation : Measurable rawObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hobservationSkill : Measurable observationSkill := hbaseScore.prodMk hskill
  have hallTake : ∀ᵐ student ∂accessLaw,
      E.takeDecision (skill student) (base student) = true := by
    simpa [accessLaw, skill, base] using
      E.access_take_ae_of_activeNoTake_measure_zero hactiveNoTakeZero
  have hsourceTakeEvent : sourceTakeEvent =ᵐ[accessLaw] Set.univ := by
    filter_upwards [hallTake] with student htake
    apply propext
    change E.takeDecision (skill student) (base student) = true ↔ True
    simpa using htake
  have htakerEqAccess : takerLaw = accessLaw := by
    unfold takerLaw lg21NormalizedRestriction
    rw [measure_congr hsourceTakeEvent,
      Measure.restrict_congr_set hsourceTakeEvent]
    simp
  have htakerPositive : 0 < accessLaw sourceTakeEvent := by
    rw [measure_congr hsourceTakeEvent]
    simp
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability accessLaw sourceTakeEvent
      (ne_of_gt htakerPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
      (ne_of_gt hreporterPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hreporterLaw : reporterLaw =
      lg21NormalizedRestriction takerLaw (baseScore ⁻¹' reportSet) := by
    simpa [rawLaw, accessLaw, sourceTakeEvent, takerLaw, baseScore, reportSet,
      base, score, skill, lg21HiddenAccessTakerEvent] using
      (lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw E)
  have hreporterAcTaker : reporterLaw ≪ takerLaw := by
    rw [hreporterLaw]
    exact Measure.smul_absolutelyContinuous.trans
      Measure.restrict_le_self.absolutelyContinuous
  have hrawFactor : accessLaw.map observationSkill =
      (baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
    calc
      accessLaw.map observationSkill =
          (accessLaw.map rawObservation).map association := by
            rw [Measure.map_map (MeasurableEquiv.measurable association)
              hrawObservation]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)).map association := by
            rw [show accessLaw.map rawObservation =
              baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
                (M.noiseVariance testFeature : ℝ) by
              simpa [accessLaw, rawObservation, base, score, skill] using hsourceFactor]
      _ = gaussianSignalBaseScoreLatentLaw baseLaw baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ) := by rfl
      _ = (baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
            simpa [scoreKernel, posteriorKernel] using
              (gaussianSignalBaseScoreLatentLaw_factorization
                baseLaw baseMean hbaseMean priorVariance
                (M.noiseVariance testFeature : ℝ)
                hpriorVariance hnoiseVariance)
  have hbaseScoreLaw : accessLaw.map baseScore = baseLaw ⊗ₘ scoreKernel := by
    calc
      accessLaw.map baseScore = (accessLaw.map observationSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservationSkill]
        rfl
      _ = ((baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel).map Prod.fst := by
        rw [hrawFactor]
      _ = baseLaw ⊗ₘ scoreKernel := Measure.fst_compProd _ _
  have hjoint : accessLaw.map observationSkill =
      accessLaw.map baseScore ⊗ₘ posteriorKernel := by
    rw [hrawFactor, hbaseScoreLaw]
  have hjointTaker : takerLaw.map observationSkill =
      takerLaw.map baseScore ⊗ₘ posteriorKernel := by
    rw [htakerEqAccess]
    exact hjoint
  have hcondTaker : condDistrib skill baseScore takerLaw =ᵐ[
      takerLaw.map baseScore] posteriorKernel := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hbaseScore hskill hjointTaker
  have hreporterBaseScoreAc : reporterLaw.map baseScore ≪ takerLaw.map baseScore :=
    hreporterAcTaker.map hbaseScore
  have hcondReporter : condDistrib skill baseScore takerLaw =ᵐ[
      reporterLaw.map baseScore] posteriorKernel :=
    hreporterBaseScoreAc.ae_le hcondTaker
  have hcondReporterPullback : ∀ᵐ student ∂reporterLaw,
      condDistrib skill baseScore takerLaw (baseScore student) =
        posteriorKernel (baseScore student) := by
    exact ae_of_ae_map hbaseScore.aemeasurable hcondReporter
  have hreportedTaker : (fun student => E.reportedPayoff
      (base student) (score student)) =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill baseScore takerLaw (baseScore student) := by
    simpa [rawLaw, accessLaw, sourceTakeEvent, takerLaw, baseScore, reportSet,
      reporterLaw, base, score, skill, lg21HiddenAccessTakerEvent] using
      (E.reportedPayoff_eq_takerBaseScoreCondMean_ae hreporterPositive)
  have hreportedPosterior : (fun student => E.reportedPayoff
      (base student) (score student)) =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill ∂posteriorKernel (baseScore student) := by
    filter_upwards [hreportedTaker, hcondReporterPullback] with student hPBO hcond
    rw [hPBO, hcond]
  have hposteriorMeanMeasurable : Measurable (fun publicScore =>
      ∫ latentSkill, latentSkill ∂posteriorKernel publicScore) := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  have hPBOBaseScore : ∀ᵐ publicScore ∂reporterLaw.map baseScore,
      E.reportedPayoff publicScore.1 publicScore.2 =
        ∫ latentSkill, latentSkill ∂posteriorKernel publicScore := by
    rw [MeasureTheory.ae_map_iff hbaseScore.aemeasurable
      (measurableSet_eq_fun E.reportedPayoff_measurable hposteriorMeanMeasurable)]
    simpa [baseScore, base, score] using hreportedPosterior
  exact hPBOBaseScore

end

end LG21TestOptionalPolicies
