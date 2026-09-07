import LG21TestOptionalPolicies.ContinuousObservedAccessActualPBOBridge
import LG21TestOptionalPolicies.ObservedAccessOptionalSourceCloseout
import LG21TestOptionalPolicies.ObservedAccessOptionalSourceTimedCloseout
import LG21TestOptionalPolicies.Section4LiteralGaussianSourceBridge

/-!
# Actual-output transport for observed-access optional reporting

This module starts only after the literal optional source closeout has shown
that the realized `Y = X = 1` action occurs almost everywhere.  At that point
the school output is its reported-score output almost everywhere.  A separate,
explicit on-path PBO identity then identifies that output with the conditional
mean given the complete `(base, score)` observation.  The existing Section 4
Gaussian bridge turns that conditional mean into the Definition 6 estimator.

No theorem here reads an opaque equilibrium-consistency field or assigns a
PBO value to a zero-mass action history.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The actual school output for a literal optional sequential action.  A
student who does not both take and report is evaluated by the no-report
branch; only the attained report action exposes the score to the school. -/
def lg21OptionalSequentialActualOutput
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ) : Omega -> ℝ :=
  fun omega =>
    if E.takeDecision (skill omega) (base omega) = true ∧
        E.reportDecision (base omega) (score omega) = true
    then E.reportedPayoff (base omega) (score omega)
    else E.noReportPayoff (base omega)

/-- Once the literal sequential action is `take = report = true` almost
everywhere, the actual school output coincides with the reported-score output
almost everywhere. -/
theorem lg21OptionalSequentialActualOutput_eq_reported_ae_of_all_take_and_report
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ)
    (hall : ∀ᵐ omega ∂law,
      E.takeDecision (skill omega) (base omega) = true ∧
        E.reportDecision (base omega) (score omega) = true) :
    lg21OptionalSequentialActualOutput base score skill E =ᵐ[law]
      fun omega => E.reportedPayoff (base omega) (score omega) := by
  filter_upwards [hall] with omega htakeReport
  simp [lg21OptionalSequentialActualOutput, htakeReport]

/-- The literal PBO semantic needed after all access students report.  This
is the on-path conditional-mean identity for the complete observed
`(base, score)` record.  It is deliberately an explicit proof obligation,
not a consequence inferred from `estimationConsistent`. -/
def LG21OptionalAllReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ) : Prop :=
  (fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[law]
    law[skill | MeasurableSpace.comap (fun omega => (base omega, score omega))
      inferInstance]

/-- The literal actual-reporter PBO from the optional source carrier becomes
an all-population PBO only after the behavioral closeout has proved that the
actual report event has full mass.  This transport does not assign a belief to
a zero-mass history: before the collapse, the carrier field is stated under
the normalized actual-reporter law. -/
theorem LG21ObservedAccessOptionalLiteralSourceEquilibrium.actual_report_pbo_of_all_take_and_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature) :
    LG21OptionalAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let reportEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21OptionalSourceReportEvent
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      E.data.takeDecision E.data.reportDecision
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have hall : ∀ᵐ student ∂law,
      E.data.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.data.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true := by
    simpa [law] using
      (lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E)
  have hreporterAE : ∀ᵐ student ∂law, student ∈ reportEvent := by
    simpa [reportEvent, lg21OptionalSourceReportEvent] using hall
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
  have hpbo := E.actual_report_pbo (by simpa [law, reportEvent] using hreporterPositive)
  rw [hreporterLaw] at hpbo
  simpa [LG21OptionalAllReportPBO, law, reportEvent] using hpbo

/-- Source-literal action-to-D6 transport at the realized-output level.  The
behavioral premise is the already-established all-take/report conclusion; the
PBO premise is only the on-path conditional mean on that resulting full-report
population. -/
theorem lg21_optional_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
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
    (E : LG21OptionalSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true)
    (hreportedPBO : LG21OptionalAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E) :
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
    lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E =ᵐ[law]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  intro S law observation
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hactual :
      lg21OptionalSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) E =ᵐ[law]
        fun student => E.reportedPayoff
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) := by
    simpa [law] using
      (lg21OptionalSequentialActualOutput_eq_reported_ae_of_all_take_and_report
        law (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E hall)
  have hcondExp :
      law[lg21ContinuousPopulationSkill |
        MeasurableSpace.comap observation inferInstance] =ᵐ[law]
        fun student => ∫ latentSkill, latentSkill ∂condDistrib
          lg21ContinuousPopulationSkill observation law (observation student) := by
    exact condExp_ae_eq_integral_condDistrib' hobservation
      (lg21ContinuousGaussianAccessPopulation_skill_integrable M haccess)
  have hd6Observation :=
    lg21ContinuousGaussianAccessPopulation_d6Estimate_eq_condDistribMean_ae
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  have hd6Pullback : ∀ᵐ student ∂law,
      lg21D6GaussianPBOEstimate S (observation student) =
        ∫ latentSkill, latentSkill ∂condDistrib
          lg21ContinuousPopulationSkill observation law (observation student) := by
    exact ae_of_ae_map hobservation.aemeasurable hd6Observation
  have hreported :
      (fun student => E.reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[law]
        fun student => lg21D6GaussianPBOEstimate S (observation student) := by
    filter_upwards [hreportedPBO, hcondExp, hd6Pullback] with
        student hpbo hmean hd6
    rw [hpbo, hmean, hd6]
  filter_upwards [hactual, hreported] with student hactualOutput hreportedOutput
  rw [hactualOutput, hreportedOutput]

/-- The marginal-law form of the optional action-to-Definition-6 transport.
It is a direct consequence of the realized-output identity above. -/
theorem lg21_optional_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
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
    (E : LG21OptionalSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true)
    (hreportedPBO : LG21OptionalAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E) :
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
    law.map (lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E) =
      (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
  intro S law observation
  have houtput :=
    lg21_optional_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization E hall hreportedPBO
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  calc
    law.map (lg21OptionalSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E) =
        law.map (fun student => lg21D6GaussianPBOEstimate S (observation student)) :=
      Measure.map_congr houtput
    _ = (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
      rw [Measure.map_map (lg21D6GaussianPBOEstimate_measurable S) hobservation]
      rfl

/-- Continuous literal-source wrapper for the optional behavior closeout.
The actual-reporter PBO is carried under its normalized realized action law
and is promoted to the full access law only after the proved all-report
endpoint; all action and Gaussian-factorization facts are otherwise derived
from the literal population and existing optional carrier. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_actualOutputLaw_eq_d6
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
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
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    law.map (lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
      (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  have hreportedPBO :=
    LG21ObservedAccessOptionalLiteralSourceEquilibrium.actual_report_pbo_of_all_take_and_report
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  exact lg21_optional_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
    M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
    htestNoiseVariance hfullBaseFactorization E.data hall hreportedPBO

/-- Literal optional source wrapper for the realized-output identity. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_actualOutput_eq_d6_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
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
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data =ᵐ[law]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  have hreportedPBO :=
    LG21ObservedAccessOptionalLiteralSourceEquilibrium.actual_report_pbo_of_all_take_and_report
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  exact lg21_optional_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
    M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
    htestNoiseVariance hfullBaseFactorization E.data hall hreportedPBO

/-- Actual school output for the explicit source-timed optional carrier. -/
def lg21OptionalSourceTimedActualOutput
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base) : Omega -> ℝ :=
  fun omega =>
    if A.takeDecision (skill omega) (base omega) = true ∧
        A.reportDecision (base omega) (score omega) = true
    then A.reportedPayoff (base omega) (score omega)
    else A.noReportPayoff (base omega)

/-- The source-timed output is definitionally the sequential output of the
local technical adapter. -/
theorem lg21OptionalSourceTimedActualOutput_eq_sequentialAdapter
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base) :
    lg21OptionalSourceTimedActualOutput base score skill A =
      lg21OptionalSequentialActualOutput base score skill A.toSequentialData := rfl

/-- On-path all-report PBO for the explicit source-timed action carrier. -/
def LG21OptionalSourceTimedAllReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base) : Prop :=
  (fun omega => A.reportedPayoff (base omega) (score omega)) =ᵐ[law]
    law[skill | MeasurableSpace.comap (fun omega => (base omega, score omega))
      inferInstance]

/-- Promote the literal actual-report PBO to the full access law only after
the source-timed behavior proof has made the actual report action full mass. -/
theorem LG21ObservedAccessOptionalSourceTimedEquilibrium.actual_report_pbo_of_all_take_and_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature) :
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
  have hall : ∀ᵐ student ∂law,
      E.actions.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.actions.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true := by
    simpa [law] using
      (lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae_of_sourceTimed
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E)
  have hreporterAE : ∀ᵐ student ∂law, student ∈ reportEvent := by
    simpa [reportEvent, lg21OptionalSourceReportEvent] using hall
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

/-- Source-timed optional action-to-Definition-6 transport.  The generic
sequential record appears only inside the local compatibility adapter used by
the already-proved measure-theoretic transport. -/
theorem lg21_optional_sourceTimed_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
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
    (A : LG21OptionalSourceTimedActions
      (LG21NonTestFeature Feature testFeature -> ℝ))
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      A.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        A.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true)
    (hreportedPBO : LG21OptionalSourceTimedAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) A) :
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
      (lg21ContinuousPopulationSkill (Feature := Feature)) A) =
      (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
  intro S law observation
  have houtput :
      lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) A =ᵐ[law]
        fun student => lg21D6GaussianPBOEstimate S (observation student) := by
    have htransport :=
      lg21_optional_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
        htestNoiseVariance hfullBaseFactorization A.toSequentialData
        (by
          simpa [LG21OptionalSourceTimedActions.toSequentialData] using hall)
        (by
          simpa [LG21OptionalAllReportPBO, LG21OptionalSourceTimedAllReportPBO,
            LG21OptionalSourceTimedActions.toSequentialData] using hreportedPBO)
    simpa [lg21OptionalSourceTimedActualOutput,
      LG21OptionalSourceTimedActions.toSequentialData] using htransport
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  calc
    law.map (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) A) =
        law.map (fun student => lg21D6GaussianPBOEstimate S (observation student)) :=
      Measure.map_congr houtput
    _ = (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
      rw [Measure.map_map (lg21D6GaussianPBOEstimate_measurable S) hobservation]
      rfl

/-- The source-timed adapter preserves the realized-output identity, not only
the induced marginal output law. -/
theorem lg21_optional_sourceTimed_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
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
    (A : LG21OptionalSourceTimedActions
      (LG21NonTestFeature Feature testFeature -> ℝ))
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      A.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        A.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true)
    (hreportedPBO : LG21OptionalSourceTimedAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) A) :
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
      (lg21ContinuousPopulationSkill (Feature := Feature)) A =ᵐ[law]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
  have htransport :=
    lg21_optional_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization A.toSequentialData
      (by
        simpa [LG21OptionalSourceTimedActions.toSequentialData] using hall)
      (by
        simpa [LG21OptionalAllReportPBO, LG21OptionalSourceTimedAllReportPBO,
          LG21OptionalSourceTimedActions.toSequentialData] using hreportedPBO)
  simpa [lg21OptionalSourceTimedActualOutput,
    LG21OptionalSourceTimedActions.toSequentialData] using htransport

/-- Continuous observed-access source-timed optional transport to the
Definition-6 access-side estimator. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutputLaw_eq_d6
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
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
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    law.map (lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.actions) =
      (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae_of_sourceTimed
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  have hreportedPBO :=
    LG21ObservedAccessOptionalSourceTimedEquilibrium.actual_report_pbo_of_all_take_and_report
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  exact lg21_optional_sourceTimed_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
    M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
    htestNoiseVariance hfullBaseFactorization E.actions hall hreportedPBO

/-- Source-timed literal carrier wrapper for the realized-output identity. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutput_eq_d6_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
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
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae_of_sourceTimed
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  have hreportedPBO :=
    LG21ObservedAccessOptionalSourceTimedEquilibrium.actual_report_pbo_of_all_take_and_report
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  exact lg21_optional_sourceTimed_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
    M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
    htestNoiseVariance hfullBaseFactorization E.actions hall hreportedPBO

end

end LG21TestOptionalPolicies
