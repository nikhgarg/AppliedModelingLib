import LG21TestOptionalPolicies.ObservedAccessOptionalD6OutputBridge
import LG21TestOptionalPolicies.ObservedAccessLemma41LiteralSourceCloseout

/-!
# Shared observed-access output transport for LG21 Section 4

The three observed-access protocols have different action timing, but after
Lemma 4.1 they share the same public record: the full non-test base and the
reported test score.  This module states that common output transport once,
with the action collapse and the on-path PBO identity explicit.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The realized school output attached to an observed-access action.  The
no-report branch is retained in the definition, so the all-report hypothesis
below is a genuine behavioral input rather than a change of output function. -/
def lg21ObservedAccessActualOutput
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score : Omega -> ℝ)
    (action : Omega -> LG21AccessAction)
    (reportedPayoff : Base -> ℝ -> ℝ) (noReportPayoff : Base -> ℝ) : Omega -> ℝ :=
  fun omega =>
    if (action omega).reportsScore = true then
      reportedPayoff (base omega) (score omega)
    else noReportPayoff (base omega)

/-- Once a protocol has established literal all-taking and all-reporting, its
realized output is its reported-score output almost everywhere. -/
theorem lg21ObservedAccessActualOutput_eq_reported_ae_of_all_take_and_report
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (score : Omega -> ℝ)
    (action : Omega -> LG21AccessAction)
    (reportedPayoff : Base -> ℝ -> ℝ) (noReportPayoff : Base -> ℝ)
    (hall : ∀ᵐ omega ∂law,
      action omega = LG21AccessAction.takeAndReport) :
    lg21ObservedAccessActualOutput base score action reportedPayoff noReportPayoff =ᵐ[law]
      fun omega => reportedPayoff (base omega) (score omega) := by
  filter_upwards [hall] with omega haction
  simp [lg21ObservedAccessActualOutput, haction, LG21AccessAction.takeAndReport]

/-- The PBO condition after a protocol has collapsed to the full observed
`(base, score)` record.  It is intentionally an explicit semantic condition,
not an inference from an opaque equilibrium-consistency field. -/
def LG21ObservedAccessAllReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (reportedPayoff : Base -> ℝ -> ℝ) : Prop :=
  (fun omega => reportedPayoff (base omega) (score omega)) =ᵐ[law]
    law[skill | MeasurableSpace.comap (fun omega => (base omega, score omega))
      inferInstance]

/-- Protocol-independent source transport from an all-take/all-report PBO
output to the Definition 6 access-side estimator, as an almost-everywhere
identity of the literal realized output.  The action map may encode the
mandatory, optional, or report-required protocol; only the proved all-report
event and its literal on-path PBO are used. -/
theorem lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
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
    (action : Bool × (ℝ × (Feature -> ℝ)) -> LG21AccessAction)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      action student = LG21AccessAction.takeAndReport)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
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
    lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      action reportedPayoff noReportPayoff =ᵐ[law]
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
      lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          action reportedPayoff noReportPayoff =ᵐ[law]
        fun student => reportedPayoff
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) := by
    simpa [law] using
      (lg21ObservedAccessActualOutput_eq_reported_ae_of_all_take_and_report
        law (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature) action
        reportedPayoff noReportPayoff hall)
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
  have hreportedPBO' :
      (fun student => reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[law]
        law[lg21ContinuousPopulationSkill |
          MeasurableSpace.comap observation inferInstance] := by
    simpa [LG21ObservedAccessAllReportPBO, law, observation] using hreportedPBO
  have hreported :
      (fun student => reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[law]
        fun student => lg21D6GaussianPBOEstimate S (observation student) := by
    filter_upwards [hreportedPBO', hcondExp, hd6Pullback] with
        student hpbo hmean hd6
    rw [hpbo, hmean, hd6]
  filter_upwards [hactual, hreported] with student hactual hreported
  rw [hactual, hreported]

/-- Law-level corollary of
`lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo`.
The a.e. source identity is kept separately so downstream conditional-kernel
arguments do not have to reconstruct it from this marginal equality. -/
theorem lg21ContinuousGaussianAccessPopulation_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
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
    (action : Bool × (ℝ × (Feature -> ℝ)) -> LG21AccessAction)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      action student = LG21AccessAction.takeAndReport)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
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
    law.map (lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      action reportedPayoff noReportPayoff) =
      (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
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
  have hactual :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization action reportedPayoff noReportPayoff
      hall hreportedPBO
  calc
    law.map (lg21ObservedAccessActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        action reportedPayoff noReportPayoff) =
        law.map (fun student => lg21D6GaussianPBOEstimate S (observation student)) := by
          exact Measure.map_congr (by simpa [law, observation] using hactual)
    _ = (law.map observation).map (lg21D6GaussianPBOEstimate S) := by
      rw [Measure.map_map (lg21D6GaussianPBOEstimate_measurable S) hobservation]
      rfl

/-- Protocol-independent Section 4 transport to the literal no-access
resampling output.  This is the shared law-level step used after any of the
three Lemma 4.1 action conclusions has supplied all taking and reporting. -/
theorem lg21ContinuousGaussianAccessPopulation_actualOutput_eq_noAccessResampling_of_all_take_report_and_pbo
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
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
    (action : Bool × (ℝ × (Feature -> ℝ)) -> LG21AccessAction)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      action student = LG21AccessAction.takeAndReport)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
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
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    accessLaw.map (lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      action reportedPayoff noReportPayoff) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
  intro S accessLaw noAccessLaw
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  have hactual :=
    lg21ContinuousGaussianAccessPopulation_actualOutputLaw_eq_d6_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance hbaseVariance
      htestNoiseVariance hfullBaseFactorization action reportedPayoff noReportPayoff
      hall hreportedPBO
  have hd6 :=
    lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  calc
    accessLaw.map (lg21ObservedAccessActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        action reportedPayoff noReportPayoff) =
        (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
          simpa [accessLaw, observation] using hactual
    _ = Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
          simpa [accessLaw, noAccessLaw, observation] using hd6

/-- Mandatory-given-access specialization of the shared transport.  The
mandatory carrier supplies the forced literal action; the separately explicit
PBO condition is exactly the source policy assumption on the attained full
record, not a null-branch completion. -/
theorem lg21ContinuousGaussianAccessPopulation_mandatory_actualOutput_eq_noAccessResampling_of_pbo
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
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
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
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
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    accessLaw.map (lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      mandatory.action reportedPayoff noReportPayoff) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
  have hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      mandatory.action student = LG21AccessAction.takeAndReport :=
    lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      M haccess mandatory.action mandatory.feasible
  exact
    lg21ContinuousGaussianAccessPopulation_actualOutput_eq_noAccessResampling_of_all_take_report_and_pbo
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization mandatory.action
      reportedPayoff noReportPayoff hall hreportedPBO

/-- Literal optional sequential choices as Definition 1 access actions.  This
preserves the distinct take-and-withhold branch even though its realized school
output agrees with the no-take branch. -/
def lg21OptionalSequentialAccessAction
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ) : Omega -> LG21AccessAction :=
  fun omega =>
    if E.takeDecision (skill omega) (base omega) = true then
      if E.reportDecision (base omega) (score omega) = true then
        LG21AccessAction.takeAndReport
      else LG21AccessAction.takeAndWithhold
    else LG21AccessAction.noTake

/-- The literal optional output is definitionally the shared action-output
function for the corresponding sequential action. -/
theorem lg21OptionalSequentialActualOutput_eq_observedAccessActualOutput
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ) :
    lg21OptionalSequentialActualOutput base score skill E =
      lg21ObservedAccessActualOutput base score
        (lg21OptionalSequentialAccessAction base score skill E)
        E.reportedPayoff E.noReportPayoff := by
  funext omega
  by_cases htake : E.takeDecision (skill omega) (base omega) = true
  · by_cases hreport : E.reportDecision (base omega) (score omega) = true
    · simp [lg21OptionalSequentialActualOutput,
        lg21ObservedAccessActualOutput, lg21OptionalSequentialAccessAction,
        htake, hreport, LG21AccessAction.takeAndReport]
    · simp [lg21OptionalSequentialActualOutput,
        lg21ObservedAccessActualOutput, lg21OptionalSequentialAccessAction,
        htake, hreport, LG21AccessAction.takeAndWithhold]
  · simp [lg21OptionalSequentialActualOutput,
      lg21ObservedAccessActualOutput, lg21OptionalSequentialAccessAction,
      htake, LG21AccessAction.noTake]

/-- The optional action is all taking and reporting whenever the literal
sequential closeout has established both source action decisions almost
everywhere. -/
theorem lg21OptionalSequentialAccessAction_ae_takeAndReport_of_all_take_and_report
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ)
    (hall : ∀ᵐ omega ∂law,
      E.takeDecision (skill omega) (base omega) = true ∧
        E.reportDecision (base omega) (score omega) = true) :
    ∀ᵐ omega ∂law,
      lg21OptionalSequentialAccessAction base score skill E omega =
        LG21AccessAction.takeAndReport := by
  filter_upwards [hall] with omega htakeReport
  rcases htakeReport with ⟨htake, hreport⟩
  simp [lg21OptionalSequentialAccessAction, htake, hreport]

/-- Optional-protocol specialization of the common Section 4 output transport.
The only PBO used is the source carrier's actual reporter PBO, promoted to the
whole access population after its own literal closeout has proved that action
to have full measure. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_actualOutput_eq_noAccessResampling_of_literalSource
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
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    accessLaw.map (lg21OptionalSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
  intro S accessLaw noAccessLaw
  have hall :=
    lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  have hallAction : ∀ᵐ student ∂accessLaw,
      lg21OptionalSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data student =
          LG21AccessAction.takeAndReport := by
    simpa [accessLaw] using
      (lg21OptionalSequentialAccessAction_ae_takeAndReport_of_all_take_and_report
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data hall)
  have hoptionalPBO :=
    LG21ObservedAccessOptionalLiteralSourceEquilibrium.actual_report_pbo_of_all_take_and_report
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E
  have hreportedPBO : LG21ObservedAccessAllReportPBO accessLaw
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data.reportedPayoff := by
    simpa [LG21OptionalAllReportPBO, LG21ObservedAccessAllReportPBO, accessLaw]
      using hoptionalPBO
  have hshared :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_eq_noAccessResampling_of_all_take_report_and_pbo
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
      (lg21OptionalSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data)
      E.data.reportedPayoff E.data.noReportPayoff hallAction hreportedPBO
  have houtput :=
    lg21OptionalSequentialActualOutput_eq_observedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E.data
  calc
    accessLaw.map (lg21OptionalSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E.data) =
        accessLaw.map (lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21OptionalSequentialAccessAction
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature)) E.data)
          E.data.reportedPayoff E.data.noReportPayoff) := by
            rw [houtput]
    _ = Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
          simpa [accessLaw, noAccessLaw] using hshared

/-- Literal report-required action as the common source action object.  Taking
necessarily reports in this protocol, while the no-take branch remains present
until Lemma 4.1 has ruled it out almost everywhere. -/
def lg21ReportRequiredSequentialAccessAction
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Omega -> LG21AccessAction :=
  fun omega =>
    if E.takeDecision (skill omega) (base omega) = true then
      LG21AccessAction.takeAndReport
    else LG21AccessAction.noTake

/-- The actual school output for report-required testing, expressed through
the shared action-output definition. -/
def lg21ReportRequiredSequentialActualOutput
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Omega -> ℝ :=
  lg21ObservedAccessActualOutput base score
    (lg21ReportRequiredSequentialAccessAction base skill E)
    E.reportedPayoff E.noReportPayoff

/-- The report-required action is all taking and reporting whenever its
source-timed taking decision is true almost everywhere. -/
theorem lg21ReportRequiredSequentialAccessAction_ae_takeAndReport_of_all_take
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (skill : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (hall : ∀ᵐ omega ∂law,
      E.takeDecision (skill omega) (base omega) = true) :
    ∀ᵐ omega ∂law,
      lg21ReportRequiredSequentialAccessAction base skill E omega =
        LG21AccessAction.takeAndReport := by
  filter_upwards [hall] with omega htake
  simp [lg21ReportRequiredSequentialAccessAction, htake]

/-- Promote the report-required source carrier's on-path reporter PBO from
its normalized positive reporter law to the full access law after all taking.
This is valid only after the behavior theorem has made the reporter event full
measure, and it never assigns a value on an unattained branch. -/
theorem LG21FullPublicReportRequiredSourceEquilibrium.reported_pbo_of_all_take
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E)
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
  have hpbo := S.reported_pbo (by simpa [reporterEvent] using hreporterPositive)
  change
    (fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
      lg21NormalizedRestriction rawLaw reporterEvent]
      (lg21NormalizedRestriction rawLaw reporterEvent)[skill |
        MeasurableSpace.comap (fun omega => (base omega, score omega))
          inferInstance] at hpbo
  rw [hreporterLaw] at hpbo
  simpa [LG21ObservedAccessAllReportPBO,
    LG21FullPublicReportRequiredReportedPBO] using hpbo

/-- Report-required specialization of the shared Section 4 transport.  The
all-taking conclusion is derived from the literal source carrier and the
positive-mass stability semantics; its attained reporter PBO is then promoted
only because that event has become full measure. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_noAccessResampling_of_literalSource
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
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    accessLaw.map (lg21ReportRequiredSequentialActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill E) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
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
    (lg21ContinuousGaussianAccessPopulation_actualOutput_eq_noAccessResampling_of_all_take_report_and_pbo
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
      (lg21ReportRequiredSequentialAccessAction
        (lg21ContinuousPopulationBase testFeature)
        lg21ContinuousPopulationSkill E)
      E.reportedPayoff E.noReportPayoff hallAction hreportedPBO)

/-- Compact literal-source Section 4 closeout for all three observed-access
protocols.  The mandatory PBO is explicit because its behavioral carrier only
fixes actions; the optional and report-required PBOs are promoted from their
attained source branches after their respective literal action closeouts. -/
theorem lg21ContinuousGaussianAccessPopulation_allProtocols_actualOutput_eq_noAccessResampling_of_literalSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (mandatoryReportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (mandatoryNoReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) mandatoryReportedPayoff)
    (optional : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportRequiredTestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
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
    ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (reportRequiredSource.base_measurable.prodMk
          (reportRequiredSource.score_measurable.prodMk
            reportRequiredSource.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
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
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    accessLaw.map (lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff) =
        Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S) ∧
      accessLaw.map (lg21OptionalSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) optional.data) =
        Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S) ∧
      accessLaw.map (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired) =
        Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  intro reportRequiredSource hreportRequiredStable
  refine ⟨?_, ?_, ?_⟩
  · exact
      lg21ContinuousGaussianAccessPopulation_mandatory_actualOutput_eq_noAccessResampling_of_pbo
        M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization mandatory
        mandatoryReportedPayoff mandatoryNoReportPayoff hmandatoryReportedPBO
  · exact
      lg21ContinuousGaussianAccessPopulation_optional_actualOutput_eq_noAccessResampling_of_literalSource
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional baseLaw baseMean hbaseMean baseVariance
        hbaseVariance hfullBaseFactorization
  · exact
      lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_noAccessResampling_of_literalSource
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired hreportRequiredTestLaw baseLaw baseMean
        hbaseMean baseVariance hbaseVariance hfullBaseFactorization
        reportRequiredSource hreportRequiredStable

end

end LG21TestOptionalPolicies
