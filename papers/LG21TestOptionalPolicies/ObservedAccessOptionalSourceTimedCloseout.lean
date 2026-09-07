import LG21TestOptionalPolicies.ObservedAccessOptionalSourceCloseout

/-!
# Source-timed observed-access optional-reporting closeout

This module provides the credit-bearing optional-reporting interface for the
observed-access Lemma 4.1 path.  It keeps the paper's source-timed actions,
the two best-response implications used by the proof, and the literal PBO on
the actual full public action branch explicit.  The older wrapper based on
`LG21OptionalSequentialEquilibriumData` remains a compatibility path only.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-- The source-timed optional-reporting action data used by the observed-access
closeout.  The legacy sequential record is available only as a local adapter
for technical lemmas that still use its expected-payoff notation. -/
structure LG21OptionalSourceTimedActions
    (Base : Type*) [MeasurableSpace Base] where
  testLaw : ℝ -> Base -> Measure ℝ
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision : ℝ -> Base -> Bool
  reportDecision : Base -> ℝ -> Bool
  reportedPayoff : Base -> ℝ -> ℝ
  noReportPayoff : Base -> ℝ
  continuationPayoff_integrable : ∀ skill base,
    Integrable (fun score =>
      if reportDecision base score then reportedPayoff base score
      else noReportPayoff base) (testLaw skill base)

namespace LG21OptionalSourceTimedActions

/-- Local compatibility adapter for reusable sequential expected-payoff
lemmas.  Its consistency field has no source-facing role. -/
def toSequentialData
    {Base : Type*} [MeasurableSpace Base]
    (A : LG21OptionalSourceTimedActions Base) :
    LG21OptionalSequentialEquilibriumData ℝ Base ℝ where
  testLaw := A.testLaw
  testLaw_isProbability := A.testLaw_isProbability
  takeDecision := A.takeDecision
  reportDecision := A.reportDecision
  reportedPayoff := A.reportedPayoff
  noReportPayoff := A.noReportPayoff
  continuationPayoff_integrable := A.continuationPayoff_integrable
  estimationConsistent := True

end LG21OptionalSourceTimedActions

/-- The actual pre-score taker set at one public base.  Unlike the legacy
fibre witness, this set is definitionally fixed by the source action rule. -/
def lg21OptionalActualTakerSet
    {Base : Type*} [MeasurableSpace Base]
    (A : LG21OptionalSourceTimedActions Base) (publicBase : Base) : Set ℝ :=
  {latentSkill | A.takeDecision latentSkill publicBase = true}

/-- Literal PBO data for a positive actual reporter fibre.  Both the selected
latent population and the report event are induced by the one actual source
action rule; no latent band or arbitrary cohort is supplied by the caller. -/
structure LG21OptionalActualFullActionReporterFibrePBO
    {Base : Type*} [MeasurableSpace Base]
    (A : LG21OptionalSourceTimedActions Base)
    (publicBase : Base) (priorMean priorVariance noiseVariance : ℝ) : Prop where
  taker_measurable : MeasurableSet (lg21OptionalActualTakerSet A publicBase)
  taker_positive : 0 < gaussianReal priorMean priorVariance.toNNReal
    (lg21OptionalActualTakerSet A publicBase)
  report_measurable : MeasurableSet
    {score | A.reportDecision publicBase score = true}
  reporter_positive :
    0 < normalizedSelectedBase
      (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ lg21OptionalActualTakerSet A publicBase)
      {score | A.reportDecision publicBase score = true}
  reported_pbo :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    A.reportedPayoff publicBase =ᵐ[
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ lg21OptionalActualTakerSet A publicBase))
        {score | A.reportDecision publicBase score = true}]
      fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ lg21OptionalActualTakerSet A publicBase) score

namespace LG21OptionalActualFullActionReporterFibrePBO

/-- A literal positive actual reporter fibre gives all taking at that public
base using only the two source best-response implications. -/
theorem all_take
    {Base : Type*} [MeasurableSpace Base]
    {A : LG21OptionalSourceTimedActions Base}
    {publicBase : Base} {priorMean priorVariance noiseVariance : ℝ}
    (H : LG21OptionalActualFullActionReporterFibrePBO A publicBase
      priorMean priorVariance noiseVariance)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (htestLaw : ∀ latentSkill,
      A.testLaw latentSkill publicBase =
        gaussianReal latentSkill noiseVariance.toNNReal)
    (hreportBestResponse : ∀ score,
      A.reportDecision publicBase score = true ->
        A.noReportPayoff publicBase ≤ A.reportedPayoff publicBase score)
    (htakeBestResponse : ∀ latentSkill,
      A.takeDecision latentSkill publicBase = false ->
        (∫ score,
          if A.reportDecision publicBase score then
            A.reportedPayoff publicBase score
          else A.noReportPayoff publicBase
          ∂A.testLaw latentSkill publicBase) ≤ A.noReportPayoff publicBase) :
    ∀ latentSkill, A.takeDecision latentSkill publicBase = true := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hall := lg21_positive_reporter_selectedGaussian_all_take_at_base_of_bestResponses
    A.toSequentialData publicBase priorMean priorVariance noiseVariance
      (lg21OptionalActualTakerSet A publicBase)
      hpriorVariance hnoiseVariance H.taker_measurable H.taker_positive
      H.report_measurable H.reporter_positive
      (by
        intro latentSkill
        simpa [LG21OptionalSourceTimedActions.toSequentialData] using
          htestLaw latentSkill)
      (by
        simpa [LG21OptionalSourceTimedActions.toSequentialData] using H.reported_pbo)
      (by
        intro score hreport
        simpa [LG21OptionalSourceTimedActions.toSequentialData] using
          hreportBestResponse score hreport)
      (by
        intro latentSkill hnoTake
        simpa [LG21OptionalSourceTimedActions.toSequentialData,
          lg21OptionalSequentialTakeExpectedPayoff,
          lg21OptionalSequentialContinuationPayoff] using
          htakeBestResponse latentSkill hnoTake)
  simpa [LG21OptionalSourceTimedActions.toSequentialData] using hall

end LG21OptionalActualFullActionReporterFibrePBO

/-- Source closeout using explicit source-timed action data.  The positive
reporter PBO is for the actual full `take = report = true` action rule, while
the two stability fields handle the two positive-mass deviations separately. -/
theorem lg21_optional_source_all_take_and_report_ae_of_explicit_bestResponses
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (A : LG21OptionalSourceTimedActions Base)
    (htake : Measurable (fun omega => A.takeDecision (skill omega) (base omega)))
    (hreport : Measurable (fun omega => A.reportDecision (base omega) (score omega)))
    (htakePublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      A.takeDecision profile.2.2 profile.1))
    (hreportPublic : Measurable (fun profile : Base × (ℝ × ℝ) =>
      A.reportDecision profile.1 profile.2.1))
    (hreportBestResponse : ∀ publicBase score,
      A.reportDecision publicBase score = true ->
        A.noReportPayoff publicBase ≤ A.reportedPayoff publicBase score)
    (htakeBestResponse : ∀ latentSkill publicBase,
      A.takeDecision latentSkill publicBase = false ->
        (∫ score,
          if A.reportDecision publicBase score then
            A.reportedPayoff publicBase score
          else A.noReportPayoff publicBase
          ∂A.testLaw latentSkill publicBase) ≤ A.noReportPayoff publicBase)
    (hzeroReporterStable : LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      A.takeDecision A.reportDecision)
    (hpartialReporterStable :
      LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
        sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
          A.takeDecision A.reportDecision)
    (hactualPositiveReporterFibre : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalSequentialFullPublicReportSet
          A.takeDecision A.reportDecision)
        publicBase ≠ 0 ->
      LG21OptionalActualFullActionReporterFibrePBO A publicBase
        (baseMean publicBase) baseVariance noiseVariance)
    (htestLaw : ∀ publicBase latentSkill,
      A.testLaw latentSkill publicBase =
        gaussianReal latentSkill noiseVariance.toNNReal) :
    ∀ᵐ omega ∂sourceLaw,
      A.takeDecision (skill omega) (base omega) = true ∧
        A.reportDecision (base omega) (score omega) = true := by
  let reportEvent : Set (Base × (ℝ × ℝ)) :=
    lg21OptionalSequentialFullPublicReportSet A.takeDecision A.reportDecision
  have hpositiveReporterAllTake : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        reportEvent publicBase ≠ 0 ->
      ∀ latentSkill, A.takeDecision latentSkill publicBase = true := by
    intro publicBase hpositive
    have H := hactualPositiveReporterFibre publicBase
      (by simpa [reportEvent] using hpositive)
    apply H.all_take hbaseVariance hnoiseVariance
    · exact htestLaw publicBase
    · exact hreportBestResponse publicBase
    · intro latentSkill hnoTake
      exact htakeBestResponse latentSkill publicBase hnoTake
  have hnoTakeZero : sourceLaw
      {omega | A.takeDecision (skill omega) (base omega) = false} = 0 := by
    exact lg21_optional_source_noTake_mass_zero_of_positiveReporter_allTake
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
      hsourceFactor A.takeDecision A.reportDecision htake hreport
      htakePublic hreportPublic hzeroReporterStable
      (by simpa [reportEvent] using hpositiveReporterAllTake) 0
  have htakeBad : {omega | ¬ A.takeDecision (skill omega) (base omega) = true} =
      {omega | A.takeDecision (skill omega) (base omega) = false} := by
    ext omega
    cases htakeValue : A.takeDecision (skill omega) (base omega) <;>
      simp [htakeValue]
  have hallTake : ∀ᵐ omega ∂sourceLaw,
      A.takeDecision (skill omega) (base omega) = true := by
    rw [ae_iff, htakeBad]
    exact hnoTakeZero
  let scoreNoReport : Set Omega :=
    {omega | A.reportDecision (base omega) (score omega) = false}
  have hnoReportImpossible : ¬ 0 < sourceLaw scoreNoReport := by
    simpa [scoreNoReport] using
      (lg21_optional_no_positive_currentNoReport_of_recalibratedEntry_stable
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
        hsourceFactor A.takeDecision A.reportDecision hallTake hpartialReporterStable)
  have hnoReportZero : sourceLaw scoreNoReport = 0 :=
    le_antisymm (not_lt.mp hnoReportImpossible) (zero_le _)
  have hreportBad : {omega | ¬ A.reportDecision (base omega) (score omega) = true} =
      scoreNoReport := by
    ext omega
    cases hreportValue : A.reportDecision (base omega) (score omega) <;>
      simp [scoreNoReport, hreportValue]
  have hreportAE : ∀ᵐ omega ∂sourceLaw,
      A.reportDecision (base omega) (score omega) = true := by
    rw [ae_iff, hreportBad]
    exact hnoReportZero
  filter_upwards [hallTake, hreportAE] with omega htakeValue hreportValue
  exact ⟨htakeValue, hreportValue⟩

/-- Concrete observed-access source equilibrium for optional reporting.  The
source action functions and the two best-response implications are explicit;
there is no `definition1` field or opaque equilibrium-consistency premise. -/
structure LG21ObservedAccessOptionalSourceTimedEquilibrium
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) where
  actions : LG21OptionalSourceTimedActions
    (LG21NonTestFeature Feature testFeature -> ℝ)
  takeDecision_measurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    actions.takeDecision pair.2 pair.1)
  reportDecision_measurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    actions.reportDecision pair.1 pair.2)
  /-- Definition 1's full post-score binary best-response condition, stated
  directly on the source report action. -/
  report_best_response : ∀ publicBase,
    NoProfitableBinaryChoiceDeviation
      (fun score => actions.reportDecision publicBase score = true)
      (actions.reportedPayoff publicBase)
      (fun _ => actions.noReportPayoff publicBase)
  /-- Definition 1's full pre-score binary best-response condition, stated
  directly on the source taking action. -/
  take_best_response : ∀ publicBase,
    NoProfitableBinaryChoiceDeviation
      (fun latentSkill => actions.takeDecision latentSkill publicBase = true)
      (fun latentSkill => ∫ score,
        if actions.reportDecision publicBase score then
          actions.reportedPayoff publicBase score
        else actions.noReportPayoff publicBase
        ∂actions.testLaw latentSkill publicBase)
      (fun _ => actions.noReportPayoff publicBase)
  local_entry_stable :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
        ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
          lg21ContinuousPopulationSkill_measurable))
      actions.takeDecision actions.reportDecision
  recalibrated_report_entry_stable :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
        ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
          lg21ContinuousPopulationSkill_measurable))
      actions.takeDecision actions.reportDecision
  /-- Definition 1's known-decision-function PBO semantics on a positive
  public reporter fibre.  The fibre is induced by the actual full action
  rule, rather than by an existential latent cohort. -/
  actual_full_action_reporter_fibre_pbo : ∀
      (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
      (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ)
      (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ->
      0 < baseVariance ->
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationBase testFeature student,
            (lg21ContinuousPopulationFeature testFeature student,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) ->
      ∀ publicBase,
        selectionMass
          (gaussianSignalJointKernel baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ))
          (lg21OptionalSequentialFullPublicReportSet
            actions.takeDecision actions.reportDecision)
          publicBase ≠ 0 ->
        LG21OptionalActualFullActionReporterFibrePBO actions publicBase
          (baseMean publicBase) baseVariance
          (M.noiseVariance testFeature : ℝ)
  test_law_gaussian : ∀ publicBase latentSkill,
    actions.testLaw latentSkill publicBase =
      gaussianReal latentSkill (M.noiseVariance testFeature)
  /-- Literal PBO on the actual full `take = report = true` source branch. -/
  actual_report_integrable : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))
  actual_report_pbo : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    (fun student => actions.reportedPayoff
      (lg21ContinuousPopulationBase testFeature student)
      (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            actions.takeDecision actions.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (fun student =>
              (lg21ContinuousPopulationBase testFeature student,
                lg21ContinuousPopulationFeature testFeature student))
              inferInstance]
  /-- Literal PBO on the actual complement of the full report action. -/
  actual_noReport_integrable : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))
  actual_noReport_pbo : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    (fun student => actions.noReportPayoff
      (lg21ContinuousPopulationBase testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceNoReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            actions.takeDecision actions.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (lg21ContinuousPopulationBase testFeature)
              inferInstance]

/-- Observed-access optional-reporting closeout through the source-timed
carrier.  The local sequential adapter is used only by the strict-gain lemma;
the endpoint itself consumes explicit best responses and actual-branch PBOs. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae_of_sourceTimed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.actions.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
        E.actions.reportDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true := by
  let sourceLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  letI : IsProbabilityMeasure sourceLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable score := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have htake : Measurable (fun student =>
      E.actions.takeDecision (skill student) (base student)) := by
    exact E.takeDecision_measurable.comp (hbase.prodMk hskill)
  have hreport : Measurable (fun student =>
      E.actions.reportDecision (base student) (score student)) := by
    exact E.reportDecision_measurable.comp (hbase.prodMk hscore)
  have htakePublic : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
      E.actions.takeDecision profile.2.2 profile.1) := by
    exact E.takeDecision_measurable.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hreportPublic : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
      E.actions.reportDecision profile.1 profile.2.1) := by
    exact E.reportDecision_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hactualPositiveReporterFibre : ∀ publicBase,
      selectionMass
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ))
        (lg21OptionalSequentialFullPublicReportSet
          E.actions.takeDecision E.actions.reportDecision)
        publicBase ≠ 0 ->
      LG21OptionalActualFullActionReporterFibrePBO E.actions publicBase
        (baseMean publicBase) baseVariance
        (M.noiseVariance testFeature : ℝ) := by
    exact E.actual_full_action_reporter_fibre_pbo
      baseLaw baseMean baseVariance hbaseMean
      hbaseLaw hbaseVariance hsourceFactor
  have htestLaw : ∀ publicBase latentSkill,
      E.actions.testLaw latentSkill publicBase =
        gaussianReal latentSkill (M.noiseVariance testFeature : ℝ).toNNReal := by
    intro publicBase latentSkill
    simpa using E.test_law_gaussian publicBase latentSkill
  simpa [sourceLaw, base, score, skill] using
    (lg21_optional_source_all_take_and_report_ae_of_explicit_bestResponses
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
      hbaseVariance htestNoiseVariance hsourceFactor E.actions
      htake hreport htakePublic hreportPublic
      (fun publicBase score hreportAction =>
        (E.report_best_response publicBase).1 score hreportAction)
      (fun latentSkill publicBase hnoTake =>
        (E.take_best_response publicBase).2 latentSkill
          (by simpa [hnoTake])) E.local_entry_stable
      E.recalibrated_report_entry_stable hactualPositiveReporterFibre htestLaw)

end

end LG21TestOptionalPolicies
