import LG21TestOptionalPolicies.ObservedAccessOptionalPositiveMassRefinedEquilibrium
import LG21TestOptionalPolicies.Section4LiteralGaussianSourceBridge
import LG21TestOptionalPolicies.ContinuousObservedAccessActualPBOBridge

/-!
# All-report witness for the optional positive-mass refinement

This module constructs the literal all-take/all-report action profile on the
continuous Gaussian access population.  Its reported value is the source
derived full-profile Gaussian conditional mean.  The no-report branch is
unattained, so the refinement asks for no numerical PBO there.

The two entry-stability fields are discharged only because their respective
entry predicates require a current zero-reporter region or a current
nonreporter who changes to report.  Neither exists for this profile.  This is
an existence result for the stated positive-mass carrier, not a claim about a
stronger candidate-wide equilibrium refinement.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The source-timed all-take/all-report actions paired with the literal
full-profile Gaussian posterior mean on the report branch. -/
def lg21ObservedAccessOptionalAllTakeAllReportActions
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) :
    LG21OptionalSourceTimedActions Base where
  testLaw := fun latentSkill _ => gaussianReal latentSkill S.testNoiseVariance
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  takeDecision := fun _ _ => true
  reportDecision := fun _ _ => true
  reportedPayoff := fun publicBase score =>
    lg21D6GaussianPBOEstimate S (publicBase, score)
  noReportPayoff := fun _ => 0
  continuationPayoff_integrable := by
    intro latentSkill publicBase
    let law := gaussianReal latentSkill S.testNoiseVariance
    let weight := lg21D6PosteriorTestWeight S
    let intercept := S.posteriorBaseMean publicBase -
      weight * S.posteriorBaseMean publicBase
    have hid : Integrable (fun score : ℝ => score) law := by
      exact (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := latentSkill) (v := S.testNoiseVariance) (p := 1)
        (by norm_num)).integrable le_rfl
    have haffine : Integrable (fun score : ℝ =>
        intercept + weight * score) law := by
      simpa [mul_comm] using
        ((integrable_const intercept).add (hid.const_mul weight))
    have hformula : (fun score : ℝ =>
        lg21D6GaussianPBOEstimate S (publicBase, score)) =
        (fun score : ℝ => intercept + weight * score) := by
      funext score
      dsimp [intercept, weight, lg21D6GaussianPBOEstimate]
      ring
    simpa [law, hformula] using haffine

@[simp] theorem lg21ObservedAccessOptionalAllTakeAllReportActions_takeDecision
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) (latentSkill : ℝ) (publicBase : Base) :
    (lg21ObservedAccessOptionalAllTakeAllReportActions S).takeDecision
      latentSkill publicBase = true := rfl

@[simp] theorem lg21ObservedAccessOptionalAllTakeAllReportActions_reportDecision
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) (publicBase : Base) (score : ℝ) :
    (lg21ObservedAccessOptionalAllTakeAllReportActions S).reportDecision
      publicBase score = true := rfl

/-- The literal report event of the all-take/all-report actions is the full
source population. -/
theorem lg21OptionalSourceReportEvent_allTakeAllReport_eq_univ
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (S : LG21GaussianPBOResamplingSource Base) :
    lg21OptionalSourceReportEvent base score skill
      (lg21ObservedAccessOptionalAllTakeAllReportActions S).takeDecision
      (lg21ObservedAccessOptionalAllTakeAllReportActions S).reportDecision = Set.univ := by
  ext omega
  simp [lg21OptionalSourceReportEvent]

/-- The complementary no-report event is literally empty. -/
theorem lg21OptionalSourceNoReportEvent_allTakeAllReport_eq_empty
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (S : LG21GaussianPBOResamplingSource Base) :
    lg21OptionalSourceNoReportEvent base score skill
      (lg21ObservedAccessOptionalAllTakeAllReportActions S).takeDecision
      (lg21ObservedAccessOptionalAllTakeAllReportActions S).reportDecision = ∅ := by
  ext omega
  simp [lg21OptionalSourceNoReportEvent]

/-- The all-report PBO obligation is nonvacuous: its actual action event has
probability one under every source probability law. -/
theorem lg21_optional_allTakeAllReport_reportEvent_positive
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (S : LG21GaussianPBOResamplingSource Base) :
    0 < sourceLaw
      (lg21OptionalSourceReportEvent base score skill
        (lg21ObservedAccessOptionalAllTakeAllReportActions S).takeDecision
        (lg21ObservedAccessOptionalAllTakeAllReportActions S).reportDecision) := by
  rw [lg21OptionalSourceReportEvent_allTakeAllReport_eq_univ]
  rw [IsProbabilityMeasure.measure_univ]
  exact zero_lt_one

/-- With everyone currently taking and reporting, no positive public-base
region can have zero current reporter mass.  This discharges the local-entry
clause of the positive-mass refinement from its literal antecedent. -/
theorem lg21_optional_allTakeAllReport_local_recalibrated_entry_stable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega)))) :
    LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic (fun _ _ => true) (fun _ _ => true) := by
  intro region candidateTake candidateReport candidate hentry
  rcases hentry with ⟨hregion, hregionPositive, hzeroReporter, _⟩
  have hreportEvent :
      lg21OptionalSourceReportEvent base score skill
        (fun _ _ => true) (fun _ _ => true) = Set.univ := by
    ext omega
    simp [lg21OptionalSourceReportEvent]
  have hregionZero : sourceLaw (base ⁻¹' region) = 0 := by
    simpa [hreportEvent] using hzeroReporter
  exact (ne_of_gt hregionPositive) hregionZero

/-- With everyone currently taking and reporting, no agent can satisfy the
literal `changed to report` predicate.  This discharges the refinement's
positive-mass report-entry clause without choosing any null-branch value. -/
theorem lg21_optional_allTakeAllReport_recalibrated_report_entry_stable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega)))) :
    LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
      sourceLaw base score skill hpublic (fun _ _ => true) (fun _ _ => true) := by
  intro candidateTake candidateReport candidate hentry
  rcases hentry with ⟨_, _, _, hchangedPositive, _⟩
  have hchangedEmpty :
      lg21OptionalSourceChangedToReportForActionEvent base score skill
        (fun _ _ => true) (fun _ _ => true) candidateTake candidateReport = ∅ := by
    ext omega
    simp [lg21OptionalSourceChangedToReportForActionEvent]
  rw [hchangedEmpty] at hchangedPositive
  simpa using hchangedPositive

/-- A source-derived full-profile Gaussian posterior supplies a nonvacuous
all-take/all-report witness for the optional positive-mass refinement.  The
reported PBO is the literal conditional mean on the full access population;
the no-report fields are discharged only after proving that their antecedent
event is empty. -/
def lg21ObservedAccessOptionalPositiveMassRefinedEquilibrium_allTakeAllReport_of_fullBaseGaussianFactorization
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
    LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium M haccess testFeature := by
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
  let actions := lg21ObservedAccessOptionalAllTakeAllReportActions S
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
  have hreportEvent :
      lg21OptionalSourceReportEvent base score skill
        actions.takeDecision actions.reportDecision = Set.univ := by
    simpa [actions] using
      (lg21OptionalSourceReportEvent_allTakeAllReport_eq_univ base score skill S)
  have hnoReportEvent :
      lg21OptionalSourceNoReportEvent base score skill
        actions.takeDecision actions.reportDecision = ∅ := by
    simpa [actions] using
      (lg21OptionalSourceNoReportEvent_allTakeAllReport_eq_empty base score skill S)
  have hreportLaw :
      lg21NormalizedRestriction law
        (lg21OptionalSourceReportEvent base score skill
          actions.takeDecision actions.reportDecision) = law := by
    rw [hreportEvent]
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
  refine
    { actions := actions
      takeDecision_measurable := by
        simpa [actions] using
          (measurable_const : Measurable (fun _ :
            (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => true))
      reportDecision_measurable := by
        simpa [actions] using
          (measurable_const : Measurable (fun _ :
            (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => true))
      local_recalibrated_entry_stable := by
        intro region candidateTake candidateReport candidate _hfixedLaw hentry
        exact (lg21_optional_allTakeAllReport_local_recalibrated_entry_stable
          law base score skill hpublic) region candidateTake candidateReport
            candidate hentry
      recalibrated_report_entry_stable := by
        intro candidateTake candidateReport candidate _hfixedLaw hentry
        exact (lg21_optional_allTakeAllReport_recalibrated_report_entry_stable
          law base score skill hpublic) candidateTake candidateReport candidate hentry
      test_law_gaussian := by
        intro publicBase latentSkill
        rfl
      actual_report_integrable := by
        intro hpositive
        rw [hreportLaw]
        exact hskillIntegrable
      actual_report_pbo := by
        intro hpositive
        rw [hreportLaw]
        filter_upwards [hd6Pullback, hcondExp] with student hd6 hmean
        change lg21D6GaussianPBOEstimate S (observation student) =
          law[skill | MeasurableSpace.comap observation inferInstance] student
        rw [hd6, ← hmean]
      actual_noReport_integrable := by
        intro hpositive
        have hpositive' : 0 < law
            (lg21OptionalSourceNoReportEvent base score skill
              actions.takeDecision actions.reportDecision) := by
          simpa [law, base, score, skill] using hpositive
        rw [hnoReportEvent] at hpositive'
        exfalso
        simpa using hpositive'
      actual_noReport_pbo := by
        intro hpositive
        have hpositive' : 0 < law
            (lg21OptionalSourceNoReportEvent base score skill
              actions.takeDecision actions.reportDecision) := by
          simpa [law, base, score, skill] using hpositive
        rw [hnoReportEvent] at hpositive'
        exfalso
        simpa using hpositive' }

/-- Existence of the preceding witness for the literal finite-profile Gaussian
source.  The only inputs are the source's positive prior and noise variances;
the full non-test conditional Gaussian factorization is constructed by the
existing finite-coordinate proof. -/
theorem lg21ContinuousGaussianAccessPopulation_exists_optionalPositiveMassRefined_allTakeAllReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium M haccess testFeature,
      (∀ latentSkill publicBase,
        E.actions.takeDecision latentSkill publicBase = true) ∧
      (∀ publicBase score,
        E.actions.reportDecision publicBase score = true) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        M testFeature hpriorVariance hnonTestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hfullBaseFactorization⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let E :=
    lg21ObservedAccessOptionalPositiveMassRefinedEquilibrium_allTakeAllReport_of_fullBaseGaussianFactorization
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  refine ⟨E, ?_, ?_⟩
  · intro latentSkill publicBase
    rfl
  · intro publicBase score
    rfl

/-- A chosen instance of the fully source-derived witness.  The accompanying
existence theorem exposes its all-take/all-report behavior, while this
definition is convenient for downstream constructions that require a value. -/
noncomputable def lg21ContinuousGaussianAccessPopulation_optionalPositiveMassRefined_allTakeAllReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium M haccess testFeature :=
  Classical.choose
    (lg21ContinuousGaussianAccessPopulation_exists_optionalPositiveMassRefined_allTakeAllReport
      M haccess testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance)

end

end LG21TestOptionalPolicies
