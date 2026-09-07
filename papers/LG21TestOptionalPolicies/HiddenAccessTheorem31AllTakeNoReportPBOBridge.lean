import LG21TestOptionalPolicies.HiddenAccessTheorem31PublicSelectionPosterior

/-!
# All-taking no-report PBO bridge for LG21 Theorem 3.1

Once the source pre-score action takes almost everywhere, the incumbent's
literal `X = 0` population is the same attained raw population as the
all-take profile with its actual public report action.  This module makes that
identification before transporting the incumbent PBO.  The resulting equality
is only on the attained base marginal; later callers may transport it further
only through an explicit absolute-continuity argument.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- If the literal access/no-take event is null, the incumbent `X = 0` event
equals the raw all-take candidate event with the same public report action,
almost everywhere under the source population. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalNoReportEvent_ae_eq_allTakeRawCandidate_of_allTake_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21HiddenAccessOptionalNoReportEvent testFeature E.takeDecision E.reportDecision =ᵐ[
      lg21ContinuousGaussianPopulationLaw M]
      lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) E.reportDecision := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let actualNoReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let allTakeNoReport := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) E.reportDecision
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  filter_upwards [hactiveNull] with student hnot
  rcases student with ⟨access, primitive⟩
  cases access with
  | false =>
      apply propext
      change
        (if false = true then
          if lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = true then
            lg21HiddenAccessStudentReport testFeature E.reportDecision primitive
          else false
        else false) = false ↔
        (if false = true then
          if lg21HiddenAccessStudentTake testFeature
              (lg21HiddenAccessAllTake testFeature) primitive = true then
            lg21HiddenAccessStudentReport testFeature E.reportDecision primitive
          else false
        else false) = false
      simp
  | true =>
      by_cases htake :
          lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = true
      · apply propext
        have hallTake : lg21HiddenAccessStudentTake testFeature
            (lg21HiddenAccessAllTake testFeature) primitive = true := by
          simp [lg21HiddenAccessStudentTake, lg21HiddenAccessAllTake]
        change
          (if true = true then
            if lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = true then
              lg21HiddenAccessStudentReport testFeature E.reportDecision primitive
            else false
          else false) = false ↔
          (if true = true then
            if lg21HiddenAccessStudentTake testFeature
                (lg21HiddenAccessAllTake testFeature) primitive = true then
              lg21HiddenAccessStudentReport testFeature E.reportDecision primitive
            else false
          else false) = false
        simp [htake, hallTake]
      · have htakeFalse :
          lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = false := by
            cases htakeAction :
                lg21HiddenAccessStudentTake testFeature E.takeDecision primitive <;>
              simp_all
        exact (hnot (by
          simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
            htakeFalse])).elim

/-- The normalized actual no-report law equals the raw all-take candidate law
when the source pre-score no-take action is null. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalNoReportLaw_eq_allTakeRawCandidate_of_allTake_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21HiddenAccessOptionalNoReportLaw M testFeature
      E.takeDecision E.reportDecision =
      lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature) E.reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let actualNoReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let allTakeNoReport := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) E.reportDecision
  have hEvent : actualNoReport =ᵐ[rawLaw] allTakeNoReport := by
    simpa [rawLaw, actualNoReport, allTakeNoReport] using
      E.optionalNoReportEvent_ae_eq_allTakeRawCandidate_of_allTake_ae
        hactiveNoTakeZero
  simpa [lg21HiddenAccessOptionalNoReportLaw, rawLaw,
    actualNoReport, allTakeNoReport] using
    (lg21_optional_normalizedRestriction_congr_ae rawLaw hEvent)

/-- The actual no-report branch is positive under all-taking-a.e. because the
literal no-access population remains in the branch. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalNoReportEvent_positive_of_allTake_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature
        E.takeDecision E.reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let actualNoReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let allTakeNoReport := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) E.reportDecision
  have hEvent : actualNoReport =ᵐ[rawLaw] allTakeNoReport := by
    simpa [rawLaw, actualNoReport, allTakeNoReport] using
      E.optionalNoReportEvent_ae_eq_allTakeRawCandidate_of_allTake_ae
        hactiveNoTakeZero
  rw [show lg21ContinuousGaussianPopulationLaw M actualNoReport = rawLaw actualNoReport by rfl,
    measure_congr hEvent]
  exact lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess M testFeature
    (lg21HiddenAccessAllTake testFeature) E.reportDecision hnoAccess

/-- Mapping a source law to its `(public base, latent skill)` coordinates
does not change the regular conditional skill law given the base, on the
attained base marginal. -/
theorem lg21_condDistrib_skill_base_eq_baseSkillMap_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) [IsFiniteMeasure law]
    (base : Omega → Base) (skill : Omega → ℝ)
    (hbase : Measurable base) (hskill : Measurable skill) :
    condDistrib skill base law =ᵐ[law.map base]
      condDistrib Prod.snd Prod.fst (law.map fun omega => (base omega, skill omega)) := by
  have hmap := condDistrib_map (ν := law) (X := Prod.fst) (Y := Prod.snd)
    (f := fun omega => (base omega, skill omega))
    measurable_fst.aemeasurable measurable_snd.aemeasurable
    (hbase.prodMk hskill).aemeasurable
  simpa [Function.comp_def] using hmap.symm

/-- The incumbent no-report payoff is the conditional skill mean under the
same raw all-take `(base, skill)` law that is obtained by retaining its actual
public report action.  This is an attained-law statement, so it does not
choose a value at a null base fibre. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.noReportPayoff_eq_allTakeRawCandidate_condDistribMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    ∀ᵐ publicBase ∂
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) E.reportDecision).map Prod.fst,
      E.noReportPayoff publicBase =
        lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
          E.reportDecision publicBase := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let actualLaw := lg21HiddenAccessOptionalNoReportLaw M testFeature
    E.takeDecision E.reportDecision
  let candidateNoReport := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) E.reportDecision
  let candidateLaw := lg21NormalizedRestriction rawLaw candidateNoReport
  let base : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let skill : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
    lg21ContinuousPopulationSkill
  let baseSkill : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student => (base student, skill student)
  let actionLaw := candidateLaw.map baseSkill
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hbaseSkill : Measurable baseSkill := hbase.prodMk hskill
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hactualPositive : 0 < rawLaw
      (lg21HiddenAccessOptionalNoReportEvent testFeature
        E.takeDecision E.reportDecision) := by
    simpa [rawLaw] using
      E.optionalNoReportEvent_positive_of_allTake_ae
        hnoAccess hactiveNoTakeZero
  letI : IsProbabilityMeasure actualLaw := by
    simpa [actualLaw, rawLaw] using
      (lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalNoReportEvent testFeature
          E.takeDecision E.reportDecision)
        (ne_of_gt hactualPositive) (measure_ne_top _ _))
  letI : IsFiniteMeasure actualLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure candidateLaw := by
    simpa [candidateLaw, rawLaw, candidateNoReport] using
      (lg21NormalizedRestriction_isProbability rawLaw candidateNoReport
        (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
          M testFeature (lg21HiddenAccessAllTake testFeature) E.reportDecision hnoAccess))
        (measure_ne_top _ _))
  letI : IsFiniteMeasure candidateLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure actionLaw := by
    simpa [actionLaw] using Measure.isProbabilityMeasure_map hbaseSkill.aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  have hactualLaw : actualLaw = candidateLaw := by
    simpa [actualLaw, candidateLaw, rawLaw, candidateNoReport] using
      E.optionalNoReportLaw_eq_allTakeRawCandidate_of_allTake_ae
        hactiveNoTakeZero
  have hsourcePBO : (fun student => E.noReportPayoff (base student)) =ᵐ[actualLaw]
      actualLaw[skill | MeasurableSpace.comap base inferInstance] := by
    simpa [LG21HiddenAccessActualNoReportPBO, rawLaw, actualLaw, base, skill] using
      E.noReport_pbo hactualPositive
  have hcondExp : actualLaw[skill | MeasurableSpace.comap base inferInstance] =ᵐ[
      actualLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill base actualLaw (base student) := by
    simpa [rawLaw, actualLaw, base, skill] using
      (lg21HiddenAccessOptional_noReport_condExp_eq_actual_condDistrib_ae
        M testFeature E.takeDecision E.reportDecision hactualPositive)
  have hPBOActual : (fun student => E.noReportPayoff (base student)) =ᵐ[actualLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill base actualLaw (base student) :=
    hsourcePBO.trans hcondExp
  have hPBOCandidate : (fun student => E.noReportPayoff (base student)) =ᵐ[candidateLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill base candidateLaw (base student) := by
    simpa only [hactualLaw] using hPBOActual
  have hcondMap : condDistrib skill base candidateLaw =ᵐ[candidateLaw.map base]
      condDistrib Prod.snd Prod.fst actionLaw := by
    simpa [actionLaw, baseSkill] using
      (lg21_condDistrib_skill_base_eq_baseSkillMap_ae
        candidateLaw base skill hbase hskill)
  have hcondMapPullback : ∀ᵐ student ∂candidateLaw,
      condDistrib skill base candidateLaw (base student) =
        condDistrib Prod.snd Prod.fst actionLaw (base student) := by
    exact ae_of_ae_map hbase.aemeasurable hcondMap
  have hPBOAction : (fun student => E.noReportPayoff (base student)) =ᵐ[candidateLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib Prod.snd Prod.fst actionLaw (base student) := by
    filter_upwards [hPBOCandidate, hcondMapPullback] with student hPBO hcond
    rw [hPBO, hcond]
  have hbaseMarginal : candidateLaw.map base = actionLaw.map Prod.fst := by
    calc
      candidateLaw.map base = (candidateLaw.map baseSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hbaseSkill]
        rfl
      _ = actionLaw.map Prod.fst := by rfl
  have hmeanMeasurable : Measurable (fun publicBase =>
      ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst actionLaw publicBase) := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  have hPBOBaseMean : ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
      E.noReportPayoff publicBase =
        ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst actionLaw publicBase := by
    rw [← hbaseMarginal]
    rw [MeasureTheory.ae_map_iff hbase.aemeasurable
      (measurableSet_eq_fun E.noReportPayoff_measurable hmeanMeasurable)]
    simpa [actionLaw, baseSkill, base, skill] using hPBOAction
  filter_upwards [hPBOBaseMean] with publicBase hPBO
  rw [hPBO]
  symm
  simpa [actionLaw, candidateLaw, candidateNoReport, rawLaw, baseSkill] using
    (lg21HiddenAccessAllTake_candidateNoReportValue_eq_condDistribMean
      M hnoAccess testFeature E.reportDecision publicBase)

/-- The attained public-base marginal of any all-take no-report branch is a
positive reweighting of the common source base law.  This exposes the support
fact needed to transport PBO identities to another public action branch. -/
theorem lg21HiddenAccessAllTake_arbitraryNoReport_baseMarginal_eq_publicScoreWeightedBase
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    letI : IsMarkovKernel joint := gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let selection := lg21HiddenAccessPublicNoReportSelection testFeature candidateReport
    let accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection
    let fibreMass := lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel (M.accessLaw {false}) (M.accessLaw {true})
    let actionLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport
    letI : IsProbabilityMeasure actionLaw :=
      lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    actionLaw.map Prod.fst =
      (lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature) candidateReport))⁻¹ •
        baseLaw.withDensity fibreMass := by
  intro joint noAccessKernel selection accessSelectedSkillKernel fibreMass actionLaw
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection)
  have hselection : MeasurableSet selection := by
    simpa [selection] using
      (lg21HiddenAccessPublicNoReportSelection_measurable testFeature
        candidateReport hcandidateReport)
  have hfibreMass : Measurable fibreMass := by
    simpa [fibreMass, accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreRawFibreMass_measurable
        joint (M.accessLaw {false}) (M.accessLaw {true}) selection hselection)
  let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
    noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel, fibreMass] using
      (lg21HiddenAccessScoreNormalizedKernel_isMarkov
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccess hnoAccessFinite haccessFinite hfibreMass)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) candidateReport
  let weightedBase := (rawLaw noReportEvent)⁻¹ • baseLaw.withDensity fibreMass
  let rawKernel := lg21HiddenAccessScoreRawKernel
    noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true})
  letI : IsProbabilityMeasure actionLaw := by
    simpa [actionLaw] using
      (lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport)
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  have hrawLaw : actionLaw = (rawLaw noReportEvent)⁻¹ •
      (baseLaw ⊗ₘ rawKernel) := by
    simpa [actionLaw, rawLaw, noReportEvent, rawKernel,
      noAccessKernel, accessSelectedSkillKernel, selection, joint] using
      (lg21HiddenAccessAllTake_arbitraryNoReportBaseSkillLaw_eq_normalized_publicScoreRawKernel
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hsourceFactor candidateReport hcandidateReport)
  have hweighted : baseLaw.withDensity fibreMass ⊗ₘ normalizedKernel =
      baseLaw ⊗ₘ rawKernel := by
    simpa [normalizedKernel, rawKernel, fibreMass] using
      (lg21HiddenAccessScoreWeightedBase_compProd_normalizedKernel
        baseLaw noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccess hnoAccessFinite haccessFinite hfibreMass)
  have hfactor : actionLaw = weightedBase ⊗ₘ normalizedKernel := by
    calc
      actionLaw = (rawLaw noReportEvent)⁻¹ •
          (baseLaw ⊗ₘ rawKernel) := hrawLaw
      _ = (rawLaw noReportEvent)⁻¹ •
          (baseLaw.withDensity fibreMass ⊗ₘ normalizedKernel) := by rw [hweighted]
      _ = weightedBase ⊗ₘ normalizedKernel := by
        rw [Measure.compProd_smul_left]
  calc
    actionLaw.map Prod.fst = (weightedBase ⊗ₘ normalizedKernel).map Prod.fst := by
      rw [hfactor]
    _ = weightedBase := Measure.fst_compProd _ _

/-- Positive no-access mass gives every all-taking literal no-report base
branch full source-base support.  The statement is independent of the shape
or name of the public report rule. -/
theorem lg21HiddenAccessAllTake_baseLaw_absolutelyContinuous_arbitraryNoReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    baseLaw ≪
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport).map Prod.fst := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  let noAccessKernel := joint.map Prod.snd
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  let selection := lg21HiddenAccessPublicNoReportSelection testFeature candidateReport
  let accessSelectedSkillKernel :=
    lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection)
  let fibreMass := lg21HiddenAccessScoreRawFibreMass
    accessSelectedSkillKernel (M.accessLaw {false}) (M.accessLaw {true})
  let actionLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
    (lg21HiddenAccessAllTake testFeature) candidateReport
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) candidateReport
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hselection : MeasurableSet selection := by
    simpa [selection] using
      (lg21HiddenAccessPublicNoReportSelection_measurable testFeature
        candidateReport hcandidateReport)
  have hfibreMass : Measurable fibreMass := by
    simpa [fibreMass, accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreRawFibreMass_measurable
        joint (M.accessLaw {false}) (M.accessLaw {true}) selection hselection)
  have hfibrePositive : ∀ publicBase, 0 < fibreMass publicBase := by
    intro publicBase
    change 0 < M.accessLaw {false} + M.accessLaw {true} *
      accessSelectedSkillKernel publicBase Set.univ
    exact lt_of_lt_of_le hnoAccess (le_add_right le_rfl)
  have hbaseDensity : baseLaw ≪ baseLaw.withDensity fibreMass :=
    withDensity_absolutelyContinuous' hfibreMass.aemeasurable
      (Filter.Eventually.of_forall fun publicBase =>
        ne_of_gt (hfibrePositive publicBase))
  have hfactor : actionLaw.map Prod.fst =
      (rawLaw noReportEvent)⁻¹ • baseLaw.withDensity fibreMass := by
    simpa [actionLaw, rawLaw, noReportEvent, fibreMass,
      accessSelectedSkillKernel, selection, noAccessKernel, joint] using
      (lg21HiddenAccessAllTake_arbitraryNoReport_baseMarginal_eq_publicScoreWeightedBase
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hsourceFactor candidateReport hcandidateReport
        hnoAccessFinite haccessFinite)
  change baseLaw ≪ actionLaw.map Prod.fst
  rw [hfactor]
  exact hbaseDensity.smul_right
    (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw noReportEvent))

end

end LG21TestOptionalPolicies
