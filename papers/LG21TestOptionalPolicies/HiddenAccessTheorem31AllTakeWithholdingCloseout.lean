import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeReporterPBOBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate

/-!
# All-taking withholding closeout for LG21 Theorem 3.1

This module closes the literal all-taking branch of the hidden-access
optional-reporting argument.  It works only with attained action laws: the
no-report PBO is identified on the positive no-access population, and the
reported PBO is identified on the actual reporter population.  No value is
assigned to a null public history.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- If access students take almost everywhere and access withholding has zero
literal mass, the actual no-report event is the literal no-access event almost
everywhere under the raw population. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalNoReportEvent_ae_eq_noAccess_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0) :
    lg21HiddenAccessOptionalNoReportEvent testFeature E.takeDecision E.reportDecision =ᵐ[
      lg21ContinuousGaussianPopulationLaw M]
      lg21HiddenAccessNoAccessEvent := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let accessNoReport := lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  have haccessNoReportNull : ∀ᵐ student ∂rawLaw, student ∉ accessNoReport := by
    rw [ae_iff]
    simpa [rawLaw, accessNoReport] using haccessNoReportZero
  have hdecomposition : noReport =ᵐ[rawLaw]
      Set.union noAccess accessNoReport := by
    filter_upwards [hactiveNull] with student hnot
    rcases student with ⟨access, primitive⟩
    cases access with
    | false =>
        apply propext
        change
          lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
              E.reportDecision (false, primitive) = false ↔
            (false = false ∨ false = true ∧
              lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false)
        simp [lg21HiddenAccessOptionalObservedAction]
    | true =>
        by_cases htake :
            lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = true
        · apply propext
          change
            lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
                E.reportDecision (true, primitive) = false ↔
              (true = false ∨ true = true ∧
                lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false)
          simp [lg21HiddenAccessOptionalObservedAction, htake]
        · have htakeFalse :
            lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = false := by
              cases htakeAction :
                  lg21HiddenAccessStudentTake testFeature E.takeDecision primitive <;>
                simp_all
          exact (hnot (by
            simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
              htakeFalse])).elim
  have hunion : Set.union noAccess accessNoReport =ᵐ[rawLaw] noAccess := by
    filter_upwards [haccessNoReportNull] with student hnot
    apply propext
    constructor
    · intro hmember
      rcases hmember with hmember | hmember
      · exact hmember
      · exact (hnot hmember).elim
    · intro hmember
      exact Or.inl hmember
  simpa [rawLaw, noReport, noAccess] using hdecomposition.trans hunion

/-- Under the same hypotheses, the normalized actual `X = 0` law is exactly
the normalized no-access source law.  Positivity is supplied by the literal
no-access population, so this does not invoke an off-path conditional law. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalNoReportLaw_eq_noAccessLaw_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0) :
    lg21HiddenAccessOptionalNoReportLaw M testFeature
      E.takeDecision E.reportDecision = lg21HiddenAccessNoAccessLaw M := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  have hEvent : noReport =ᵐ[rawLaw] noAccess := by
    simpa [rawLaw, noReport, noAccess] using
      E.optionalNoReportEvent_ae_eq_noAccess_of_allTake_allReport
        hactiveNoTakeZero haccessNoReportZero
  simpa [lg21HiddenAccessOptionalNoReportLaw, lg21HiddenAccessNoAccessLaw,
    rawLaw, noReport, noAccess] using
    (lg21_optional_normalizedRestriction_congr_ae rawLaw hEvent)

/-- The actual `X = 0` branch remains positive if it is only the literal
no-access population modulo null action events. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalNoReportEvent_positive_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature
        E.takeDecision E.reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  have hnoAccessPositive : 0 < rawLaw noAccess := by
    rw [show noAccess = ({false} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [noAccess, lg21HiddenAccessNoAccessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa using hnoAccess
  have hEvent : noReport =ᵐ[rawLaw] noAccess := by
    simpa [rawLaw, noReport, noAccess] using
      E.optionalNoReportEvent_ae_eq_noAccess_of_allTake_allReport
        hactiveNoTakeZero haccessNoReportZero
  rw [show lg21ContinuousGaussianPopulationLaw M noReport = rawLaw noReport by rfl,
    measure_congr hEvent]
  exact hnoAccessPositive

/-- When the attained no-report branch contains only no-access students, its
literal PBO is the Gaussian conditional mean given the non-test base.  This
uses the source PBO only on that positive branch. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.noReportPayoff_eq_baseMean_ae_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0)
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
    let noAccessLaw := lg21HiddenAccessNoAccessLaw M
    let base : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    ∀ᵐ student ∂noAccessLaw,
      E.noReportPayoff (base student) = baseMean (base student) := by
  intro noAccessLaw base
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReportLaw := lg21HiddenAccessOptionalNoReportLaw M testFeature
    E.takeDecision E.reportDecision
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let joint := gaussianSignalJointKernel baseMean hbaseMean priorVariance
    (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hnoReportPositive : 0 < rawLaw
      (lg21HiddenAccessOptionalNoReportEvent testFeature
        E.takeDecision E.reportDecision) := by
    simpa [rawLaw] using
      E.optionalNoReportEvent_positive_of_allTake_allReport
        hnoAccess hactiveNoTakeZero haccessNoReportZero
  letI : IsProbabilityMeasure noReportLaw := by
    simpa [noReportLaw] using
      (lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalNoReportEvent testFeature
          E.takeDecision E.reportDecision)
        (ne_of_gt hnoReportPositive) (measure_ne_top _ _))
  letI : IsFiniteMeasure noReportLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure noAccessLaw := by
    simpa [noAccessLaw] using lg21HiddenAccessNoAccessLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure noAccessLaw := ⟨by simp⟩
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hnoReportLaw : noReportLaw = noAccessLaw := by
    simpa [noReportLaw, noAccessLaw] using
      E.optionalNoReportLaw_eq_noAccessLaw_of_allTake_allReport
        hnoAccess hactiveNoTakeZero haccessNoReportZero
  have hsourcePBO : (fun student => E.noReportPayoff (base student)) =ᵐ[noReportLaw]
      noReportLaw[skill | MeasurableSpace.comap base inferInstance] := by
    simpa [LG21HiddenAccessActualNoReportPBO, rawLaw, noReportLaw, base, skill] using
      E.noReport_pbo hnoReportPositive
  have hcondExp : noReportLaw[skill | MeasurableSpace.comap base inferInstance] =ᵐ[
      noReportLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill base noReportLaw (base student) := by
    simpa [rawLaw, noReportLaw, base, skill] using
      (lg21HiddenAccessOptional_noReport_condExp_eq_actual_condDistrib_ae
        M testFeature E.takeDecision E.reportDecision hnoReportPositive)
  have hPBOCond : (fun student => E.noReportPayoff (base student)) =ᵐ[noAccessLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill base noAccessLaw (base student) := by
    simpa only [hnoReportLaw] using hsourcePBO.trans hcondExp
  have hrawSourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ joint := by
    calc
      (lg21ContinuousGaussianPopulationLaw M).map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) :=
        lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
          M E.access_positive testFeature
      _ = baseLaw ⊗ₘ joint := by
        simpa [joint, lg21HiddenAccessBaseScoreSkillObservation] using hsourceFactor
  have hjointSkill : joint.map Prod.snd = skillKernel := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal]
    rw [show skillKernel publicBase =
        gaussianReal (baseMean publicBase) priorVariance.toNNReal by
      exact gaussianLocationKernel_apply
        baseMean hbaseMean priorVariance.toNNReal publicBase]
  have hfullBaseLatent :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ skillKernel := by
    calc
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ joint.map Prod.snd := by
            simpa [joint] using
              (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
                M E.access_positive testFeature baseLaw baseMean hbaseMean
                priorVariance (M.noiseVariance testFeature : ℝ) (by
                  simpa [joint] using hrawSourceFactor))
      _ = baseLaw ⊗ₘ skillKernel := by
            rw [hjointSkill]
  have hnoAccessPair : noAccessLaw.map (fun student =>
      (base student, skill student)) = baseLaw ⊗ₘ skillKernel := by
    calc
      noAccessLaw.map (fun student => (base student, skill student)) =
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
            simpa [noAccessLaw, base, skill] using
              (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature)
      _ = baseLaw ⊗ₘ skillKernel := hfullBaseLatent
  have hbaseMarginal : noAccessLaw.map base = baseLaw := by
    calc
      noAccessLaw.map base =
          (noAccessLaw.map (fun student => (base student, skill student))).map Prod.fst := by
            rw [Measure.map_map measurable_fst (hbase.prodMk hskill)]
            rfl
      _ = (baseLaw ⊗ₘ skillKernel).map Prod.fst := by rw [hnoAccessPair]
      _ = baseLaw := Measure.fst_compProd _ _
  have hjoint : noAccessLaw.map (fun student => (base student, skill student)) =
      noAccessLaw.map base ⊗ₘ skillKernel := by
    rw [hnoAccessPair, hbaseMarginal]
  have hcondDistrib : condDistrib skill base noAccessLaw =ᵐ[
      noAccessLaw.map base] skillKernel := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hbase hskill hjoint
  have hcondPullback : ∀ᵐ student ∂noAccessLaw,
      condDistrib skill base noAccessLaw (base student) = skillKernel (base student) := by
    exact ae_of_ae_map hbase.aemeasurable hcondDistrib
  filter_upwards [hPBOCond, hcondPullback] with student hPBO hcondAt
  rw [hPBO, hcondAt]
  simpa [skillKernel] using
    (lg21_gaussianLocationKernel_skill_mean
      baseMean hbaseMean priorVariance.toNNReal (base student))

/-- The no-access and access populations have the same public-base marginal.
With measurable source payoffs, the attained no-report PBO identity therefore
holds almost everywhere on that common base law as well. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.noReportPayoff_eq_baseMean_ae_on_baseLaw_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0)
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
    ∀ᵐ publicBase ∂baseLaw,
      E.noReportPayoff publicBase = baseMean publicBase := by
  let noAccessLaw := lg21HiddenAccessNoAccessLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let joint := gaussianSignalJointKernel baseMean hbaseMean priorVariance
    (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hnoAccessPBO : ∀ᵐ student ∂noAccessLaw,
      E.noReportPayoff (base student) = baseMean (base student) := by
    simpa [noAccessLaw, base] using
      E.noReportPayoff_eq_baseMean_ae_of_allTake_allReport
        hnoAccess hactiveNoTakeZero haccessNoReportZero
        baseLaw baseMean hbaseMean priorVariance hpriorVariance hnoiseVariance
        hsourceFactor
  have hrawSourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ joint := by
    calc
      (lg21ContinuousGaussianPopulationLaw M).map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) :=
        lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
          M E.access_positive testFeature
      _ = baseLaw ⊗ₘ joint := by
        simpa [joint, lg21HiddenAccessBaseScoreSkillObservation] using hsourceFactor
  have hjointSkill : joint.map Prod.snd = skillKernel := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal]
    rw [show skillKernel publicBase =
        gaussianReal (baseMean publicBase) priorVariance.toNNReal by
      exact gaussianLocationKernel_apply
        baseMean hbaseMean priorVariance.toNNReal publicBase]
  have hfullBaseLatent :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ skillKernel := by
    calc
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ joint.map Prod.snd := by
            simpa [joint] using
              (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
                M E.access_positive testFeature baseLaw baseMean hbaseMean
                priorVariance (M.noiseVariance testFeature : ℝ) (by
                  simpa [joint] using hrawSourceFactor))
      _ = baseLaw ⊗ₘ skillKernel := by rw [hjointSkill]
  have hnoAccessPair : noAccessLaw.map (fun student =>
      (base student, skill student)) = baseLaw ⊗ₘ skillKernel := by
    calc
      noAccessLaw.map (fun student => (base student, skill student)) =
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
            simpa [noAccessLaw, base, skill] using
              (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature)
      _ = baseLaw ⊗ₘ skillKernel := hfullBaseLatent
  have hbaseMarginal : noAccessLaw.map base = baseLaw := by
    calc
      noAccessLaw.map base =
          (noAccessLaw.map (fun student => (base student, skill student))).map Prod.fst := by
            rw [Measure.map_map measurable_fst (hbase.prodMk hskill)]
            rfl
      _ = (baseLaw ⊗ₘ skillKernel).map Prod.fst := by rw [hnoAccessPair]
      _ = baseLaw := Measure.fst_compProd _ _
  rw [← hbaseMarginal]
  rw [MeasureTheory.ae_map_iff hbase.aemeasurable
    (measurableSet_eq_fun E.noReportPayoff_measurable hbaseMean)]
  simpa [Function.comp_def] using hnoAccessPBO

/-- With no literal non-takers or access-withholders, the actual reporter
event agrees almost everywhere with the literal positive-access event. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalReportEvent_ae_eq_access_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0) :
    lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision =ᵐ[
      lg21ContinuousGaussianPopulationLaw M]
      {student | student.1 = true} := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let accessNoReport := lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  have haccessNoReportNull : ∀ᵐ student ∂rawLaw, student ∉ accessNoReport := by
    rw [ae_iff]
    simpa [rawLaw, accessNoReport] using haccessNoReportZero
  filter_upwards [hactiveNull, haccessNoReportNull] with student hnotTake hnotReport
  rcases student with ⟨access, primitive⟩
  apply propext
  change lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
    E.reportDecision (access, primitive) = true ↔ access = true
  cases access with
  | false =>
      simp [lg21HiddenAccessOptionalObservedAction]
  | true =>
      by_cases htake :
          lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = true
      · have hreport :
            lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = true := by
            cases haction :
                lg21HiddenAccessStudentReport testFeature E.reportDecision primitive with
            | false =>
                exact (hnotReport (by
                  change true = true ∧
                    lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false
                  exact ⟨rfl, haction⟩)).elim
            | true => rfl
        simp [lg21HiddenAccessOptionalObservedAction, htake, hreport]
      · have htakeFalse :
            lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = false := by
            cases haction :
                lg21HiddenAccessStudentTake testFeature E.takeDecision primitive <;>
              simp_all
        exact (hnotTake (by
          change true = true ∧
            lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = false
          exact ⟨rfl, htakeFalse⟩)).elim

/-- Under the same null-event hypotheses, the actual reporter law is exactly
the positive-access population law. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalReporterLaw_eq_accessLaw_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0) :
    lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) =
      lg21ContinuousGaussianAccessPopulationLaw M := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  have hEvent : reportEvent =ᵐ[rawLaw] accessEvent := by
    simpa [rawLaw, reportEvent, accessEvent] using
      E.optionalReportEvent_ae_eq_access_of_allTake_allReport
        hactiveNoTakeZero haccessNoReportZero
  simpa [rawLaw, reportEvent, accessEvent,
    lg21ContinuousGaussianAccessPopulationLaw, lg21ContinuousPopulationAccess] using
    (lg21_optional_normalizedRestriction_congr_ae rawLaw hEvent)

/-- The reporter event has positive raw mass whenever it agrees almost
everywhere with the literal positive-access event. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.optionalReportEvent_positive_of_allTake_allReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  have haccessPositive : 0 < rawLaw accessEvent := by
    rw [show accessEvent = ({true} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [accessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa [rawLaw] using E.access_positive
  have hEvent : reportEvent =ᵐ[rawLaw] accessEvent := by
    simpa [rawLaw, reportEvent, accessEvent] using
      E.optionalReportEvent_ae_eq_access_of_allTake_allReport
        hactiveNoTakeZero haccessNoReportZero
  rw [show lg21ContinuousGaussianPopulationLaw M reportEvent = rawLaw reportEvent by rfl,
    measure_congr hEvent]
  exact haccessPositive

/-- A nondegenerate Gaussian score law cannot almost surely make the raw
posterior mean at least its value at the conditional score mean: its strict
lower score tail has positive mass. -/
private theorem lg21_not_ae_baseMean_le_rawGaussianPosterior
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) :
    ¬ ∀ᵐ score ∂gaussianLocationKernel baseMean hbaseMean
        (priorVariance + noiseVariance).toNNReal publicBase,
      baseMean publicBase ≤ ∫ latentSkill, latentSkill ∂
        gaussianSignalPosteriorBaseKernel baseMean hbaseMean
          priorVariance noiseVariance (publicBase, score) := by
  let scoreLaw := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + noiseVariance).toNNReal publicBase
  let posteriorMean : ℝ -> ℝ := fun score =>
    ∫ latentSkill, latentSkill ∂
      gaussianSignalPosteriorBaseKernel baseMean hbaseMean
        priorVariance noiseVariance (publicBase, score)
  have hscoreVariance : 0 < priorVariance + noiseVariance := by
    linarith
  have hscoreVarianceNN : (priorVariance + noiseVariance).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hscoreVariance)
  have htailPositive : 0 < scoreLaw (Set.Iio (baseMean publicBase)) := by
    rw [show scoreLaw = gaussianReal (baseMean publicBase)
        (priorVariance + noiseVariance).toNNReal by
      exact gaussianLocationKernel_apply baseMean hbaseMean
        (priorVariance + noiseVariance).toNNReal publicBase]
    exact lg21_gaussianReal_Iio_pos (baseMean publicBase) (baseMean publicBase)
      hscoreVarianceNN
  have hmeanAtMean : posteriorMean (baseMean publicBase) = baseMean publicBase := by
    rw [show posteriorMean (baseMean publicBase) =
        ∫ latentSkill, latentSkill ∂
          gaussianSignalPosteriorBaseKernel baseMean hbaseMean
            priorVariance noiseVariance (publicBase, baseMean publicBase) by rfl,
      gaussianSignalPosteriorBaseKernel_integral_id]
    have hden : priorVariance + noiseVariance ≠ 0 := ne_of_gt hscoreVariance
    field_simp [gaussianSignalWeight, gaussianSignalPriorWeight, hden]
  have hstrict : StrictMono posteriorMean := by
    simpa [posteriorMean] using
      (strictMono_gaussianSignalPosteriorBaseKernel_integral_id
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance publicBase)
  intro hAE
  have hbadNull : scoreLaw {score | ¬ baseMean publicBase ≤ posteriorMean score} = 0 := by
    rw [← ae_iff]
    simpa [scoreLaw, posteriorMean] using hAE
  have htailSubset : Set.Iio (baseMean publicBase) ⊆
      {score | ¬ baseMean publicBase ≤ posteriorMean score} := by
    intro score hscore
    exact not_le_of_gt (by
      rw [← hmeanAtMean]
      exact hstrict hscore)
  have htailZero : scoreLaw (Set.Iio (baseMean publicBase)) = 0 :=
    measure_mono_null htailSubset hbadNull
  exact (ne_of_gt htailPositive) htailZero

/-- The literal access law has the unselected Gaussian `(base, score)`
factorization supplied by the full source factorization. -/
private theorem lg21_hiddenAccess_accessBaseScoreLaw_eq_gaussianLocation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
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
    lg21HiddenAccessAccessBaseScoreLaw M testFeature =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal := by
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, score student)
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
  let posteriorKernel := gaussianSignalPosteriorBaseKernel baseMean hbaseMean
    priorVariance (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
  letI : IsMarkovKernel posteriorKernel := by
    simpa [posteriorKernel] using
      (gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
  have hbase : Measurable base :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable score :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hskill : Measurable skill := measurable_fst.comp measurable_snd
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hrawObservation : Measurable rawObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hobservationSkill : Measurable observationSkill := hbaseScore.prodMk hskill
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
  calc
    lg21HiddenAccessAccessBaseScoreLaw M testFeature = accessLaw.map baseScore := by rfl
    _ = (accessLaw.map observationSkill).map Prod.fst := by
      rw [Measure.map_map measurable_fst hobservationSkill]
      rfl
    _ = ((baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel).map Prod.fst := by
      rw [hrawFactor]
    _ = baseLaw ⊗ₘ scoreKernel := Measure.fst_compProd _ _
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal := by rfl

/-- In the literal hidden-access model, an a.e. all-taking profile must leave
a positive literal access-withholding population.  The proof uses the actual
positive no-access branch to identify the attained no-report PBO, and the
actual reporter branch to identify the reported PBO; it never completes a
null public history. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.accessNoReportEvent_positive_of_allTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hnoAccess : 0 < M.accessLaw {false})
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
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
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) := by
  by_contra hnotPositive
  have hzero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0 :=
    bot_unique (le_of_not_gt hnotPositive)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let reporterLaw := lg21NormalizedRestriction rawLaw
    (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (lg21HiddenAccessStudentBase testFeature student.2,
      lg21HiddenAccessStudentScore testFeature student.2)
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  let posteriorKernel := gaussianSignalPosteriorBaseKernel baseMean hbaseMean
    priorVariance (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
  letI : IsMarkovKernel posteriorKernel := by
    simpa [posteriorKernel] using
      (gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
  have hbaseScoreFactor : lg21HiddenAccessAccessBaseScoreLaw M testFeature =
      baseLaw ⊗ₘ scoreKernel := by
    simpa [scoreKernel] using
      (lg21_hiddenAccess_accessBaseScoreLaw_eq_gaussianLocation
        E baseLaw baseMean hbaseMean priorVariance hpriorVariance hnoiseVariance
        hsourceFactor)
  have hallReportByBase : ∀ᵐ publicBase ∂baseLaw,
      ∀ᵐ score ∂scoreKernel publicBase,
        E.reportDecision publicBase score = true := by
    have hallReport : ∀ᵐ profile ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
        E.reportDecision profile.1 profile.2 = true :=
      lg21HiddenAccess_allReport_ae_of_accessNoReport_mass_zero
        M E.access_positive testFeature E.reportDecision E.reportDecision_measurable hzero
    rw [hbaseScoreFactor] at hallReport
    exact Measure.ae_ae_of_ae_compProd hallReport
  have hnoReportBase : ∀ᵐ publicBase ∂baseLaw,
      E.noReportPayoff publicBase = baseMean publicBase :=
    E.noReportPayoff_eq_baseMean_ae_on_baseLaw_of_allTake_allReport
      hnoAccess hactiveNoTakeZero hzero baseLaw baseMean hbaseMean priorVariance
      hpriorVariance hnoiseVariance hsourceFactor
  have hreporterPositive : 0 < rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) := by
    simpa [rawLaw] using
      E.optionalReportEvent_positive_of_allTake_allReport
        hactiveNoTakeZero hzero
  have hreporterLaw : reporterLaw = accessLaw := by
    simpa [rawLaw, reporterLaw, accessLaw] using
      E.optionalReporterLaw_eq_accessLaw_of_allTake_allReport
        hactiveNoTakeZero hzero
  have hreportedPBO : ∀ᵐ publicScore ∂reporterLaw.map baseScore,
      E.reportedPayoff publicScore.1 publicScore.2 =
        ∫ latentSkill, latentSkill ∂posteriorKernel publicScore := by
    simpa [rawLaw, reporterLaw, baseScore, posteriorKernel] using
      E.reportedPayoff_eq_rawGaussianPosterior_ae_of_allTake
        hactiveNoTakeZero hreporterPositive baseLaw baseMean hbaseMean priorVariance
        hpriorVariance hnoiseVariance hsourceFactor
  have hreporterBaseScoreFactor : reporterLaw.map baseScore =
      baseLaw ⊗ₘ scoreKernel := by
    calc
      reporterLaw.map baseScore = accessLaw.map baseScore := by rw [hreporterLaw]
      _ = lg21HiddenAccessAccessBaseScoreLaw M testFeature := by rfl
      _ = baseLaw ⊗ₘ scoreKernel := hbaseScoreFactor
  rw [hreporterBaseScoreFactor] at hreportedPBO
  have hreportedByBase : ∀ᵐ publicBase ∂baseLaw,
      ∀ᵐ score ∂scoreKernel publicBase,
        E.reportedPayoff publicBase score =
          ∫ latentSkill, latentSkill ∂posteriorKernel (publicBase, score) :=
    Measure.ae_ae_of_ae_compProd hreportedPBO
  have hbestByBase := lg21HiddenAccess_reportBestResponse_ae_by_base_of_factorization
    E hreportBest baseLaw scoreKernel hbaseScoreFactor
  have hposteriorLowerBound : ∀ᵐ publicBase ∂baseLaw,
      ∀ᵐ score ∂scoreKernel publicBase,
        baseMean publicBase ≤ ∫ latentSkill, latentSkill ∂
          posteriorKernel (publicBase, score) := by
    filter_upwards [hnoReportBase, hallReportByBase, hbestByBase, hreportedByBase]
      with publicBase hnoReport hallReport hbest hreported
    filter_upwards [hallReport, hbest, hreported] with score hreport hbestAt hreportedAt
    calc
      baseMean publicBase = E.noReportPayoff publicBase := hnoReport.symm
      _ ≤ E.reportedPayoff publicBase score := hbestAt hreport
      _ = ∫ latentSkill, latentSkill ∂posteriorKernel (publicBase, score) := hreportedAt
  have hfalse : ∀ᵐ publicBase ∂baseLaw, False := by
    filter_upwards [hposteriorLowerBound] with publicBase hbound
    exact lg21_not_ae_baseMean_le_rawGaussianPosterior
      baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ)
      hpriorVariance hnoiseVariance publicBase (by
        simpa [scoreKernel, posteriorKernel] using hbound)
  have hbaseZero : baseLaw Set.univ = 0 := by
    simpa using (ae_iff.mp hfalse)
  have hbaseOne : baseLaw Set.univ = 1 := IsProbabilityMeasure.measure_univ
  rw [hbaseOne] at hbaseZero
  norm_num at hbaseZero

end

end LG21TestOptionalPolicies
