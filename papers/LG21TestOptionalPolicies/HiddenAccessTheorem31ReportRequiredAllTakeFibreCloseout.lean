import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralSource
import LG21TestOptionalPolicies.HiddenAccessTheorem31CandidatePBORefinement
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterPBOBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralPBOBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredActionClassification
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate
import LG21TestOptionalPolicies.ContinuousObservedAccessActualPBOBridge
import LG21TestOptionalPolicies.RawGaussianOptionalPositiveBranch
import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge

/-!
# Local all-taking branch identification for LG21 Theorem 3.1

This module records the literal, observable part of the report-required
all-taking argument.  On a public-base region where access students who decline
the test have zero raw mass, the actual no-report branch is, almost everywhere,
exactly the no-access branch.  The conclusion is deliberately an equality of
events and normalized laws; it does not condition on an unobserved skill band
or select a value of a PBO at a null history.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE

/-- On a base region where access no-takers have null raw mass, forced
reporting makes the literal no-report event coincide a.e. with the literal
no-access event.  This is an action-level fact and uses no posterior formula. -/
theorem noReportRegion_ae_eq_noAccessRegion_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0) :
    Set.inter
      (lg21HiddenAccessOptionalNoReportEvent (Feature := Feature) testFeature E.source.takeDecision
        E.source.reportDecision)
      (lg21HiddenAccessBaseRegionEvent testFeature region) =ᵐ[
        lg21ContinuousGaussianPopulationLaw M]
      Set.inter (lg21HiddenAccessNoAccessEvent (Feature := Feature))
        (lg21HiddenAccessBaseRegionEvent testFeature region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.source.takeDecision E.source.reportDecision
  let noAccess : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessNoAccessEvent
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  have hnull : ∀ᵐ student ∂rawLaw,
      student ∉ regionEvent ∩ E.source.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw, regionEvent] using hregionNoTakeZero
  filter_upwards [hnull] with student hnot
  apply propext
  rcases student with ⟨access, primitive⟩
  cases access with
  | false =>
      change
        (lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
            E.source.reportDecision (false, primitive) = false ∧
          lg21HiddenAccessStudentBase testFeature primitive ∈ region) ↔
        (false = false ∧
          lg21HiddenAccessStudentBase testFeature primitive ∈ region)
      simp [lg21HiddenAccessOptionalObservedAction]
  | true =>
      by_cases hregion : lg21HiddenAccessStudentBase testFeature primitive ∈ region
      · by_cases htake :
          lg21HiddenAccessStudentTake testFeature E.source.takeDecision primitive = true
        · have hreport :
            lg21HiddenAccessStudentReport testFeature E.source.reportDecision primitive =
              true := by
            simpa [lg21HiddenAccessStudentReport] using
              E.reportDecision_eq_true
                (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive)
          change
            (lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
                E.source.reportDecision (true, primitive) = false ∧
              lg21HiddenAccessStudentBase testFeature primitive ∈ region) ↔
            (true = false ∧
              lg21HiddenAccessStudentBase testFeature primitive ∈ region)
          simp [lg21HiddenAccessOptionalObservedAction, htake, hreport]
        · have htakeFalse :
            lg21HiddenAccessStudentTake testFeature E.source.takeDecision primitive = false :=
            Bool.eq_false_of_not_eq_true htake
          have hbad : (true, primitive) ∈
              regionEvent ∩ E.source.activeNoTakeEvent := by
            constructor
            · simpa [regionEvent, lg21HiddenAccessBaseRegionEvent] using hregion
            · simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
                htakeFalse]
          exact (hnot hbad).elim
      · change
          (lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
              E.source.reportDecision (true, primitive) = false ∧
            lg21HiddenAccessStudentBase testFeature primitive ∈ region) ↔
          (true = false ∧
            lg21HiddenAccessStudentBase testFeature primitive ∈ region)
        simp [hregion]

/-- The same local all-taking hypothesis identifies the attained reporter
branch with the access population on that public-base region.  This is the
reporter-side counterpart to `noReportRegion_ae_eq_noAccessRegion...`. -/
theorem reportRegion_ae_eq_accessRegion_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0) :
    Set.inter
      (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
        E.source.reportDecision)
      (lg21HiddenAccessBaseRegionEvent testFeature region) =ᵐ[
        lg21ContinuousGaussianPopulationLaw M]
      Set.inter
        ({student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true})
        (lg21HiddenAccessBaseRegionEvent testFeature region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.source.takeDecision E.source.reportDecision
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  have hnull : ∀ᵐ student ∂rawLaw,
      student ∉ regionEvent ∩ E.source.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw, regionEvent] using hregionNoTakeZero
  filter_upwards [hnull] with student hnot
  apply propext
  rcases student with ⟨access, primitive⟩
  cases access with
  | false =>
      change
        (lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
            E.source.reportDecision (false, primitive) = true ∧
          lg21HiddenAccessStudentBase testFeature primitive ∈ region) ↔
        (false = true ∧
          lg21HiddenAccessStudentBase testFeature primitive ∈ region)
      simp [lg21HiddenAccessOptionalObservedAction]
  | true =>
      by_cases hregion : lg21HiddenAccessStudentBase testFeature primitive ∈ region
      · by_cases htake :
          lg21HiddenAccessStudentTake testFeature E.source.takeDecision primitive = true
        · have hreport :
            lg21HiddenAccessStudentReport testFeature E.source.reportDecision primitive =
              true := by
            simpa [lg21HiddenAccessStudentReport] using
              E.reportDecision_eq_true
                (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive)
          change
            (lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
                E.source.reportDecision (true, primitive) = true ∧
              lg21HiddenAccessStudentBase testFeature primitive ∈ region) ↔
            (true = true ∧
              lg21HiddenAccessStudentBase testFeature primitive ∈ region)
          simp [lg21HiddenAccessOptionalObservedAction, htake, hreport]
        · have htakeFalse :
            lg21HiddenAccessStudentTake testFeature E.source.takeDecision primitive = false :=
            Bool.eq_false_of_not_eq_true htake
          have hbad : (true, primitive) ∈
              regionEvent ∩ E.source.activeNoTakeEvent := by
            constructor
            · simpa [regionEvent, lg21HiddenAccessBaseRegionEvent] using hregion
            · simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
                htakeFalse]
          exact (hnot hbad).elim
      · change
          (lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
              E.source.reportDecision (true, primitive) = true ∧
            lg21HiddenAccessStudentBase testFeature primitive ∈ region) ↔
          (true = true ∧
            lg21HiddenAccessStudentBase testFeature primitive ∈ region)
        simp [hregion]

/-- Normalizing the local reporter branch gives exactly the local access law
under the preceding event identity. -/
theorem localReporterLaw_eq_localAccessLaw_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0) :
    lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      ((lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
        E.source.reportDecision) ∩
        lg21HiddenAccessBaseRegionEvent testFeature region) =
    lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      ({student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true} ∩
        lg21HiddenAccessBaseRegionEvent testFeature region) := by
  exact lg21_optional_normalizedRestriction_congr_ae
    (lg21ContinuousGaussianPopulationLaw M)
    (E.reportRegion_ae_eq_accessRegion_of_activeNoTake_zero region
      hregionNoTakeZero)

/-- Independence of access from the primitive Gaussian population transports
a positive public-base region to a positive access mass. -/
theorem lg21HiddenAccess_access_inter_baseRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (haccess : 0 < M.accessLaw {true})
    (hregion : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      ({student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true} ∩
        lg21HiddenAccessBaseRegionEvent testFeature region) := by
  let primitiveRegion : Set (ℝ × (Feature -> ℝ)) :=
    {primitive | lg21HiddenAccessStudentBase testFeature primitive ∈ region}
  have hregionEq : lg21HiddenAccessBaseRegionEvent testFeature region =
      Set.univ ×ˢ primitiveRegion := by
    ext student
    simp [lg21HiddenAccessBaseRegionEvent, primitiveRegion]
  have hintersectionEq :
      ({student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true} ∩
        lg21HiddenAccessBaseRegionEvent testFeature region) =
      ({true} : Set Bool) ×ˢ primitiveRegion := by
    rw [hregionEq]
    ext student
    simp
  have hprimitivePositive : 0 <
      lg21ContinuousGaussianStudentPrimitiveLaw M primitiveRegion := by
    rw [hregionEq,
      lg21ContinuousGaussianPopulation_access_student_factorization] at hregion
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    rw [IsProbabilityMeasure.measure_univ, one_mul] at hregion
    exact hregion
  rw [hintersectionEq,
    lg21ContinuousGaussianPopulation_access_student_factorization]
  exact ENNReal.mul_pos (ne_of_gt haccess) (ne_of_gt hprimitivePositive)

/-- The preceding event equality transports directly to the locally normalized
no-report law.  This exposes the actual no-access mixture law required for a
subsequent local PBO or stability contradiction. -/
theorem localNoReportLaw_eq_localNoAccessLaw_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0) :
    lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      ((lg21HiddenAccessOptionalNoReportEvent (Feature := Feature) testFeature E.source.takeDecision
        E.source.reportDecision) ∩ lg21HiddenAccessBaseRegionEvent testFeature region) =
    lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessNoAccessEvent (Feature := Feature) ∩
        lg21HiddenAccessBaseRegionEvent testFeature region) := by
  exact lg21_optional_normalizedRestriction_congr_ae
    (lg21ContinuousGaussianPopulationLaw M)
    (E.noReportRegion_ae_eq_noAccessRegion_of_activeNoTake_zero region
      hregionNoTakeZero)

/-- The actual no-report PBO transports to a positive base region on which
access no-takers have null mass.  It is then a conditional skill mean under
the local literal no-access law.  The selected region is a public-base event,
so this is a restriction of an attained PBO rather than a belief assignment at
a latent-band-labelled history. -/
theorem localNoReportPayoff_eq_condDistrib_ae_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hlocalNoAccessPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessNoAccessEvent (Feature := Feature) ∩
        lg21HiddenAccessBaseRegionEvent testFeature region))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let noReportEvent := lg21HiddenAccessOptionalNoReportEvent testFeature
      E.source.takeDecision E.source.reportDecision
    let noAccessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      lg21HiddenAccessNoAccessEvent
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
    let localNoAccessLaw := lg21NormalizedRestriction rawLaw
      (noAccessEvent ∩ regionEvent)
    let base : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
      lg21ContinuousPopulationSkill
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure localNoAccessLaw :=
      lg21NormalizedRestriction_isProbability rawLaw (noAccessEvent ∩ regionEvent)
        (ne_of_gt hlocalNoAccessPositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure localNoAccessLaw := ⟨by simp⟩
    ∀ᵐ student ∂localNoAccessLaw,
      E.source.noReportPayoff (base student) =
        ∫ latentSkill, latentSkill ∂
          condDistrib skill base localNoAccessLaw (base student) := by
  intro rawLaw noReportEvent noAccessEvent regionEvent localNoAccessLaw base skill
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localNoAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (noAccessEvent ∩ regionEvent)
      (ne_of_gt hlocalNoAccessPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localNoAccessLaw := ⟨by simp⟩
  let localNoReportLaw := lg21NormalizedRestriction rawLaw
    (noReportEvent ∩ regionEvent)
  let globalNoReportLaw := lg21NormalizedRestriction rawLaw noReportEvent
  have hnoReportEvent : MeasurableSet noReportEvent := by
    simpa [noReportEvent] using
      (lg21HiddenAccessOptionalNoReportEvent_measurable testFeature
        E.source.takeDecision E.source.reportDecision E.source.takeDecision_measurable
        E.source.reportDecision_measurable)
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hregionEventEq : Set.inter noReportEvent regionEvent =ᵐ[rawLaw]
      Set.inter noAccessEvent regionEvent := by
    simpa [rawLaw, noReportEvent, noAccessEvent, regionEvent] using
      E.noReportRegion_ae_eq_noAccessRegion_of_activeNoTake_zero region
        hregionNoTakeZero
  have hlocalNoReportPositive : 0 < rawLaw (noReportEvent ∩ regionEvent) := by
    change 0 < rawLaw (Set.inter noReportEvent regionEvent)
    rw [measure_congr hregionEventEq]
    change 0 < rawLaw (Set.inter noAccessEvent regionEvent)
    simpa [rawLaw, noAccessEvent, regionEvent] using hlocalNoAccessPositive
  have hglobalNoReportPositive : 0 < rawLaw noReportEvent :=
    lt_of_lt_of_le hlocalNoReportPositive (measure_mono inter_subset_left)
  letI : IsProbabilityMeasure globalNoReportLaw :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt hglobalNoReportPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure globalNoReportLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localNoReportLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (noReportEvent ∩ regionEvent)
      (ne_of_gt hlocalNoReportPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localNoReportLaw := ⟨by simp⟩
  have hglobalPBO : (fun student => E.source.noReportPayoff (base student)) =ᵐ[
      globalNoReportLaw]
      globalNoReportLaw[skill | MeasurableSpace.comap base inferInstance] := by
    simpa [LG21HiddenAccessActualNoReportPBO, rawLaw, globalNoReportLaw,
      noReportEvent, base, skill] using E.source.noReport_pbo hglobalNoReportPositive
  have hregionPreimage : base ⁻¹' region = regionEvent := by
    ext student
    rfl
  have hselectedPositive : 0 < globalNoReportLaw (base ⁻¹' region) := by
    rw [hregionPreimage]
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw noReportEvent
      regionEvent hnoReportEvent hlocalNoReportPositive
  have hselectedPBO := lg21_publicPBO_condDistrib_on_positive_publicEvent_ae
    globalNoReportLaw base skill (fun student => E.source.noReportPayoff (base student))
    hbase hskill (by
      unfold globalNoReportLaw lg21NormalizedRestriction
      simpa [rawLaw, noReportEvent, skill] using
        (lg21ContinuousGaussianPopulation_skill_integrable M).restrict.smul_measure
          (ENNReal.inv_ne_top.mpr (ne_of_gt hglobalNoReportPositive)))
    hglobalPBO region hregion hselectedPositive
  have hselectedLaw : lg21NormalizedRestriction globalNoReportLaw
      (base ⁻¹' region) = localNoReportLaw := by
    rw [hregionPreimage]
    simpa [globalNoReportLaw, localNoReportLaw] using
      (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
        noReportEvent regionEvent hnoReportEvent hregionEvent)
  have hlocalNoReportPBO : ∀ᵐ student ∂localNoReportLaw,
      E.source.noReportPayoff (base student) =
        ∫ latentSkill, latentSkill ∂
          condDistrib skill base localNoReportLaw (base student) := by
    simpa only [hselectedLaw] using hselectedPBO
  have hlocalLaw : localNoReportLaw = localNoAccessLaw := by
    simpa [rawLaw, noReportEvent, noAccessEvent, regionEvent,
      localNoReportLaw, localNoAccessLaw] using
      E.localNoReportLaw_eq_localNoAccessLaw_of_activeNoTake_zero region
        hregionNoTakeZero
  simpa only [hlocalLaw] using hlocalNoReportPBO

/-- On a positive base region with locally all-taking access types, the
literal no-report PBO is the unselected Gaussian prior mean conditional on
the public base.  The proof first transports the real no-report PBO to the
local no-access branch, then factors that branch from the source joint law.
-/
theorem localNoReportPayoff_eq_baseMean_ae_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let noAccessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      lg21HiddenAccessNoAccessEvent
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
    let localNoAccessLaw := lg21NormalizedRestriction rawLaw
      (noAccessEvent ∩ regionEvent)
    let base : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    ∀ᵐ student ∂localNoAccessLaw,
      E.source.noReportPayoff (base student) = baseMean (base student) := by
  intro rawLaw noAccessEvent regionEvent localNoAccessLaw base
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let noAccessLaw := lg21HiddenAccessNoAccessLaw M
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let joint := gaussianSignalJointKernel baseMean hbaseMean priorVariance
    (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hlocalNoAccessPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive M testFeature region
        hnoAccess hregionPositive)
  letI : IsProbabilityMeasure localNoAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (noAccessEvent ∩ regionEvent)
      (ne_of_gt hlocalNoAccessPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localNoAccessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure noAccessLaw := by
    simpa [noAccessLaw] using
      (lg21HiddenAccessNoAccessLaw_isProbability M hnoAccess)
  letI : IsFiniteMeasure noAccessLaw := ⟨by simp⟩
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ))
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hnoAccessEvent : MeasurableSet noAccessEvent := by
    unfold noAccessEvent lg21HiddenAccessNoAccessEvent
    exact (measurableSet_singleton false).preimage measurable_fst
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalPBO := E.localNoReportPayoff_eq_condDistrib_ae_of_activeNoTake_zero
    region hregion hlocalNoAccessPositive hregionNoTakeZero
  have hPBO : ∀ᵐ student ∂localNoAccessLaw,
      E.source.noReportPayoff (base student) =
        ∫ latentSkill, latentSkill ∂
          condDistrib skill base localNoAccessLaw (base student) := by
    simpa [rawLaw, noAccessEvent, regionEvent, localNoAccessLaw, base, skill] using
      hlocalPBO
  have hlocalAsNoAccess : localNoAccessLaw =
      lg21NormalizedRestriction noAccessLaw regionEvent := by
    symm
    simpa [rawLaw, noAccessEvent, regionEvent, localNoAccessLaw, noAccessLaw] using
      (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
        noAccessEvent regionEvent hnoAccessEvent hregionEvent)
  have hrawSourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ joint := by
    simpa [joint] using hsourceFactor
  have hjointSkill : joint.map Prod.snd = skillKernel := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal]
    rw [show skillKernel publicBase =
        gaussianReal (baseMean publicBase) priorVariance.toNNReal by
      exact gaussianLocationKernel_apply baseMean hbaseMean priorVariance.toNNReal
        publicBase]
  have hfullBaseLatent :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ skillKernel := by
    calc
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ joint.map Prod.snd := by
            simpa [joint] using
              (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
                M E.source.access_positive testFeature baseLaw baseMean hbaseMean
                priorVariance (M.noiseVariance testFeature : ℝ) hrawSourceFactor)
      _ = baseLaw ⊗ₘ skillKernel := by rw [hjointSkill]
  have hnoAccessPair : noAccessLaw.map (fun student =>
      (base student, skill student)) = baseLaw ⊗ₘ skillKernel := by
    calc
      noAccessLaw.map (fun student => (base student, skill student)) =
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
            simpa [noAccessLaw, base, skill] using
              (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature)
      _ = baseLaw ⊗ₘ skillKernel := hfullBaseLatent
  have hregionPreimage : (fun student => (base student, skill student)) ⁻¹'
      (region ×ˢ Set.univ) = regionEvent := by
    ext student
    simp [base, regionEvent, lg21HiddenAccessBaseRegionEvent]
  have hlocalPair : localNoAccessLaw.map (fun student =>
      (base student, skill student)) =
      lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel := by
    calc
      localNoAccessLaw.map (fun student => (base student, skill student)) =
          (lg21NormalizedRestriction noAccessLaw regionEvent).map
            (fun student => (base student, skill student)) := by
              rw [hlocalAsNoAccess]
      _ = (lg21NormalizedRestriction noAccessLaw
          ((fun student => (base student, skill student)) ⁻¹'
            (region ×ˢ Set.univ))).map
            (fun student => (base student, skill student)) := by
              rw [hregionPreimage]
      _ = lg21NormalizedRestriction
          (noAccessLaw.map (fun student => (base student, skill student)))
          (region ×ˢ Set.univ) := by
              exact lg21_normalizedRestriction_map_preimage noAccessLaw
                (fun student => (base student, skill student)) (hbase.prodMk hskill)
                (region ×ˢ Set.univ) (hregion.prod MeasurableSet.univ)
      _ = lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel)
          (region ×ˢ Set.univ) := by rw [hnoAccessPair]
      _ = lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel := by
            rw [lg21_normalizedRestriction_compProd_left baseLaw skillKernel
              region hregion]
  have hbaseMarginal : localNoAccessLaw.map base =
      lg21NormalizedRestriction baseLaw region := by
    letI : SFinite (lg21NormalizedRestriction baseLaw region) := by
      unfold lg21NormalizedRestriction
      infer_instance
    calc
      localNoAccessLaw.map base =
          (localNoAccessLaw.map (fun student =>
            (base student, skill student))).map Prod.fst := by
              rw [Measure.map_map measurable_fst (hbase.prodMk hskill)]
              rfl
      _ = (lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel).map Prod.fst := by
            rw [hlocalPair]
      _ = lg21NormalizedRestriction baseLaw region := Measure.fst_compProd _ _
  have hjoint : localNoAccessLaw.map (fun student =>
      (base student, skill student)) =
      localNoAccessLaw.map base ⊗ₘ skillKernel := by
    rw [hlocalPair, hbaseMarginal]
  have hcondDistrib : condDistrib skill base localNoAccessLaw =ᵐ[
      localNoAccessLaw.map base] skillKernel := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hbase hskill hjoint
  have hcondPullback : ∀ᵐ student ∂localNoAccessLaw,
      condDistrib skill base localNoAccessLaw (base student) =
        skillKernel (base student) := by
    exact ae_of_ae_map hbase.aemeasurable hcondDistrib
  filter_upwards [hPBO, hcondPullback] with student hPBOAt hcondAt
  rw [hPBOAt, hcondAt]
  simpa [skillKernel] using
    (lg21_gaussianLocationKernel_skill_mean baseMean hbaseMean
      priorVariance.toNNReal (base student))

/-- On a locally all-taking public-base region, the literal reporter PBO is
the unselected Gaussian posterior mean on the local access base-score law.
The proof retains the actual global reporter law until it is explicitly
restricted by the public base coordinate, then uses the local action-event
identity to replace the selected law by the access law. -/
theorem localReportedPayoff_eq_rawGaussianPosterior_ae_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
    let localAccessLaw := lg21NormalizedRestriction rawLaw
      (accessEvent ∩ regionEvent)
    let base : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
      fun student => lg21HiddenAccessStudentScore testFeature student.2
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (base student, score student)
    let posteriorKernel : Kernel
        ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ℝ :=
      gaussianSignalPosteriorBaseKernel baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ)
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ)
    (fun publicScore => E.source.reportedPayoff publicScore.1 publicScore.2) =ᵐ[
      localAccessLaw.map baseScore]
      fun publicScore => ∫ latentSkill, latentSkill ∂posteriorKernel publicScore := by
  intro rawLaw accessEvent regionEvent localAccessLaw base score baseScore posteriorKernel
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.source.takeDecision E.source.reportDecision
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let takeEvent := lg21HiddenAccessTakerEvent testFeature E.source.takeDecision
  let takerLaw := lg21NormalizedRestriction accessLaw takeEvent
  let reportSet := lg21HiddenAccessReportSet testFeature E.source.reportDecision
  let reporterLaw := lg21NormalizedRestriction rawLaw reportEvent
  let localReporterLaw := lg21NormalizedRestriction rawLaw (reportEvent ∩ regionEvent)
  let selected : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    region ×ˢ Set.univ
  let localTakerLaw := lg21NormalizedRestriction takerLaw
    (baseScore ⁻¹' selected)
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  let rawObservation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
    fun student => (base student, (score student, skill student))
  let observationSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    fun student => (baseScore student, skill student)
  let association : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ≃ᵐ
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.source.access_positive)
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov baseMean hbaseMean priorVariance
      (M.noiseVariance testFeature : ℝ)
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hscore : Measurable score := by
    simpa [score] using
      ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hrawObservation : Measurable rawObservation := hbase.prodMk (hscore.prodMk hskill)
  have hobservationSkill : Measurable observationSkill := hbaseScore.prodMk hskill
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have haccessEvent : MeasurableSet accessEvent := by
    unfold accessEvent
    exact (measurableSet_singleton true).preimage measurable_fst
  have hreportEvent : MeasurableSet reportEvent := by
    simpa [reportEvent] using
      (lg21HiddenAccessOptionalReportEvent_measurable testFeature
        E.source.takeDecision E.source.reportDecision E.source.takeDecision_measurable
        E.source.reportDecision_measurable)
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21HiddenAccessTakerEvent_measurable testFeature E.source.takeDecision
        E.source.takeDecision_measurable)
  have hlocalAccessPositive : 0 < rawLaw (accessEvent ∩ regionEvent) := by
    simpa [rawLaw, accessEvent, regionEvent] using
      (lg21HiddenAccess_access_inter_baseRegion_positive M testFeature region
        E.source.access_positive hregionPositive)
  letI : IsProbabilityMeasure localAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (accessEvent ∩ regionEvent)
      (ne_of_gt hlocalAccessPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localAccessLaw := ⟨by simp⟩
  have hreportRegionEq : Set.inter reportEvent regionEvent =ᵐ[rawLaw]
      Set.inter accessEvent regionEvent := by
    simpa [rawLaw, reportEvent, accessEvent, regionEvent] using
      E.reportRegion_ae_eq_accessRegion_of_activeNoTake_zero region
        hregionNoTakeZero
  have hlocalReporterPositive : 0 < rawLaw (reportEvent ∩ regionEvent) := by
    change 0 < rawLaw (Set.inter reportEvent regionEvent)
    rw [measure_congr hreportRegionEq]
    exact hlocalAccessPositive
  have hglobalReporterPositive : 0 < rawLaw reportEvent :=
    lt_of_lt_of_le hlocalReporterPositive (measure_mono inter_subset_left)
  have htakePositive : 0 < accessLaw takeEvent := by
    simpa [accessLaw, takeEvent] using
      (E.source.accessLaw_takerEvent_positive hglobalReporterPositive)
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability accessLaw takeEvent
      (ne_of_gt htakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hglobalReporterPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hreportSet : reportSet = Set.univ := by
    ext publicScore
    simp [reportSet, lg21HiddenAccessReportSet, E.reportDecision_eq_true]
  have hreporterLaw : reporterLaw = takerLaw := by
    calc
      reporterLaw = lg21NormalizedRestriction takerLaw
          (baseScore ⁻¹' reportSet) := by
            simpa [rawLaw, accessLaw, takeEvent, takerLaw, baseScore,
              reportSet, reporterLaw] using
              (lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw E.source)
      _ = takerLaw := by simp [hreportSet, lg21NormalizedRestriction]
  have hreportedReporter : (fun student => E.source.reportedPayoff
      (base student) (score student)) =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill baseScore takerLaw (baseScore student) := by
    simpa [rawLaw, accessLaw, takeEvent, takerLaw, baseScore, reportSet,
      reporterLaw, base, score, skill] using
      (E.source.reportedPayoff_eq_takerBaseScoreCondMean_ae hglobalReporterPositive)
  have hreportedTaker : (fun student => E.source.reportedPayoff
      (base student) (score student)) =ᵐ[takerLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill baseScore takerLaw (baseScore student) := by
    simpa only [hreporterLaw] using hreportedReporter
  have hintegrableTaker : Integrable skill takerLaw := by
    unfold takerLaw lg21NormalizedRestriction
    exact (lg21ContinuousGaussianAccessPopulation_skill_integrable M
      E.source.access_positive).restrict.smul_measure
        (ENNReal.inv_ne_top.mpr (ne_of_gt htakePositive))
  have hcondExpTaker : takerLaw[skill |
      MeasurableSpace.comap baseScore inferInstance] =ᵐ[takerLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill baseScore takerLaw (baseScore student) := by
    exact condExp_ae_eq_integral_condDistrib' hbaseScore hintegrableTaker
  have hreportedTakerCond : (fun student => E.source.reportedPayoff
      (base student) (score student)) =ᵐ[takerLaw]
      takerLaw[skill | MeasurableSpace.comap baseScore inferInstance] :=
    hreportedTaker.trans hcondExpTaker.symm
  have hselected : MeasurableSet selected := hregion.prod MeasurableSet.univ
  have hbaseScoreSelectedPreimage : baseScore ⁻¹' selected = regionEvent := by
    ext student
    simp [baseScore, base, score, selected, regionEvent,
      lg21HiddenAccessBaseRegionEvent]
  have hselectedPositive : 0 < takerLaw (baseScore ⁻¹' selected) := by
    rw [← hreporterLaw, hbaseScoreSelectedPreimage]
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw reportEvent
      regionEvent hreportEvent hlocalReporterPositive
  letI : IsProbabilityMeasure localTakerLaw :=
    lg21NormalizedRestriction_isProbability takerLaw (baseScore ⁻¹' selected)
      (ne_of_gt hselectedPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localTakerLaw := ⟨by simp⟩
  have hselectedPBO := lg21_publicPBO_condDistrib_on_positive_publicEvent_ae
    takerLaw baseScore skill (fun student => E.source.reportedPayoff
      (base student) (score student))
    hbaseScore hskill hintegrableTaker hreportedTakerCond selected hselected hselectedPositive
  have hlocalTakerReporter : localTakerLaw = localReporterLaw := by
    calc
      localTakerLaw = lg21NormalizedRestriction reporterLaw
          (baseScore ⁻¹' selected) := by rw [hreporterLaw]
      _ = lg21NormalizedRestriction reporterLaw regionEvent := by
            rw [hbaseScoreSelectedPreimage]
      _ = lg21NormalizedRestriction
          (lg21NormalizedRestriction rawLaw reportEvent) regionEvent := by rfl
      _ = localReporterLaw := by
            simpa [localReporterLaw] using
              (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
                reportEvent regionEvent hreportEvent hregionEvent)
  have hlocalReporterAccess : localReporterLaw = localAccessLaw := by
    simpa [rawLaw, reportEvent, accessEvent, regionEvent,
      localReporterLaw, localAccessLaw] using
      E.localReporterLaw_eq_localAccessLaw_of_activeNoTake_zero region
        hregionNoTakeZero
  have hlocalTakerAccess : localTakerLaw = localAccessLaw :=
    hlocalTakerReporter.trans hlocalReporterAccess
  have hlocalPBO : (fun student => E.source.reportedPayoff
      (base student) (score student)) =ᵐ[localAccessLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib skill baseScore localAccessLaw (baseScore student) := by
    simpa only [localTakerLaw, hlocalTakerAccess] using hselectedPBO
  have hlocalAccessAsAccess : localAccessLaw =
      lg21NormalizedRestriction accessLaw regionEvent := by
    symm
    simpa [rawLaw, accessEvent, regionEvent, localAccessLaw, accessLaw,
      lg21ContinuousPopulationAccess] using
      (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
        accessEvent regionEvent haccessEvent hregionEvent)
  have haccessFactor : accessLaw.map rawObservation =
      baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ) := by
    calc
      accessLaw.map rawObservation = rawLaw.map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
            simpa [accessLaw, rawLaw, rawObservation, base, score, skill,
              lg21HiddenAccessBaseScoreSkillObservation] using
              (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                M E.source.access_positive testFeature).symm
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ) := hsourceFactor
  have haccessObservationFactor : accessLaw.map observationSkill =
      (baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
    calc
      accessLaw.map observationSkill =
          (accessLaw.map rawObservation).map association := by
            rw [Measure.map_map association.measurable hrawObservation]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)).map association := by
            rw [haccessFactor]
      _ = gaussianSignalBaseScoreLatentLaw baseLaw baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ) := by rfl
      _ = (baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
            simpa [scoreKernel, posteriorKernel] using
              (gaussianSignalBaseScoreLatentLaw_factorization baseLaw baseMean hbaseMean
                priorVariance (M.noiseVariance testFeature : ℝ)
                hpriorVariance hnoiseVariance)
  have hregionObservationPreimage : observationSkill ⁻¹'
      ((region ×ˢ Set.univ) ×ˢ Set.univ) = regionEvent := by
    ext student
    simp [observationSkill, baseScore, base, score, skill, regionEvent,
      lg21HiddenAccessBaseRegionEvent]
  have hlocalObservationFactor : localAccessLaw.map observationSkill =
      (lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
    calc
      localAccessLaw.map observationSkill =
          (lg21NormalizedRestriction accessLaw regionEvent).map observationSkill := by
            rw [hlocalAccessAsAccess]
      _ = (lg21NormalizedRestriction accessLaw
          (observationSkill ⁻¹' ((region ×ˢ Set.univ) ×ˢ Set.univ))).map
            observationSkill := by rw [hregionObservationPreimage]
      _ = lg21NormalizedRestriction (accessLaw.map observationSkill)
          ((region ×ˢ Set.univ) ×ˢ Set.univ) := by
            exact lg21_normalizedRestriction_map_preimage accessLaw observationSkill
              hobservationSkill ((region ×ˢ Set.univ) ×ˢ Set.univ)
              ((hregion.prod MeasurableSet.univ).prod MeasurableSet.univ)
      _ = lg21NormalizedRestriction
          ((baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel)
          ((region ×ˢ Set.univ) ×ˢ Set.univ) := by rw [haccessObservationFactor]
      _ = lg21NormalizedRestriction (baseLaw ⊗ₘ scoreKernel)
          (region ×ˢ Set.univ) ⊗ₘ posteriorKernel := by
            rw [lg21_normalizedRestriction_compProd_left
              (baseLaw ⊗ₘ scoreKernel) posteriorKernel
              (region ×ˢ Set.univ) (hregion.prod MeasurableSet.univ)]
      _ = (lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel) ⊗ₘ
          posteriorKernel := by
            rw [lg21_normalizedRestriction_compProd_left baseLaw scoreKernel
              region hregion]
  have hlocalBaseScore : localAccessLaw.map baseScore =
      lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel := by
    letI : SFinite (lg21NormalizedRestriction baseLaw region) := by
      unfold lg21NormalizedRestriction
      infer_instance
    calc
      localAccessLaw.map baseScore =
          (localAccessLaw.map observationSkill).map Prod.fst := by
            rw [Measure.map_map measurable_fst hobservationSkill]
            rfl
      _ = ((lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel) ⊗ₘ
          posteriorKernel).map Prod.fst := by rw [hlocalObservationFactor]
      _ = lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel :=
        Measure.fst_compProd _ _
  have hjoint : localAccessLaw.map observationSkill =
      localAccessLaw.map baseScore ⊗ₘ posteriorKernel := by
    rw [hlocalObservationFactor, hlocalBaseScore]
  have hcondDistrib : condDistrib skill baseScore localAccessLaw =ᵐ[
      localAccessLaw.map baseScore] posteriorKernel := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hbaseScore hskill hjoint
  have hcondPullback : ∀ᵐ student ∂localAccessLaw,
      condDistrib skill baseScore localAccessLaw (baseScore student) =
        posteriorKernel (baseScore student) := by
    exact ae_of_ae_map hbaseScore.aemeasurable hcondDistrib
  have hreportedPosterior : (fun student => E.source.reportedPayoff
      (base student) (score student)) =ᵐ[localAccessLaw]
      fun student => ∫ latentSkill, latentSkill ∂posteriorKernel (baseScore student) := by
    filter_upwards [hlocalPBO, hcondPullback] with student hPBO hcond
    rw [hPBO, hcond]
  have hposteriorMeanMeasurable : Measurable (fun publicScore =>
      ∫ latentSkill, latentSkill ∂posteriorKernel publicScore) := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  refine (MeasureTheory.ae_map_iff hbaseScore.aemeasurable
    (measurableSet_eq_fun E.source.reportedPayoff_measurable
      hposteriorMeanMeasurable)).mpr ?_
  simpa [baseScore, base, score] using hreportedPosterior

/-- Restricting the literal access population to a public-base region leaves
the source Gaussian `(base, score)` factorization intact.  This is a raw-law
transport only; it is independent of the strategic action taken on that
region. -/
theorem localAccessBaseScoreLaw_eq_gaussianLocation_of_sourceFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
    let localAccessLaw := lg21NormalizedRestriction rawLaw
      (accessEvent ∩ regionEvent)
    let base : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
      fun student => lg21HiddenAccessStudentScore testFeature student.2
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (base student, score student)
    localAccessLaw.map baseScore =
      lg21NormalizedRestriction baseLaw region ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean
          (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal := by
  intro rawLaw accessEvent regionEvent localAccessLaw base score baseScore
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
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
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.source.access_positive)
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
  letI : IsMarkovKernel posteriorKernel := by
    simpa [posteriorKernel] using
      (gaussianSignalPosteriorBaseKernel_isMarkov baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ))
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hscore : Measurable score := by
    simpa [score] using
      ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hrawObservation : Measurable rawObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hobservationSkill : Measurable observationSkill := hbaseScore.prodMk hskill
  have haccessEvent : MeasurableSet accessEvent := by
    unfold accessEvent
    exact (measurableSet_singleton true).preimage measurable_fst
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalPositive : 0 < rawLaw (accessEvent ∩ regionEvent) := by
    simpa [rawLaw, accessEvent, regionEvent] using
      (lg21HiddenAccess_access_inter_baseRegion_positive M testFeature region
        E.source.access_positive hregionPositive)
  letI : IsProbabilityMeasure localAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (accessEvent ∩ regionEvent)
      (ne_of_gt hlocalPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localAccessLaw := ⟨by simp⟩
  have hlocalAccessAsAccess : localAccessLaw =
      lg21NormalizedRestriction accessLaw regionEvent := by
    symm
    simpa [rawLaw, accessEvent, regionEvent, localAccessLaw, accessLaw,
      lg21ContinuousPopulationAccess] using
      (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
        accessEvent regionEvent haccessEvent hregionEvent)
  have haccessFactor : accessLaw.map rawObservation =
      baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ) := by
    calc
      accessLaw.map rawObservation = rawLaw.map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
            simpa [accessLaw, rawLaw, rawObservation, base, score, skill,
              lg21HiddenAccessBaseScoreSkillObservation] using
              (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                M E.source.access_positive testFeature).symm
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ) := hsourceFactor
  have haccessObservationFactor : accessLaw.map observationSkill =
      (baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
    calc
      accessLaw.map observationSkill =
          (accessLaw.map rawObservation).map association := by
            rw [Measure.map_map association.measurable hrawObservation]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)).map association := by
            rw [haccessFactor]
      _ = gaussianSignalBaseScoreLatentLaw baseLaw baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ) := by rfl
      _ = (baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
            simpa [scoreKernel, posteriorKernel] using
              (gaussianSignalBaseScoreLatentLaw_factorization baseLaw baseMean hbaseMean
                priorVariance (M.noiseVariance testFeature : ℝ)
                hpriorVariance hnoiseVariance)
  have hregionObservationPreimage : observationSkill ⁻¹'
      ((region ×ˢ Set.univ) ×ˢ Set.univ) = regionEvent := by
    ext student
    simp [observationSkill, baseScore, base, score, skill, regionEvent,
      lg21HiddenAccessBaseRegionEvent]
  have hlocalObservationFactor : localAccessLaw.map observationSkill =
      (lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel := by
    calc
      localAccessLaw.map observationSkill =
          (lg21NormalizedRestriction accessLaw regionEvent).map observationSkill := by
            rw [hlocalAccessAsAccess]
      _ = (lg21NormalizedRestriction accessLaw
          (observationSkill ⁻¹' ((region ×ˢ Set.univ) ×ˢ Set.univ))).map
            observationSkill := by rw [hregionObservationPreimage]
      _ = lg21NormalizedRestriction (accessLaw.map observationSkill)
          ((region ×ˢ Set.univ) ×ˢ Set.univ) := by
            exact lg21_normalizedRestriction_map_preimage accessLaw observationSkill
              hobservationSkill ((region ×ˢ Set.univ) ×ˢ Set.univ)
              ((hregion.prod MeasurableSet.univ).prod MeasurableSet.univ)
      _ = lg21NormalizedRestriction
          ((baseLaw ⊗ₘ scoreKernel) ⊗ₘ posteriorKernel)
          ((region ×ˢ Set.univ) ×ˢ Set.univ) := by
            rw [haccessObservationFactor]
      _ = lg21NormalizedRestriction (baseLaw ⊗ₘ scoreKernel)
          (region ×ˢ Set.univ) ⊗ₘ posteriorKernel := by
            rw [lg21_normalizedRestriction_compProd_left
              (baseLaw ⊗ₘ scoreKernel) posteriorKernel
              (region ×ˢ Set.univ) (hregion.prod MeasurableSet.univ)]
      _ = (lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel) ⊗ₘ
          posteriorKernel := by
            rw [lg21_normalizedRestriction_compProd_left baseLaw scoreKernel
              region hregion]
  letI : SFinite (lg21NormalizedRestriction baseLaw region) := by
    unfold lg21NormalizedRestriction
    infer_instance
  calc
    localAccessLaw.map baseScore =
        (localAccessLaw.map observationSkill).map Prod.fst := by
          rw [Measure.map_map measurable_fst hobservationSkill]
          rfl
    _ = ((lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel) ⊗ₘ
        posteriorKernel).map Prod.fst := by rw [hlocalObservationFactor]
    _ = lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel :=
      Measure.fst_compProd _ _

/-- The corresponding local access `(base, latent-skill)` law.  Keeping this
separate from the score law makes the later pre-score best-response argument
explicit about its information timing. -/
theorem localAccessBaseSkillLaw_eq_gaussianLocation_of_sourceFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
    let localAccessLaw := lg21NormalizedRestriction rawLaw
      (accessEvent ∩ regionEvent)
    let baseSkill : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      lg21HiddenAccessBaseSkillObservation testFeature
    localAccessLaw.map baseSkill =
      lg21NormalizedRestriction baseLaw region ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean priorVariance.toNNReal := by
  intro rawLaw accessEvent regionEvent localAccessLaw baseSkill
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let latentBase : Bool × (ℝ × (Feature -> ℝ)) ->
      ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student =>
      (lg21ContinuousPopulationSkill student,
        lg21HiddenAccessStudentBase testFeature student.2)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.source.access_positive)
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  have hbaseSkill : Measurable baseSkill := by
    simpa [baseSkill] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hlatentBase : Measurable latentBase := by
    simpa [latentBase] using
      (lg21HiddenAccessLatentBaseObservation_measurable testFeature)
  have haccessEvent : MeasurableSet accessEvent := by
    unfold accessEvent
    exact (measurableSet_singleton true).preimage measurable_fst
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalPositive : 0 < rawLaw (accessEvent ∩ regionEvent) := by
    simpa [rawLaw, accessEvent, regionEvent] using
      (lg21HiddenAccess_access_inter_baseRegion_positive M testFeature region
        E.source.access_positive hregionPositive)
  letI : IsProbabilityMeasure localAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (accessEvent ∩ regionEvent)
      (ne_of_gt hlocalPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localAccessLaw := ⟨by simp⟩
  have hlocalAccessAsAccess : localAccessLaw =
      lg21NormalizedRestriction accessLaw regionEvent := by
    symm
    simpa [rawLaw, accessEvent, regionEvent, localAccessLaw, accessLaw,
      lg21ContinuousPopulationAccess] using
      (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
        accessEvent regionEvent haccessEvent hregionEvent)
  have haccessFactor : accessLaw.map baseSkill = baseLaw ⊗ₘ skillKernel := by
    calc
      accessLaw.map baseSkill = (accessLaw.map latentBase).map Prod.swap := by
        rw [Measure.map_map measurable_swap hlatentBase]
        rfl
      _ = (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap := by
        rfl
      _ = baseLaw ⊗ₘ skillKernel := by
        simpa [skillKernel] using
          (lg21HiddenAccessAccessLatentBaseLaw_swap_eq_gaussianLocation_of_scoreFactor
            M E.source.access_positive testFeature baseLaw baseMean hbaseMean
            priorVariance (M.noiseVariance testFeature : ℝ) hsourceFactor)
  have hregionPreimage : baseSkill ⁻¹' (region ×ˢ Set.univ) = regionEvent := by
    ext student
    simp [baseSkill, regionEvent, lg21HiddenAccessBaseSkillObservation,
      lg21HiddenAccessBaseRegionEvent]
  calc
    localAccessLaw.map baseSkill =
        (lg21NormalizedRestriction accessLaw regionEvent).map baseSkill := by
          rw [hlocalAccessAsAccess]
    _ = (lg21NormalizedRestriction accessLaw
        (baseSkill ⁻¹' (region ×ˢ Set.univ))).map baseSkill := by
          rw [hregionPreimage]
    _ = lg21NormalizedRestriction (accessLaw.map baseSkill)
        (region ×ˢ Set.univ) := by
          exact lg21_normalizedRestriction_map_preimage accessLaw baseSkill
            hbaseSkill (region ×ˢ Set.univ) (hregion.prod MeasurableSet.univ)
    _ = lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel)
        (region ×ˢ Set.univ) := by rw [haccessFactor]
    _ = lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel := by
          rw [lg21_normalizedRestriction_compProd_left baseLaw skillKernel
            region hregion]

/-- A zero raw mass of access no-takers on a public-base region becomes an
almost-everywhere all-taking statement under that region's Gaussian
`(base, latent-skill)` law. -/
theorem localAllTake_ae_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ publicBase ∂lg21NormalizedRestriction baseLaw region,
      ∀ᵐ latentSkill ∂gaussianLocationKernel baseMean hbaseMean
        priorVariance.toNNReal publicBase,
        E.source.takeDecision latentSkill publicBase = true := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let localAccessLaw := lg21NormalizedRestriction rawLaw
    (accessEvent ∩ regionEvent)
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let baseSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, skill student)
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  have haccessEvent : MeasurableSet accessEvent := by
    unfold accessEvent
    exact (measurableSet_singleton true).preimage measurable_fst
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalPositive : 0 < rawLaw (accessEvent ∩ regionEvent) := by
    simpa [rawLaw, accessEvent, regionEvent] using
      (lg21HiddenAccess_access_inter_baseRegion_positive M testFeature region
        E.source.access_positive hregionPositive)
  letI : IsProbabilityMeasure localAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (accessEvent ∩ regionEvent)
      (ne_of_gt hlocalPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localAccessLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hbaseSkill : Measurable baseSkill := hbase.prodMk hskill
  have htakeAction : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      E.source.takeDecision profile.2 profile.1) := by
    simpa using
      (E.source.takeDecision_measurable.comp (measurable_snd.prodMk measurable_fst))
  have hrawNull : ∀ᵐ student ∂rawLaw,
      student ∉ regionEvent ∩ E.source.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw, regionEvent] using hregionNoTakeZero
  have hlocalNull : ∀ᵐ student ∂localAccessLaw,
      student ∉ regionEvent ∩ E.source.activeNoTakeEvent := by
    have hlocalAC : localAccessLaw ≪ rawLaw := by
      unfold localAccessLaw lg21NormalizedRestriction
      exact Measure.smul_absolutelyContinuous.trans
        Measure.restrict_le_self.absolutelyContinuous
    exact hlocalAC.ae_le hrawNull
  have hlocalMember : ∀ᵐ student ∂localAccessLaw,
      student ∈ accessEvent ∩ regionEvent := by
    unfold localAccessLaw lg21NormalizedRestriction
    exact Measure.ae_smul_measure
      (ae_restrict_mem (haccessEvent.inter hregionEvent)) _
  have hlocalAll : ∀ᵐ student ∂localAccessLaw,
      E.source.takeDecision (skill student) (base student) = true := by
    filter_upwards [hlocalNull, hlocalMember] with student hnull hmember
    by_cases htake : E.source.takeDecision (skill student) (base student) = true
    · exact htake
    · have htakeFalse : E.source.takeDecision (skill student) (base student) = false :=
        Bool.eq_false_of_not_eq_true htake
      have hactive : student ∈ E.source.activeNoTakeEvent := by
        change student.1 = true ∧
          E.source.takeDecision student.2.1
            (lg21HiddenAccessStudentBase testFeature student.2) = false
        refine ⟨by simpa [accessEvent] using hmember.1, ?_⟩
        simpa [base, skill, lg21HiddenAccessStudentTake] using htakeFalse
      exact (hnull ⟨hmember.2, hactive⟩).elim
  have hlocalBaseSkill : localAccessLaw.map baseSkill =
      lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel := by
    simpa [rawLaw, accessEvent, regionEvent, localAccessLaw, baseSkill,
      skillKernel] using
      (E.localAccessBaseSkillLaw_eq_gaussianLocation_of_sourceFactor
        region hregion hregionPositive baseLaw baseMean hbaseMean priorVariance
        hsourceFactor)
  letI : SFinite (lg21NormalizedRestriction baseLaw region) := by
    unfold lg21NormalizedRestriction
    infer_instance
  have hproduct : ∀ᵐ profile ∂
      lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel,
      E.source.takeDecision profile.2 profile.1 = true := by
    rw [← hlocalBaseSkill]
    refine (MeasureTheory.ae_map_iff hbaseSkill.aemeasurable
      ((measurableSet_singleton true).preimage htakeAction)).mpr ?_
    simpa [Function.comp_def, baseSkill, base, skill] using hlocalAll
  simpa [skillKernel] using Measure.ae_ae_of_ae_compProd hproduct

/-- The locally attained reporter PBO can be evaluated under every individual
Gaussian test law.  This is an a.e. null-set transport from the actual
positive reporter branch, followed by the source's nondegenerate Gaussian
test law; it does not compare an infeasible post-score action. -/
theorem localReportedPayoff_eq_rawGaussianPosterior_ae_under_eachTestLaw_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ publicBase ∂lg21NormalizedRestriction baseLaw region, ∀ latentSkill,
      ∀ᵐ score ∂E.source.testLaw latentSkill publicBase,
        E.source.reportedPayoff publicBase score =
          ∫ skill, skill ∂gaussianSignalPosteriorBaseKernel baseMean hbaseMean
            priorVariance (M.noiseVariance testFeature : ℝ) (publicBase, score) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let localAccessLaw := lg21NormalizedRestriction rawLaw
    (accessEvent ∩ regionEvent)
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, score student)
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
      (gaussianSignalPosteriorBaseKernel_isMarkov baseMean hbaseMean
        priorVariance (M.noiseVariance testFeature : ℝ))
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hscore : Measurable score := by
    simpa [score] using
      ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hlocal : (fun publicScore =>
      E.source.reportedPayoff publicScore.1 publicScore.2) =ᵐ[
        localAccessLaw.map baseScore]
      fun publicScore => ∫ latentSkill, latentSkill ∂posteriorKernel publicScore := by
    simpa [rawLaw, accessEvent, regionEvent, localAccessLaw, base, score,
      baseScore, posteriorKernel] using
      (E.localReportedPayoff_eq_rawGaussianPosterior_ae_of_activeNoTake_zero
        region hregion hregionPositive hregionNoTakeZero baseLaw baseMean hbaseMean
        priorVariance hpriorVariance hnoiseVariance hsourceFactor)
  have hlocalBaseScore : localAccessLaw.map baseScore =
      lg21NormalizedRestriction baseLaw region ⊗ₘ scoreKernel := by
    simpa [rawLaw, accessEvent, regionEvent, localAccessLaw, base, score,
      baseScore, scoreKernel] using
      (E.localAccessBaseScoreLaw_eq_gaussianLocation_of_sourceFactor
        region hregion hregionPositive baseLaw baseMean hbaseMean priorVariance
        hpriorVariance hnoiseVariance hsourceFactor)
  letI : SFinite (lg21NormalizedRestriction baseLaw region) := by
    unfold lg21NormalizedRestriction
    infer_instance
  rw [hlocalBaseScore] at hlocal
  have hbyBase := Measure.ae_ae_of_ae_compProd hlocal
  filter_upwards [hbyBase] with publicBase hPBO latentSkill
  rw [E.source.raw_test_law latentSkill publicBase]
  have hscoreLaw : scoreKernel publicBase = gaussianReal (baseMean publicBase)
      (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal := by
    exact gaussianLocationKernel_apply baseMean hbaseMean
      (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal publicBase
  have hnoiseNN : 0 < M.noiseVariance testFeature := by
    exact_mod_cast hnoiseVariance
  have htestAC : gaussianReal latentSkill
      (M.noiseVariance testFeature) ≪ scoreKernel publicBase := by
    rw [hscoreLaw]
    exact AppliedModelingLib.Probability.gaussianReal_absolutelyContinuous_of_positive_variances
      latentSkill (baseMean publicBase)
      hnoiseNN
      (Real.toNNReal_pos.mpr (add_pos hpriorVariance hnoiseVariance))
  exact htestAC.ae_eq hPBO

/-- On a locally all-taking base region, the pre-score value of taking is the
Gaussian posterior's ex-ante affine value.  The equality is derived after
integrating the on-path PBO under each test law, which is the timing required
by the report-required policy. -/
theorem localTakeExpectedPayoff_eq_rawGaussianAffine_ae_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ publicBase ∂lg21NormalizedRestriction baseLaw region, ∀ latentSkill,
      (∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase) =
        gaussianSignalPriorWeight priorVariance (M.noiseVariance testFeature : ℝ) *
            baseMean publicBase +
          gaussianSignalWeight priorVariance (M.noiseVariance testFeature : ℝ) *
            latentSkill := by
  have hPBO :=
    E.localReportedPayoff_eq_rawGaussianPosterior_ae_under_eachTestLaw_of_activeNoTake_zero
      region hregion hregionPositive hregionNoTakeZero baseLaw baseMean hbaseMean
      priorVariance hpriorVariance hnoiseVariance hsourceFactor
  filter_upwards [hPBO] with publicBase hPBO latentSkill
  have hPBOAt := hPBO latentSkill
  rw [E.source.raw_test_law latentSkill publicBase] at hPBOAt
  rw [E.source.raw_test_law latentSkill publicBase]
  calc
    (∫ score, E.source.reportedPayoff publicBase score ∂
        gaussianReal latentSkill (M.noiseVariance testFeature)) =
        ∫ score, (∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ)
            (publicBase, score)) ∂gaussianReal latentSkill
              (M.noiseVariance testFeature) :=
      integral_congr_ae hPBOAt
    _ = ∫ score,
        (gaussianSignalPriorWeight priorVariance (M.noiseVariance testFeature : ℝ) *
            baseMean publicBase +
          gaussianSignalWeight priorVariance (M.noiseVariance testFeature : ℝ) * score)
          ∂gaussianReal latentSkill (M.noiseVariance testFeature) := by
      apply integral_congr_ae
      filter_upwards with score
      rw [gaussianSignalPosteriorBaseKernel_integral_id]
      ring
    _ = gaussianSignalPriorWeight priorVariance (M.noiseVariance testFeature : ℝ) *
          baseMean publicBase +
        gaussianSignalWeight priorVariance (M.noiseVariance testFeature : ℝ) *
          latentSkill :=
      lg21_gaussian_expected_affine_test_payoff latentSkill
        (M.noiseVariance testFeature)
        (gaussianSignalPriorWeight priorVariance
          (M.noiseVariance testFeature : ℝ) * baseMean publicBase)
        (gaussianSignalWeight priorVariance
          (M.noiseVariance testFeature : ℝ))

/-- A nondegenerate Gaussian score has a positive lower tail on which its
unselected posterior mean is strictly below the prior/base mean.  This is the
analytic exclusion used after the literal local action and PBO transports. -/
theorem lg21_not_ae_baseMean_le_rawGaussianPosterior
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
  have hscoreVariance : 0 < priorVariance + noiseVariance := by linarith
  have hscoreVarianceNN : (priorVariance + noiseVariance).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hscoreVariance)
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
      (strictMono_gaussianSignalPosteriorBaseKernel_integral_id baseMean hbaseMean
        priorVariance noiseVariance hpriorVariance hnoiseVariance publicBase)
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

/-- The local no-access population has exactly the source base law restricted
to the public region.  This law identity is independent of strategy labels;
it follows from the literal access product and the Gaussian source factor. -/
theorem localNoAccessBaseLaw_eq_selectedBase
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let noAccessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      lg21HiddenAccessNoAccessEvent
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
    let localNoAccessLaw := lg21NormalizedRestriction rawLaw
      (noAccessEvent ∩ regionEvent)
    let base : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    localNoAccessLaw.map base = lg21NormalizedRestriction baseLaw region := by
  intro rawLaw noAccessEvent regionEvent localNoAccessLaw base
  let noAccessLaw := lg21HiddenAccessNoAccessLaw M
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let joint := gaussianSignalJointKernel baseMean hbaseMean priorVariance
    (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hlocalPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive M testFeature region
        hnoAccess hregionPositive)
  letI : IsProbabilityMeasure localNoAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (noAccessEvent ∩ regionEvent)
      (ne_of_gt hlocalPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localNoAccessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure noAccessLaw := by
    simpa [noAccessLaw] using
      (lg21HiddenAccessNoAccessLaw_isProbability M hnoAccess)
  letI : IsFiniteMeasure noAccessLaw := ⟨by simp⟩
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ))
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hnoAccessEvent : MeasurableSet noAccessEvent := by
    unfold noAccessEvent lg21HiddenAccessNoAccessEvent
    exact (measurableSet_singleton false).preimage measurable_fst
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalAsNoAccess : localNoAccessLaw =
      lg21NormalizedRestriction noAccessLaw regionEvent := by
    symm
    simpa [rawLaw, noAccessEvent, regionEvent, localNoAccessLaw, noAccessLaw] using
      (lg21_normalizedRestriction_normalizedRestriction_eq_inter rawLaw
        noAccessEvent regionEvent hnoAccessEvent hregionEvent)
  have hrawSourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ joint := by
    simpa [joint] using hsourceFactor
  have hjointSkill : joint.map Prod.snd = skillKernel := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal]
    rw [show skillKernel publicBase =
        gaussianReal (baseMean publicBase) priorVariance.toNNReal by
      exact gaussianLocationKernel_apply baseMean hbaseMean priorVariance.toNNReal
        publicBase]
  have hfullBaseLatent :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ skillKernel := by
    calc
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ joint.map Prod.snd := by
            simpa [joint] using
              (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
                M E.source.access_positive testFeature baseLaw baseMean hbaseMean
                priorVariance (M.noiseVariance testFeature : ℝ) hrawSourceFactor)
      _ = baseLaw ⊗ₘ skillKernel := by rw [hjointSkill]
  have hnoAccessPair : noAccessLaw.map (fun student =>
      (base student, skill student)) = baseLaw ⊗ₘ skillKernel := by
    calc
      noAccessLaw.map (fun student => (base student, skill student)) =
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
            simpa [noAccessLaw, base, skill] using
              (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature)
      _ = baseLaw ⊗ₘ skillKernel := hfullBaseLatent
  have hregionPreimage : (fun student => (base student, skill student)) ⁻¹'
      (region ×ˢ Set.univ) = regionEvent := by
    ext student
    simp [base, regionEvent, lg21HiddenAccessBaseRegionEvent]
  have hlocalPair : localNoAccessLaw.map (fun student =>
      (base student, skill student)) =
      lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel := by
    calc
      localNoAccessLaw.map (fun student => (base student, skill student)) =
          (lg21NormalizedRestriction noAccessLaw regionEvent).map
            (fun student => (base student, skill student)) := by
              rw [hlocalAsNoAccess]
      _ = (lg21NormalizedRestriction noAccessLaw
          ((fun student => (base student, skill student)) ⁻¹'
            (region ×ˢ Set.univ))).map
            (fun student => (base student, skill student)) := by
              rw [hregionPreimage]
      _ = lg21NormalizedRestriction
          (noAccessLaw.map (fun student => (base student, skill student)))
          (region ×ˢ Set.univ) := by
              exact lg21_normalizedRestriction_map_preimage noAccessLaw
                (fun student => (base student, skill student)) (hbase.prodMk hskill)
                (region ×ˢ Set.univ) (hregion.prod MeasurableSet.univ)
      _ = lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel)
          (region ×ˢ Set.univ) := by rw [hnoAccessPair]
      _ = lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel := by
            rw [lg21_normalizedRestriction_compProd_left baseLaw skillKernel
              region hregion]
  letI : SFinite (lg21NormalizedRestriction baseLaw region) := by
    unfold lg21NormalizedRestriction
    infer_instance
  calc
    localNoAccessLaw.map base =
        (localNoAccessLaw.map (fun student =>
          (base student, skill student))).map Prod.fst := by
            rw [Measure.map_map measurable_fst (hbase.prodMk hskill)]
            rfl
    _ = (lg21NormalizedRestriction baseLaw region ⊗ₘ skillKernel).map Prod.fst := by
          rw [hlocalPair]
    _ = lg21NormalizedRestriction baseLaw region := Measure.fst_compProd _ _

/-- The local no-report mean identity, expressed directly on the selected
public-base law.  This is the form that can be combined with reporter values
and score-level best responses without comparing access labels. -/
theorem localNoReportPayoff_eq_baseMean_ae_on_selectedBase_of_activeNoTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ publicBase ∂lg21NormalizedRestriction baseLaw region,
      E.source.noReportPayoff publicBase = baseMean publicBase := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noAccessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessNoAccessEvent
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let localNoAccessLaw := lg21NormalizedRestriction rawLaw
    (noAccessEvent ∩ regionEvent)
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hlocalNoAccessPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive M testFeature region
        hnoAccess hregionPositive)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localNoAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (noAccessEvent ∩ regionEvent)
      (ne_of_gt hlocalNoAccessPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localNoAccessLaw := ⟨by simp⟩
  have hvalue : ∀ᵐ student ∂localNoAccessLaw,
      E.source.noReportPayoff (base student) = baseMean (base student) := by
    simpa [rawLaw, noAccessEvent, regionEvent, localNoAccessLaw, base] using
      (E.localNoReportPayoff_eq_baseMean_ae_of_activeNoTake_zero region hregion
        hregionPositive hnoAccess hregionNoTakeZero baseLaw baseMean hbaseMean
        priorVariance hpriorVariance hnoiseVariance hsourceFactor)
  have hbaseLaw : localNoAccessLaw.map base =
      lg21NormalizedRestriction baseLaw region := by
    simpa [rawLaw, noAccessEvent, regionEvent, localNoAccessLaw, base] using
      (E.localNoAccessBaseLaw_eq_selectedBase region hregion hregionPositive
        hnoAccess baseLaw baseMean hbaseMean priorVariance hsourceFactor)
  rw [← hbaseLaw]
  refine (MeasureTheory.ae_map_iff hbase.aemeasurable
    (measurableSet_eq_fun E.source.noReportPayoff_measurable hbaseMean)).mpr ?_
  simpa [Function.comp_def] using hvalue

end LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE

end

end LG21TestOptionalPolicies
