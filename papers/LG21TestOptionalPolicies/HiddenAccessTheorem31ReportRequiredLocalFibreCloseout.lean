import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLocalTailCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralSource
import LG21TestOptionalPolicies.ObservedAccessReportRequiredRegionSupport
import LG21TestOptionalPolicies.SelectedGaussianSourceActionFactor

/-!
# Local-fibre closeout for report-required LG21 Theorem 3.1

This module keeps the report-required local-entry argument on the literal raw
hidden-access population.  A base-region restriction retains the no-access
component before its no-report PBO is recalibrated.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology
open Probability

/-- An almost-everywhere statement on a raw action branch remains valid after
normalizing the raw population on a measurable base region and restricting to
the same action branch. -/
theorem lg21_ae_localNormalizedRestriction_of_ae_rawRestriction
    {Omega : Type*} [MeasurableSpace Omega]
    (rawLaw : Measure Omega) (region actionEvent : Set Omega)
    (hactionEvent : MeasurableSet actionEvent) {P : Omega -> Prop}
    (hraw : ∀ᵐ omega ∂rawLaw.restrict actionEvent, P omega) :
    ∀ᵐ omega ∂(lg21NormalizedRestriction rawLaw region).restrict actionEvent,
      P omega := by
  have hlocalAC :
      (lg21NormalizedRestriction rawLaw region).restrict actionEvent ≪
        rawLaw.restrict actionEvent := by
    rw [lg21NormalizedRestriction, Measure.restrict_smul,
      Measure.restrict_restrict hactionEvent]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.restrict_mono inter_subset_left le_rfl).absolutelyContinuous
  exact hraw.filter_mono hlocalAC.ae_le

/-- Measurability of the literal report event follows from the source-timed
observed-action map; it does not assume anything about a candidate PBO. -/
theorem lg21HiddenAccessRawCandidateReportEvent_measurable_local
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidateTake pair.1 pair.2))
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessRawCandidateReportEvent testFeature
      candidateTake candidateReport) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature
      candidateTake candidateReport) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature
      candidateTake candidateReport hcandidateTake hcandidateReport)

/-- Measurability of the literal no-report event is obtained from the same
source-timed action map as the report branch. -/
theorem lg21HiddenAccessRawCandidateNoReportEvent_measurable_local
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidateTake pair.1 pair.2))
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessRawCandidateNoReportEvent testFeature
      candidateTake candidateReport) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature
      candidateTake candidateReport) ⁻¹' ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature
      candidateTake candidateReport hcandidateTake hcandidateReport)

/-- A positive base region has positive report-required tail mass.  The
second conclusion is the same fact on the global selected action law, which
is exactly what is needed to transport its literal PBO to the local branch. -/
theorem lg21ReportRequiredTail_localReport_and_globalRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (haccess : 0 < M.accessLaw {true})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)) ∧
    0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21ReportRequiredTailReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold))).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let regionProduct : Set ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) := region ×ˢ Set.univ
  let reportEvent := lg21ReportRequiredTailReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hregionProduct : MeasurableSet regionProduct := by
    simpa [regionProduct] using hregion.prod MeasurableSet.univ
  have hregionPreimage : observation ⁻¹' regionProduct = regionEvent := by
    ext student
    simp [observation, regionProduct, regionEvent,
      lg21HiddenAccessBaseScoreSkillObservation,
      lg21HiddenAccessBaseRegionEvent, lg21HiddenAccessStudentBase]
  have hbaseMap : rawLaw.map base = baseLaw := by
    calc
      rawLaw.map base = (rawLaw.map observation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservation]
        rfl
      _ = (baseLaw ⊗ₘ joint).map Prod.fst := by
        rw [show rawLaw.map observation = baseLaw ⊗ₘ joint by
          simpa [rawLaw, observation, joint] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ joint).fst = baseLaw
        rw [Measure.fst_compProd]
  have hbaseRegionPositive : 0 < baseLaw region := by
    have hrawRegionPositive : 0 < rawLaw (base ⁻¹' region) := by
      simpa [rawLaw, base, regionEvent] using hregionPositive
    rw [← Measure.map_apply hbase hregion, hbaseMap] at hrawRegionPositive
    exact hrawRegionPositive
  let localBaseLaw := lg21NormalizedRestriction baseLaw region
  letI : IsProbabilityMeasure localBaseLaw :=
    lg21NormalizedRestriction_isProbability baseLaw region
      (ne_of_gt hbaseRegionPositive) (measure_ne_top _ _)
  have htailLocalPositive : 0 < (localBaseLaw ⊗ₘ joint) tailEvent := by
    simpa [localBaseLaw, joint, tailEvent] using
      (lg21ReportRequiredBaseDependentTail_take_positive
        localBaseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold hthreshold)
  have htailNormalizedPositive : 0 <
      (lg21NormalizedRestriction (baseLaw ⊗ₘ joint) regionProduct) tailEvent := by
    rw [lg21_normalizedRestriction_compProd_left baseLaw joint region hregion]
    simpa [localBaseLaw] using htailLocalPositive
  have hjointIntersectionPositive : 0 < (baseLaw ⊗ₘ joint)
      (tailEvent ∩ regionProduct) := by
    rw [lg21NormalizedRestriction_apply (baseLaw ⊗ₘ joint) htailEvent]
      at htailNormalizedPositive
    exact (ENNReal.mul_pos_iff.mp htailNormalizedPositive).2
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  have haccessIntersectionPositive : 0 < accessLaw
      (observation ⁻¹' (tailEvent ∩ regionProduct)) := by
    rw [← Measure.map_apply hobservation (htailEvent.inter hregionProduct),
      haccessScoreSkill]
    exact hjointIntersectionPositive
  have hrawAccessIntersectionPositive : 0 < rawLaw
      (accessEvent ∩ observation ⁻¹' (tailEvent ∩ regionProduct)) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (observation ⁻¹' (tailEvent ∩ regionProduct)) at haccessIntersectionPositive
    rw [lg21NormalizedRestriction_apply rawLaw
      ((htailEvent.inter hregionProduct).preimage hobservation)]
      at haccessIntersectionPositive
    have hraw : 0 < rawLaw
        ((observation ⁻¹' (tailEvent ∩ regionProduct)) ∩ accessEvent) :=
      (ENNReal.mul_pos_iff.mp haccessIntersectionPositive).2
    simpa [inter_comm] using hraw
  have hreportEvent : reportEvent = accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [reportEvent, accessEvent, observation, tailEvent,
      lg21ReportRequiredTailReportEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  have hreportIntersectionPositive : 0 < rawLaw (reportEvent ∩ regionEvent) := by
    rw [hreportEvent, ← hregionPreimage]
    have hset : (accessEvent ∩ observation ⁻¹' tailEvent) ∩
        observation ⁻¹' regionProduct =
        accessEvent ∩ observation ⁻¹' (tailEvent ∩ regionProduct) := by
      ext student
      simp only [Set.mem_inter_iff, Set.mem_preimage, and_assoc]
    rw [hset]
    exact hrawAccessIntersectionPositive
  have hlocalPositive : 0 < lg21NormalizedRestriction rawLaw regionEvent
      reportEvent :=
    lg21_normalizedRestriction_pos_of_inter_pos rawLaw regionEvent
      reportEvent hregionEvent (by simpa [inter_comm] using hreportIntersectionPositive)
  have hglobalPositive : 0 < rawLaw reportEvent :=
    lt_of_lt_of_le hreportIntersectionPositive
      (measure_mono (by intro student hstudent; exact hstudent.1))
  let globalActionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map observation
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map hobservation.aemeasurable
  have hglobalRegionPositive : 0 < globalActionLaw (Prod.fst ⁻¹' region) := by
    rw [show globalActionLaw =
      (lg21NormalizedRestriction rawLaw reportEvent).map observation by rfl,
      Measure.map_apply hobservation (hregion.preimage measurable_fst),
      lg21NormalizedRestriction_apply rawLaw
        ((hregion.preimage measurable_fst).preimage hobservation)]
    have hpreimage : observation ⁻¹' (Prod.fst ⁻¹' region) = regionEvent := by
      ext student
      simp [observation, regionEvent,
        lg21HiddenAccessBaseScoreSkillObservation,
        lg21HiddenAccessBaseRegionEvent, lg21HiddenAccessStudentBase]
    rw [hpreimage]
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw reportEvent))
      (by simpa [inter_comm] using ne_of_gt hreportIntersectionPositive)
  refine ⟨?_, ?_⟩
  · simpa [rawLaw, regionEvent, reportEvent] using hlocalPositive
  · simpa [rawLaw, reportEvent, observation, globalActionLaw] using
      hglobalRegionPositive

/-- Transport the literal selected reporter PBO to a positive local base
region for the report-required tail candidate.  The proof first identifies
the local action law and then transports its conditional distribution. -/
theorem lg21ReportRequiredTail_localReportPBO_of_global
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (haccess : 0 < M.accessLaw {true})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hlocalPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)))
    (hglobalRegionPositive : 0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21ReportRequiredTailReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold))).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region))
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    LG21ReportRequiredTailReportPBOOn M testFeature region hregionPositive
      (lg21ReportRequiredHiddenAccessTailCandidate
        baseMean threshold hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessFinite haccessFinite)
      (by simpa [lg21ReportRequiredHiddenAccessTailCandidate] using hlocalPositive) := by
  let candidate := lg21ReportRequiredHiddenAccessTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance noAccessMass accessMass
    hnoAccessFinite haccessFinite
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision
  let globalEvent := lg21ReportRequiredTailReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let record := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let observation : ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) -> ℝ :=
    fun scoreSkill => scoreSkill.2.2
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map record
  let localActionLaw := (lg21NormalizedRestriction localLaw reportEvent).map record
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  have hglobalPositive : 0 < rawLaw globalEvent := by
    have hlocalPositiveRaw : 0 < rawLaw
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩ globalEvent) := by
      have hnormalized : 0 < lg21NormalizedRestriction rawLaw
          (lg21HiddenAccessBaseRegionEvent testFeature region) globalEvent := by
        simpa [rawLaw, localLaw, globalEvent,
          lg21ReportRequiredTailReportEvent] using hlocalPositive
      rw [lg21NormalizedRestriction_apply rawLaw
        (by
          simpa [globalEvent, lg21ReportRequiredTailReportEvent] using
            (lg21HiddenAccessRawCandidateReportEvent_measurable_local testFeature
              (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
              (fun _ _ => true)
              (lg21HiddenAccessConditionalMeanTailTake_measurable
                testFeature threshold hthreshold) measurable_const))]
        at hnormalized
      simpa [inter_comm] using (ENNReal.mul_pos_iff.mp hnormalized).2
    exact lt_of_lt_of_le hlocalPositiveRaw
      (measure_mono (by intro student hstudent; exact hstudent.2))
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw reportEvent
      (ne_of_gt (by simpa [localLaw, reportEvent, candidate] using hlocalPositive))
      (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hrecordBase : Measurable
      (Prod.fst : ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ)) := measurable_fst
  have hrecordBaseEq : ∀ student,
      Prod.fst (record student) =
        lg21HiddenAccessStudentBase testFeature student.2 := by
    intro student
    rfl
  have hglobalEventMeasurable : MeasurableSet globalEvent := by
    simpa [globalEvent, lg21ReportRequiredTailReportEvent] using
      (lg21HiddenAccessRawCandidateReportEvent_measurable_local testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)
        (lg21HiddenAccessConditionalMeanTailTake_measurable
          testFeature threshold hthreshold) measurable_const)
  have hlocalLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, globalActionLaw, localActionLaw,
      reportEvent, globalEvent, candidate,
      lg21ReportRequiredTailReportEvent] using
      (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw rawLaw
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2)
        record Prod.fst hbase hrecord hrecordBase hrecordBaseEq
        region hregion globalEvent hglobalEventMeasurable)
  have hglobalPBO : ∀ᵐ publicObservation ∂globalActionLaw.map observation,
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib latent observation
          globalActionLaw publicObservation := by
    simpa [rawLaw, globalEvent, globalActionLaw, record, observation, latent,
      lg21ReportRequiredTailReportEvent] using
      (lg21HiddenAccessConditionalMeanTail_reportedValue_eq_condDistribMean_ae
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw observation latent
    (fun publicObservation =>
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2)
    (by
      dsimp [observation]
      fun_prop)
    (by
      dsimp [latent]
      fun_prop)
    hglobalPBO (Prod.fst ⁻¹' region)
    (hregion.preimage measurable_fst)
    (by simpa [rawLaw, globalEvent, globalActionLaw, record,
      lg21ReportRequiredTailReportEvent] using hglobalRegionPositive)
  have hselectionBase : observation ⁻¹' (Prod.fst ⁻¹' region) =
      Prod.fst ⁻¹' region := by
    ext scoreSkill
    simp [observation]
  unfold LG21ReportRequiredTailReportPBOOn
  dsimp only
  simpa only [candidate, localLaw, reportEvent, record, localActionLaw,
    observation, latent, hselectionBase, ← hlocalLaw] using hselectedPBO

/-- A positive base region has positive literal no-report mass under the
report-required tail candidate.  The witness is the raw no-access component,
which remains in the PBO population after localization. -/
theorem lg21ReportRequiredTail_localNoReport_and_globalRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)) ∧
    0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21ReportRequiredTailNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold))).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let noAccessEvent := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let noReportEvent := lg21ReportRequiredTailNoReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hnoReportEvent : MeasurableSet noReportEvent := by
    simpa [noReportEvent, lg21ReportRequiredTailNoReportEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable_local testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)
        (lg21HiddenAccessConditionalMeanTailTake_measurable
          testFeature threshold hthreshold) measurable_const)
  have hcomponentPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive
        M testFeature region hnoAccess hregionPositive)
  have hsubset : noAccessEvent ∩ regionEvent ⊆ noReportEvent ∩ regionEvent := by
    intro student hstudent
    rcases hstudent with ⟨hnoAccessStudent, hregionStudent⟩
    refine ⟨?_, hregionStudent⟩
    rcases student with ⟨access, primitive⟩
    cases access <;>
      simp [noAccessEvent, lg21HiddenAccessNoAccessEvent, noReportEvent,
        lg21ReportRequiredTailNoReportEvent,
        lg21HiddenAccessRawCandidateNoReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport] at hnoAccessStudent ⊢
  have hlocalRawPositive : 0 < rawLaw (noReportEvent ∩ regionEvent) :=
    lt_of_lt_of_le hcomponentPositive (measure_mono hsubset)
  have hlocalPositive : 0 < lg21NormalizedRestriction rawLaw regionEvent
      noReportEvent := by
    rw [lg21NormalizedRestriction_apply rawLaw hnoReportEvent]
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw regionEvent))
      (ne_of_gt hlocalRawPositive)
  have hglobalPositive : 0 < rawLaw noReportEvent :=
    lt_of_lt_of_le hlocalRawPositive
      (measure_mono (by intro student hstudent; exact hstudent.1))
  let globalActionLaw :=
    (lg21NormalizedRestriction rawLaw noReportEvent).map record
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hregionPreimage : record ⁻¹' (Prod.fst ⁻¹' region) = regionEvent := by
    ext student
    simp [record, regionEvent, lg21HiddenAccessBaseSkillObservation,
      lg21HiddenAccessBaseRegionEvent]
  have hglobalRegionPositive : 0 < globalActionLaw (Prod.fst ⁻¹' region) := by
    rw [show globalActionLaw =
      (lg21NormalizedRestriction rawLaw noReportEvent).map record by rfl,
      Measure.map_apply hrecord (hregion.preimage measurable_fst),
      lg21NormalizedRestriction_apply rawLaw
        ((hregion.preimage measurable_fst).preimage hrecord),
      hregionPreimage]
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw noReportEvent))
      (by simpa [inter_comm] using ne_of_gt hlocalRawPositive)
  refine ⟨?_, ?_⟩
  · simpa [rawLaw, regionEvent, noReportEvent] using hlocalPositive
  · simpa [rawLaw, noReportEvent, record, globalActionLaw] using
      hglobalRegionPositive

/-- The literal no-report PBO transports to a localized base region.  Its
source factorization is over the full raw base/skill population, retaining
the no-access component rather than replacing it by an access posterior. -/
theorem lg21ReportRequiredTail_localNoReportPBO_of_global
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (gap : ℝ)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true})
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤)
    (hfullBaseFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal)
    (hlocalPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature
          (fun publicBase => baseMean publicBase + gap))))
    (hglobalRegionPositive : 0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21ReportRequiredTailNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature
            (fun publicBase => baseMean publicBase + gap)))).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
          (Prod.fst ⁻¹' region)) :
    LG21ReportRequiredTailNoReportPBOOn M testFeature region
      hregionPositive
      (lg21ReportRequiredHiddenAccessTailCandidate
        baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite)
      (by simpa [lg21ReportRequiredHiddenAccessTailCandidate] using hlocalPositive) := by
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let candidate := lg21ReportRequiredHiddenAccessTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21ReportRequiredTailNoReportEvent testFeature
    candidate.takeDecision
  let globalEvent := lg21ReportRequiredTailNoReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map record
  let localActionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map record
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  have hglobalPositive : 0 < rawLaw globalEvent := by
    simpa [rawLaw, globalEvent, threshold,
      lg21ReportRequiredTailNoReportEvent] using
      (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) hnoAccess)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw noReportEvent
      (ne_of_gt (by simpa [localLaw, noReportEvent, candidate, threshold] using
        hlocalPositive))
      (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hrecordBase : Measurable
      (Prod.fst : ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ->
        (LG21NonTestFeature Feature testFeature -> ℝ)) := measurable_fst
  have hrecordBaseEq : ∀ student,
      Prod.fst (record student) =
        lg21HiddenAccessStudentBase testFeature student.2 := by
    intro student
    rfl
  have hglobalEventMeasurable : MeasurableSet globalEvent := by
    simpa [globalEvent, lg21ReportRequiredTailNoReportEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable_local testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)
        (lg21HiddenAccessConditionalMeanTailTake_measurable
          testFeature threshold (hbaseMean.add measurable_const)) measurable_const)
  have hlocalLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, globalActionLaw, localActionLaw,
      noReportEvent, globalEvent, candidate, threshold,
      lg21ReportRequiredTailNoReportEvent] using
      (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw rawLaw
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2)
        record Prod.fst hbase hrecord hrecordBase hrecordBaseEq
        region hregion globalEvent hglobalEventMeasurable)
  have hglobalPBO : ∀ᵐ publicBase ∂globalActionLaw.map Prod.fst,
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite threshold publicBase =
        ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
          globalActionLaw publicBase := by
    simpa [rawLaw, globalEvent, globalActionLaw, record, threshold,
      lg21ReportRequiredTailNoReportEvent] using
      (lg21HiddenAccessConditionalMeanTail_noReportValue_eq_condDistribMean_ae
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance.toNNReal hfullBaseFactor gap hnoAccessFinite haccessFinite)
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw Prod.fst Prod.snd
    (fun publicBase =>
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite threshold publicBase)
    measurable_fst measurable_snd hglobalPBO region hregion
    (by simpa [rawLaw, globalEvent, globalActionLaw, record, threshold,
      lg21ReportRequiredTailNoReportEvent] using hglobalRegionPositive)
  unfold LG21ReportRequiredTailNoReportPBOOn
  dsimp only
  simpa only [candidate, localLaw, noReportEvent, record, localActionLaw,
    threshold, ← hlocalLaw] using hselectedPBO

/-- A zero-current-taker base region is incompatible with literal
report-required local-tail stability.  Both PBOs are recalibrated from their
actual local action populations before the positive-mass gain is used. -/
theorem lg21ReportRequired_not_stable_of_zeroCurrentTakeRegion_of_source
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    [IsFiniteMeasure M.accessLaw]
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hcurrentTakeZero : lg21HiddenAccessLocalRawLaw M testFeature region
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    ¬ LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) currentTake := by
  classical
  let noiseVariance : ℝ := (M.noiseVariance testFeature : ℝ)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := measure_ne_top _ _
  have hbaseVarianceNN : baseVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance)
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  obtain ⟨gap, hroot⟩ :=
    lg21ReportRequiredHiddenAccessMixture_exists_uniform_raw_root
      baseMean hbaseMean baseVariance.toNNReal hbaseVarianceNN
      (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess haccess
      hnoAccessFinite haccessFinite noiseVariance hnoiseVariance
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  have hthreshold : Measurable threshold := hbaseMean.add measurable_const
  have hroot' : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance (threshold publicBase) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite threshold publicBase := by
    intro publicBase
    simpa [threshold,
      Real.coe_toNNReal _ hbaseVariance.le] using hroot publicBase
  let candidate := lg21ReportRequiredHiddenAccessTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite
  have hcandidateTakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidate.takeDecision pair.1 pair.2) := by
    simpa [candidate, lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21HiddenAccessConditionalMeanTailTake_measurable
        testFeature threshold hthreshold)
  rcases lg21ReportRequiredTail_localReport_and_globalRegion_positive
      (M := M) (testFeature := testFeature) region hregion hregionPositive
      haccess baseLaw baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance threshold hthreshold hsourceFactor with
    ⟨hreportPositiveRaw, hglobalReportRegionPositiveRaw⟩
  have hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision) := by
    simpa [candidate, threshold, lg21ReportRequiredHiddenAccessTailCandidate] using
      hreportPositiveRaw
  have hglobalReportRegionPositive : 0 <
      ((lg21NormalizedRestriction rawLaw
        (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision)).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, candidate, threshold,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      hglobalReportRegionPositiveRaw
  rcases lg21ReportRequiredTail_localNoReport_and_globalRegion_positive
      (M := M) (testFeature := testFeature) region hregion hregionPositive
      hnoAccess threshold hthreshold with
    ⟨hnoReportPositiveRaw, hglobalNoReportRegionPositiveRaw⟩
  have hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision) := by
    simpa [candidate, threshold, lg21ReportRequiredHiddenAccessTailCandidate] using
      hnoReportPositiveRaw
  have hglobalNoReportRegionPositive : 0 <
      ((lg21NormalizedRestriction rawLaw
        (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision)).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, candidate, threshold,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      hglobalNoReportRegionPositiveRaw
  have hreportPBO : LG21ReportRequiredTailReportPBOOn M testFeature region
      hregionPositive candidate hreportPositive := by
    simpa [candidate, threshold, lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21ReportRequiredTail_localReportPBO_of_global
        (M := M) (testFeature := testFeature) region hregion hregionPositive
        haccess baseLaw baseMean threshold hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance hthreshold hsourceFactor
        hreportPositiveRaw hglobalReportRegionPositiveRaw
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite)
  have hfullBaseFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal :=
    lg21ReportRequiredBaseDependentTail_fullBaseLatent_eq_gaussianLocation_of_scoreFactor
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
      hsourceFactor
  have hnoReportPBO : LG21ReportRequiredTailNoReportPBOOn M testFeature region
      hregionPositive candidate hnoReportPositive := by
    simpa [candidate, threshold, lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21ReportRequiredTail_localNoReportPBO_of_global
        (M := M) (testFeature := testFeature) region hregion hregionPositive
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance gap hnoAccess haccess
        hnoAccessFinite haccessFinite hfullBaseFactor
        hnoReportPositiveRaw hglobalNoReportRegionPositiveRaw)
  have hstrictGainRaw :=
    lg21ReportRequiredHiddenAccessTail_changedTaker_strictGain_ae_of_source
      (M := M) (testFeature := testFeature) currentTake hcurrentTake
      baseLaw baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance gap hsourceFactor hroot'
  let changedEvent := lg21ReportRequiredTailChangedTesterEvent
    testFeature currentTake candidate.takeDecision
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hskill : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21ContinuousPopulationSkill student) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hcurrentRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)) :=
    hcurrentTake.comp (hskill.prodMk hbase)
  have htailRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      candidate.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)) :=
    hcandidateTakeMeasurable.comp (hskill.prodMk hbase)
  have hchangedEvent : MeasurableSet changedEvent := by
    dsimp only [changedEvent, lg21ReportRequiredTailChangedTesterEvent]
    change MeasurableSet ({student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true} ∩
        ({student | currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = false} ∩
        {student | candidate.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true}))
    exact ((measurableSet_singleton true).preimage measurable_fst).inter
      (((measurableSet_singleton false).preimage hcurrentRaw).inter
        ((measurableSet_singleton true).preimage htailRaw))
  have hstrictGain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
          candidate.takeDecision),
      candidate.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredTailTakeExpectedPayoff candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) := by
    simpa [rawLaw, regionEvent, changedEvent, candidate, threshold,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21_ae_localNormalizedRestriction_of_ae_rawRestriction rawLaw
        regionEvent changedEvent hchangedEvent hstrictGainRaw)
  exact lg21ReportRequired_not_stable_of_zeroCurrentTakeRegion
    currentTake hcurrentTake region hregion hregionPositive hcurrentTakeZero
    candidate
    { candidate_test_law := by
        intro latentSkill publicBase
        simp [candidate, lg21ReportRequiredHiddenAccessTailCandidate,
          noiseVariance]
      candidate_take_measurable := hcandidateTakeMeasurable
      report_positive := hreportPositive
      noReport_positive := hnoReportPositive
      report_pbo := hreportPBO
      noReport_pbo := hnoReportPBO
      changed_taker_strict_gain := hstrictGain }

/-- Literal source stability forces positive current taking mass on almost
every Gaussian base fibre.  A hypothetical positive zero-selection region is
converted into the exact localized current-taker-null premise consumed by
the preceding source entry theorem. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.ae_positive_takeSelectionMass_of_localTailStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.source.takeDecision)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean baseVariance.toNNReal
    let action : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
      fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
    let actionEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
      lg21SourceLatentActionEvent action
    ∀ᵐ publicBase ∂baseLaw,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
  intro skillKernel action actionEvent
  let noiseVariance : ℝ := (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel skillKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let rawBase : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let rawSkill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let rawBaseSkill := lg21HiddenAccessBaseSkillObservation testFeature
  have hrawBase : Measurable rawBase := by
    simpa [rawBase] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrawSkill : Measurable rawSkill := by
    simpa [rawSkill] using (measurable_fst.comp measurable_snd)
  have hrawBaseSkill : Measurable rawBaseSkill := by
    simpa [rawBaseSkill] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using
      (lg21SourceLatentActionEvent_measurable action haction)
  let zeroRegion : Set (LG21NonTestFeature Feature testFeature -> ℝ) :=
    {publicBase | selectionMass skillKernel actionEvent publicBase = 0}
  have hzeroRegion : MeasurableSet zeroRegion := by
    change MeasurableSet {publicBase |
      selectionMass skillKernel actionEvent publicBase = 0}
    exact (measurableSet_singleton 0).preimage
      (selectionMass_measurable hactionEvent)
  have hrawBaseSkillFactor : rawLaw.map rawBaseSkill =
      baseLaw ⊗ₘ skillKernel := by
    simpa [rawLaw, rawBaseSkill, skillKernel] using
      (lg21ReportRequiredBaseDependentTail_rawBaseSkill_eq_gaussianLocation_of_scoreFactor
        M testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
        hsourceFactor)
  have hrawBaseMarginal : rawLaw.map rawBase = baseLaw := by
    calc
      rawLaw.map rawBase = (rawLaw.map rawBaseSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hrawBaseSkill]
        rfl
      _ = (baseLaw ⊗ₘ skillKernel).map Prod.fst := by
        rw [hrawBaseSkillFactor]
      _ = baseLaw := by
        exact Measure.fst_compProd _ _
  have hzeroRegionNull : baseLaw zeroRegion = 0 := by
    by_contra hzeroRegionNotNull
    have hzeroRegionPositive : 0 < baseLaw zeroRegion :=
      pos_iff_ne_zero.mpr hzeroRegionNotNull
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature zeroRegion
    have hregionPositive : 0 < rawLaw regionEvent := by
      rw [show regionEvent = rawBase ⁻¹' zeroRegion by rfl,
        ← Measure.map_apply hrawBase hzeroRegion, hrawBaseMarginal]
      exact hzeroRegionPositive
    have hrawCurrentNoAccessZero : rawLaw
        (rawBase ⁻¹' zeroRegion ∩
          {student | E.source.takeDecision (rawSkill student)
            (rawBase student) = true}) = 0 := by
      exact lg21_reportRequired_source_currentTake_mass_zero_on_region
        rawLaw rawBase rawSkill hrawBase hrawSkill baseLaw skillKernel
        hrawBaseSkillFactor E.source.takeDecision
        (by simpa [Function.comp_def] using
          (E.source.takeDecision_measurable.comp
            (measurable_snd.prodMk measurable_fst)))
        zeroRegion hzeroRegion
        (by
          intro publicBase hmem
          change selectionMass skillKernel actionEvent publicBase = 0 at hmem
          simpa [actionEvent, action, lg21SourceLatentActionEvent,
            lg21ReportRequiredFullPublicTakeSet] using hmem)
    let currentEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true ∧
        E.source.takeDecision (rawSkill student) (rawBase student) = true}
    have hcurrentRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
        E.source.takeDecision (rawSkill student) (rawBase student)) := by
      simpa [rawSkill, rawBase] using
        (E.source.takeDecision_measurable.comp
          ((measurable_fst.comp measurable_snd).prodMk
            ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)))
    have hcurrentEvent : MeasurableSet currentEvent := by
      dsimp only [currentEvent]
      exact ((measurableSet_singleton true).preimage measurable_fst).inter
        ((measurableSet_singleton true).preimage hcurrentRaw)
    have hrawCurrentZero : rawLaw (regionEvent ∩ currentEvent) = 0 := by
      apply measure_mono_null _ hrawCurrentNoAccessZero
      intro student hstudent
      rcases hstudent with ⟨hregionMem, hcurrentMem⟩
      rcases hcurrentMem with ⟨_, htake⟩
      change rawBase student ∈ zeroRegion at hregionMem
      exact ⟨hregionMem, htake⟩
    have hlocalCurrentZero : lg21HiddenAccessLocalRawLaw M testFeature zeroRegion
        currentEvent = 0 := by
      change lg21NormalizedRestriction rawLaw regionEvent currentEvent = 0
      rw [lg21NormalizedRestriction_apply rawLaw hcurrentEvent,
        show currentEvent ∩ regionEvent = regionEvent ∩ currentEvent by
          exact Set.inter_comm currentEvent regionEvent,
        hrawCurrentZero]
      simp
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
    exact
      (lg21ReportRequired_not_stable_of_zeroCurrentTakeRegion_of_source
        M E.source.access_positive hnoAccess testFeature E.source.takeDecision
        E.source.takeDecision_measurable zeroRegion hzeroRegion hregionPositive
        (by simpa [currentEvent, rawSkill, rawBase] using hlocalCurrentZero)
        baseLaw baseMean hbaseMean baseVariance
        hbaseVariance hnoiseVariance hsourceFactor) hstable
  have hzeroAE : ∀ᵐ publicBase ∂baseLaw, publicBase ∉ zeroRegion := by
    simpa only [ae_iff, not_not] using hzeroRegionNull
  filter_upwards [hzeroAE] with publicBase hnotZero
  intro hzero
  apply hnotZero
  exact hzero

end

end LG21TestOptionalPolicies
