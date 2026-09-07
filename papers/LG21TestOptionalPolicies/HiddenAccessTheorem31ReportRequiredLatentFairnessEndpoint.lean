import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredSourceCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralOutputLawBridge

/-!
# Actual latent-law fairness endpoint for report-required LG21 Theorem 3.1

This file keeps the fairness conclusion on the literal public output map.  In
particular, it does not identify equality of output laws with equality of an
ex-ante payoff.  A strict expected payoff difference is used only to witness
that two already-defined output laws differ.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Literal Definition-2 law equality for the report-required hidden-access
source model.  The access side is the actual forced-report output law at a
fixed latent skill and public base; the no-access side is the actual no-report
point mass at that same public base. -/
def lg21HiddenAccessReportRequiredLatentSkillFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) : Prop :=
  ∀ skill publicBase,
    lg21HiddenAccessReportRequiredLatentAccessOutputLaw E skill publicBase =
      lg21HiddenAccessReportRequiredNoAccessOutputLaw E publicBase

/-- A source-attained taking type with a strict pre-score gain witnesses a
failure of literal latent-skill fairness.  The conclusion compares actual
output laws; no output-law equality is supplied by the caller. -/
theorem lg21HiddenAccessReportRequired_not_latentSkillFair_of_taking_strictExpectedGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature → ℝ)
    (htake : E.source.takeDecision skill publicBase = true)
    (hstrict : E.source.noReportPayoff publicBase <
      ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw skill publicBase) :
    ¬ lg21HiddenAccessReportRequiredLatentSkillFair E := by
  intro hfair
  exact (lg21HiddenAccessReportRequired_latentOutputLaw_ne_of_strictExpectedGain
    E skill publicBase htake hstrict) (hfair skill publicBase)

/-- The literal source factorization and local-tail stability make the
pre-score expected payoff strictly increasing on almost every public-base
fibre.  The selected-PBO identity is first obtained only on its attained
selected base law and is then transported only after positive selected fibres
have been proved. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.takeExpectedPayoff_strictMono_ae_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.source.takeDecision)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean baseVariance.toNNReal
    ∀ᵐ publicBase ∂baseLaw,
      StrictMono (fun latentSkill => ∫ score,
        E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase) := by
  intro skillKernel
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean baseVariance.toNNReal
  let action : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool :=
    fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
  let actionEvent : Set ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    lg21SourceLatentActionEvent action
  let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel)
    (lg21SourceLatentActionEvent_measurable action
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst)))
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel)
      (lg21SourceLatentActionEvent_measurable action
        (E.source.takeDecision_measurable.comp
          (measurable_snd.prodMk measurable_fst)))
  let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
    selectedSkillPatch (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch (M.noiseVariance testFeature : ℝ)
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using lg21SourceLatentActionEvent_measurable action haction
  have htakePositiveGlobal :=
    lg21HiddenAccess_reportRequired_positiveTake_of_literalSourceStability_clean
      M E.source.access_positive hnoAccess testFeature hpriorVariance
      hnonTestNoiseVariance htestNoiseVariance E.source hstable
  have hreporterPositive :=
    E.reporter_positive_of_positive_access_taking htakePositiveGlobal
  have htakeFibres : ∀ᵐ publicBase ∂baseLaw,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
    simpa [skillKernel, action, actionEvent] using
      (E.ae_positive_takeSelectionMass_of_localTailStability hnoAccess hstable
        baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
        hsourceFactor)
  have haccessFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
    calc
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (fun student =>
            (lg21HiddenAccessStudentBase testFeature student.2,
              (lg21HiddenAccessStudentScore testFeature student.2,
                lg21ContinuousPopulationSkill student))) =
          (lg21ContinuousGaussianPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
              simpa [lg21HiddenAccessBaseScoreSkillObservation] using
                (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                  M E.source.access_positive testFeature).symm
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) :=
        hsourceFactor
  have hselectedPBO :=
    E.reportedPayoff_eq_selectedGaussianPosteriorMean_ae_by_selectedBase_of_factorization
      baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) hbaseVariance htestNoiseVariance
      haccessFactor hreporterPositive
  have hselectedPositive : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel actionEvent,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
    exact ae_normalizedSelectedBase_positiveFibres hactionEvent
  have hstrictSelected : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel actionEvent,
      StrictMono (fun latentSkill => ∫ score,
        E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase) := by
    filter_upwards [hselectedPBO, hselectedPositive] with
      publicBase hPBO htakePositive
    let selected : Set ℝ :=
      {latentSkill | action publicBase latentSkill = true}
    have hselectedMeasurable : MeasurableSet selected := by
      change MeasurableSet ((action publicBase) ⁻¹' ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage
        (haction.comp (measurable_const.prodMk measurable_id))
    have hselectedPositive' : 0 < gaussianReal (baseMean publicBase)
        baseVariance.toNNReal selected := by
      apply pos_iff_ne_zero.mpr
      have htakePositive' : skillKernel publicBase
          (selectedFiber actionEvent publicBase) ≠ 0 := by
        simpa [selectionMass] using htakePositive
      have hfiber : selectedFiber actionEvent publicBase = selected := by
        ext latentSkill
        simp [selectedFiber, actionEvent, selected, lg21SourceLatentActionEvent]
      rw [hfiber] at htakePositive'
      rw [show skillKernel publicBase = gaussianReal (baseMean publicBase)
        baseVariance.toNNReal by rw [gaussianLocationKernel_apply]] at htakePositive'
      exact htakePositive'
    have hscoreLaw : (scoreSkillKernel.map Prod.fst) publicBase =
        normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) baseVariance
              (M.noiseVariance testFeature : ℝ))
          (Set.univ ×ˢ selected) := by
      simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel, selected] using
        (lg21_selectedAction_scoreLaw_eq_selectedGaussianScoreLaw_lawOnly
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) hbaseVariance htestNoiseVariance
          action haction publicBase htakePositive)
    have hPBOFixed : E.source.reportedPayoff publicBase =ᵐ[
        normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) baseVariance
              (M.noiseVariance testFeature : ℝ))
          (Set.univ ×ˢ selected)]
        fun score => ∫ latentSkill, latentSkill ∂
          lg21NormalizedRestriction
            (gaussianSignalPosteriorKernel
              (baseMean publicBase) baseVariance
                (M.noiseVariance testFeature : ℝ) score)
            selected := by
      rw [← hscoreLaw]
      simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel, action,
        selectedNormalizedKernel_apply
          (MeasurableSet.univ.prod hselectedMeasurable), selectedFiber, selected] using hPBO
    exact E.takeExpectedPayoff_strictMono_of_selectedGaussianPBO_ae
      publicBase (baseMean publicBase) baseVariance hbaseVariance htestNoiseVariance
      selected hselectedMeasurable hselectedPositive' hPBOFixed
  exact lg21_ae_base_of_ae_normalizedSelectedBase_of_ae_positiveFibres
    baseLaw skillKernel actionEvent hactionEvent hstrictSelected htakeFibres

/-- The source factorization, literal pre-score best response, and local-tail
stability supply an attained taking type with a strict expected gain.  This is
an existential source fact, not a chosen latent band made visible to the
school. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.exists_taking_strictExpectedGain_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.source.takeDecision)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    ∃ publicBase latentSkill,
      E.source.takeDecision latentSkill publicBase = true ∧
        E.source.noReportPayoff publicBase <
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase := by
  let skillKernel := gaussianLocationKernel
    baseMean hbaseMean baseVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean baseVariance.toNNReal
  let action : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool :=
    fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
  let actionEvent : Set ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    lg21SourceLatentActionEvent action
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using lg21SourceLatentActionEvent_measurable action haction
  have htakeFibres : ∀ᵐ publicBase ∂baseLaw,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
    simpa [skillKernel, action, actionEvent] using
      (E.ae_positive_takeSelectionMass_of_localTailStability hnoAccess hstable
        baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
        hsourceFactor)
  have hbest : ∀ᵐ publicBase ∂baseLaw,
      NoProfitableBinaryChoiceDeviationAE (skillKernel publicBase)
        (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
        (fun latentSkill => ∫ score,
          E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase)
        (fun _ => E.source.noReportPayoff publicBase) := by
    simpa [skillKernel] using
      (E.take_best_response_ae_by_base_of_sourceGaussianFactor
        baseLaw baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) hsourceFactor)
  have hstrict := E.takeExpectedPayoff_strictMono_ae_of_sourceGaussianFactor
    hnoAccess hstable hpriorVariance hnonTestNoiseVariance htestNoiseVariance
    baseLaw baseMean hbaseMean baseVariance hbaseVariance hsourceFactor
  have hgood : ∀ᵐ publicBase ∂baseLaw,
      selectionMass skillKernel actionEvent publicBase ≠ 0 ∧
        NoProfitableBinaryChoiceDeviationAE (skillKernel publicBase)
          (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
          (fun latentSkill => ∫ score,
            E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase)
          (fun _ => E.source.noReportPayoff publicBase) ∧
        StrictMono (fun latentSkill => ∫ score,
          E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase) := by
    filter_upwards [htakeFibres, hbest, hstrict] with publicBase
      htake hbest hstrict
    exact ⟨htake, hbest, hstrict⟩
  rcases hgood.exists with ⟨publicBase, htakePositive, hbestBase, hstrictBase⟩
  letI : NoAtoms (skillKernel publicBase) := by
    rw [show skillKernel publicBase = gaussianReal (baseMean publicBase)
      baseVariance.toNNReal by rw [gaussianLocationKernel_apply]]
    exact ProbabilityTheory.noAtoms_gaussianReal
      (ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance))
  have hchosenPositive : 0 < skillKernel publicBase
      {latentSkill | E.source.takeDecision latentSkill publicBase = true} := by
    apply pos_iff_ne_zero.mpr
    simpa [selectionMass, actionEvent, action, selectedFiber,
      lg21SourceLatentActionEvent] using htakePositive
  have hstrictChosen := lg21_positive_strictChosenGain_of_strictMono
    (skillKernel publicBase)
    (fun latentSkill => E.source.takeDecision latentSkill publicBase)
    (fun latentSkill => ∫ score,
      E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase)
    (E.source.noReportPayoff publicBase) hbestBase hstrictBase hchosenPositive
  have hnonempty : {latentSkill | E.source.takeDecision latentSkill publicBase = true ∧
      E.source.noReportPayoff publicBase <
        ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase}.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hempty
    rw [hempty, measure_empty] at hstrictChosen
    exact (ne_of_gt hstrictChosen) rfl
  rcases hnonempty with ⟨latentSkill, htake, hstrictGain⟩
  exact ⟨publicBase, latentSkill, htake, hstrictGain⟩

/-- Direct report-required Theorem-3.1 latent-law conclusion on the literal
source population.  Every ingredient is derived from the source equilibrium,
the Gaussian factorization, and the explicitly recorded positive-mass
local-tail stability refinement; no access/no-access output-law identity is a
premise. -/
theorem lg21HiddenAccessReportRequired_not_latentSkillFair_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.source.takeDecision)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    ¬ lg21HiddenAccessReportRequiredLatentSkillFair E := by
  rcases E.exists_taking_strictExpectedGain_of_sourceGaussianFactor
    hnoAccess hstable hpriorVariance hnonTestNoiseVariance htestNoiseVariance
    baseLaw baseMean hbaseMean baseVariance hbaseVariance hsourceFactor with
      ⟨publicBase, latentSkill, htake, hstrictGain⟩
  exact lg21HiddenAccessReportRequired_not_latentSkillFair_of_taking_strictExpectedGain
    E latentSkill publicBase htake hstrictGain

end

end LG21TestOptionalPolicies
