import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredActionClassification
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralPBOBridge
import LG21TestOptionalPolicies.SemanticActionCutoff

/-!
# Literal finite-cutoff endpoint for report-required LG21

This file combines only literal source best responses, the actual selected
public PBO, and the Gaussian source law.  The finite-cutoff conclusion keeps
its necessary fibrewise crossing condition explicit: positive action mass in
the aggregate does not imply that every public-base fibre contains both
actions.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Generic semantic binary-choice bridge -/

/-- A strictly monotone real payoff has a null tie level under an atomless
law.  This uses no continuity or pre-chosen cutoff. -/
theorem lg21_strictMono_tieLevel_null
    (law : Measure ℝ) [NoAtoms law]
    (payoff : ℝ -> ℝ) (hstrict : StrictMono payoff) (outside : ℝ) :
    law {skill | payoff skill = outside} = 0 := by
  by_cases hroot : ∃ cutoff, payoff cutoff = outside
  · rcases hroot with ⟨cutoff, hcutoff⟩
    refine measure_mono_null ?_ (measure_singleton cutoff)
    intro skill hskill
    rw [Set.mem_singleton_iff]
    apply hstrict.injective
    rw [hskill, hcutoff]
  · have hempty : {skill | payoff skill = outside} = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨skill, hskill⟩
      exact hroot ⟨skill, hskill⟩
    rw [hempty, measure_empty]

/-- The actual a.e. best response equals the semantic weak-payoff comparison
when strict monotonicity removes its tie level. -/
theorem lg21_bool_choice_eq_semanticUpper_ae_of_strictMono
    (law : Measure ℝ) [NoAtoms law]
    (decision : ℝ -> Bool) (takePayoff : ℝ -> ℝ) (outside : ℝ)
    (hbest : NoProfitableBinaryChoiceDeviationAE law
      (fun skill => decision skill = true) takePayoff (fun _ => outside))
    (hstrict : StrictMono takePayoff) :
    ∀ᵐ skill ∂law,
      decision skill = decide (outside ≤ takePayoff skill) := by
  apply bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
    decision hbest
  · intro skill
    rfl
  · exact lg21_strictMono_tieLevel_null law takePayoff hstrict outside

/-- The semantic weak-payoff decision of a strictly increasing take payoff is
an exactly upper-closed Boolean action, independently of how the literal
strategy is represented away from its a.e. best-response set. -/
theorem lg21_semanticUpper_upperClosed_of_strictMono
    (takePayoff : ℝ -> ℝ) (outside : ℝ)
    (hstrict : StrictMono takePayoff) :
    ∀ ⦃low high : ℝ⦄,
      low ≤ high ->
        decide (outside ≤ takePayoff low) = true ->
          decide (outside ≤ takePayoff high) = true := by
  intro low high hlowHigh hlow
  simp only [decide_eq_true_eq] at hlow ⊢
  exact hlow.trans (hstrict.monotone hlowHigh)

/-- Positive mass on both literal actions supplies the two semantic payoff
signs needed for a finite cutoff.  The second action cannot be supported only
on a tie because strict monotonicity makes that level atomless-null. -/
theorem lg21_semanticCross_of_positive_action_masses
    (law : Measure ℝ) [NoAtoms law]
    (decision : ℝ -> Bool) (takePayoff : ℝ -> ℝ) (outside : ℝ)
    (hbest : NoProfitableBinaryChoiceDeviationAE law
      (fun skill => decision skill = true) takePayoff (fun _ => outside))
    (hstrict : StrictMono takePayoff)
    (htake : 0 < law {skill | decision skill = true})
    (hnoTake : 0 < law {skill | decision skill = false}) :
    (∃ skill, outside ≤ takePayoff skill) ∧
      ∃ skill, ¬ outside ≤ takePayoff skill := by
  constructor
  · by_contra hnone
    push Not at hnone
    have hbadZero : law {skill |
        ¬ (decision skill = true -> outside ≤ takePayoff skill)} = 0 :=
      ae_iff.mp hbest.1
    have hsubset : {skill | decision skill = true} ⊆ {skill |
        ¬ (decision skill = true -> outside ≤ takePayoff skill)} := by
      intro skill hchoose hgood
      exact (not_le_of_gt (hnone skill)) (hgood hchoose)
    have hzero : law {skill | decision skill = true} = 0 :=
      measure_mono_null hsubset hbadZero
    exact (ne_of_gt htake) hzero
  · by_contra hnone
    push Not at hnone
    have hbadZero : law {skill |
        ¬ (¬ decision skill = true -> takePayoff skill ≤ outside)} = 0 :=
      ae_iff.mp hbest.2
    have htieZero : law {skill | takePayoff skill = outside} = 0 :=
      lg21_strictMono_tieLevel_null law takePayoff hstrict outside
    have hsubset : {skill | decision skill = false} ⊆
        {skill | ¬ (¬ decision skill = true -> takePayoff skill ≤ outside)} ∪
          {skill | takePayoff skill = outside} := by
      intro skill hnoTake
      by_cases hbad : ¬ (¬ decision skill = true -> takePayoff skill ≤ outside)
      · exact Or.inl hbad
      · right
        have hnotChoose : ¬ decision skill = true := by
          intro hchoose
          rw [hnoTake] at hchoose
          simp at hchoose
        have hle : takePayoff skill ≤ outside := by
          exact (not_not.mp hbad) hnotChoose
        exact le_antisymm hle (hnone skill)
    have hunionZero : law
        ({skill | ¬ (¬ decision skill = true -> takePayoff skill ≤ outside)} ∪
          {skill | takePayoff skill = outside}) = 0 :=
      measure_union_null hbadZero htieZero
    have hzero : law {skill | decision skill = false} = 0 :=
      measure_mono_null hsubset hunionZero
    exact (ne_of_gt hnoTake) hzero

/-! ## Literal source endpoint -/

/--
The literal forced-report source model has a finite latent-skill taking
cutoff on every selected public-base fibre where the semantic take payoff
crosses the no-report payoff.  The crossing premise is deliberately
fibrewise: aggregate positive take and no-take mass does not establish it.

The posterior used here is recalibrated over the actual observable taking
branch.  In particular, this theorem does not condition a PBO on a latent
high or low band.
-/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.exists_finite_takeCutoff_ae_by_selectedBase_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
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
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
        E.source.reportDecision)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let action : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
      fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
    let actionEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
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
    (∀ᵐ publicBase ∂baseLaw,
      0 < skillKernel publicBase
        {latentSkill | action publicBase latentSkill = false}) ->
    ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw skillKernel actionEvent,
      ∃ cutoff : ℝ,
        ∀ᵐ latentSkill ∂skillKernel publicBase,
          E.source.takeDecision latentSkill publicBase =
            decide (cutoff ≤ latentSkill) := by
  intro skillKernel action actionEvent selectedSkillPatch scoreSkillKernel
    hnoTakeFibres
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using
      lg21SourceLatentActionEvent_measurable action haction
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) hactionEvent
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch (M.noiseVariance testFeature : ℝ)
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  have haccessFactor : accessLaw.map
      (fun student =>
        (lg21HiddenAccessStudentBase testFeature student.2,
          (lg21HiddenAccessStudentScore testFeature student.2,
            lg21ContinuousPopulationSkill student))) =
      baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ) := by
    calc
      accessLaw.map
          (fun student =>
            (lg21HiddenAccessStudentBase testFeature student.2,
              (lg21HiddenAccessStudentScore testFeature student.2,
                lg21ContinuousPopulationSkill student))) =
          (lg21ContinuousGaussianPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
              simpa [accessLaw, lg21HiddenAccessBaseScoreSkillObservation] using
                (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                  M E.source.access_positive testFeature).symm
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ) :=
        hsourceFactor
  have hbaseSkillFactor :
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap =
        baseLaw ⊗ₘ skillKernel := by
    simpa [skillKernel] using
      (lg21HiddenAccessAccessLatentBaseLaw_swap_eq_gaussianLocation_of_scoreFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        priorVariance (M.noiseVariance testFeature : ℝ) hsourceFactor)
  have hbestBase : ∀ᵐ publicBase ∂baseLaw,
      NoProfitableBinaryChoiceDeviationAE (skillKernel publicBase)
        (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
        (fun latentSkill => ∫ score,
          E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase)
        (fun _ => E.source.noReportPayoff publicBase) := by
    exact E.take_best_response_ae_by_base_of_factorization
      baseLaw skillKernel hbaseSkillFactor
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel actionEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  have hselectedBaseAC : normalizedSelectedBase baseLaw skillKernel actionEvent ≪
      baseLaw := by
    change ((baseLaw ⊗ₘ skillKernel) actionEvent)⁻¹ •
        baseLaw.withDensity (selectionMass skillKernel actionEvent) ≪ baseLaw
    exact Measure.smul_absolutelyContinuous.trans
      (withDensity_absolutelyContinuous _ _)
  have hbestSelected := hselectedBaseAC.ae_le hbestBase
  have hnoTakeSelected := hselectedBaseAC.ae_le hnoTakeFibres
  have hselectedPBO :=
    E.reportedPayoff_eq_selectedGaussianPosteriorMean_ae_by_selectedBase_of_factorization
      baseLaw baseMean hbaseMean priorVariance
      (M.noiseVariance testFeature : ℝ) hpriorVariance hnoiseVariance
      haccessFactor hreporterPositive
  have hselectedPositive : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel actionEvent,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
    exact ae_normalizedSelectedBase_positiveFibres hactionEvent
  filter_upwards [hbestSelected, hselectedPBO, hselectedPositive,
    hnoTakeSelected] with publicBase hbest hPBO htakePositive hnoTakePositive
  let selected : Set ℝ :=
    {latentSkill | action publicBase latentSkill = true}
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((action publicBase) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (haction.comp (measurable_const.prodMk measurable_id))
  have hselectedPositive' : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal selected := by
    apply pos_iff_ne_zero.mpr
    have htakePositive' : skillKernel publicBase
        (selectedFiber actionEvent publicBase) ≠ 0 := by
      simpa [selectionMass] using htakePositive
    have hfiber : selectedFiber actionEvent publicBase = selected := by
      ext latentSkill
      simp [selectedFiber, actionEvent, selected, lg21SourceLatentActionEvent]
    rw [hfiber] at htakePositive'
    rw [show skillKernel publicBase = gaussianReal (baseMean publicBase)
      priorVariance.toNNReal by rw [gaussianLocationKernel_apply]] at htakePositive'
    exact htakePositive'
  have hscoreLaw : (scoreSkillKernel.map Prod.fst) publicBase =
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance
            (M.noiseVariance testFeature : ℝ))
        (Set.univ ×ˢ selected) := by
    simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel, selected] using
      (lg21_selectedAction_scoreLaw_eq_selectedGaussianScoreLaw_lawOnly
        baseLaw baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ) hpriorVariance hnoiseVariance
        action haction publicBase htakePositive)
  have hPBOFixed : E.source.reportedPayoff publicBase =ᵐ[
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance
            (M.noiseVariance testFeature : ℝ))
        (Set.univ ×ˢ selected)]
      fun score => ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance
              (M.noiseVariance testFeature : ℝ) score)
          selected := by
    rw [← hscoreLaw]
    simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel, action,
      selectedNormalizedKernel_apply
        (MeasurableSet.univ.prod hselectedMeasurable), selectedFiber, selected] using hPBO
  have hstrict := E.takeExpectedPayoff_strictMono_of_selectedGaussianPBO_ae
    publicBase (baseMean publicBase) priorVariance hpriorVariance hnoiseVariance
    selected hselectedMeasurable hselectedPositive' hPBOFixed
  letI : NoAtoms (skillKernel publicBase) := by
    rw [show skillKernel publicBase = gaussianReal (baseMean publicBase)
      priorVariance.toNNReal by rw [gaussianLocationKernel_apply]]
    exact ProbabilityTheory.noAtoms_gaussianReal
      (ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance))
  have htakeMass : 0 < skillKernel publicBase
      {latentSkill | E.source.takeDecision latentSkill publicBase = true} := by
    simpa [skillKernel, selected, action, gaussianLocationKernel_apply] using
      hselectedPositive'
  have hnoTakeMass : 0 < skillKernel publicBase
      {latentSkill | E.source.takeDecision latentSkill publicBase = false} := by
    simpa only [action] using hnoTakePositive
  have hcross :
      (∃ latentSkill,
        E.source.noReportPayoff publicBase ≤
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase) ∧
        ∃ latentSkill,
          ¬ E.source.noReportPayoff publicBase ≤
            ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase := by
    exact lg21_semanticCross_of_positive_action_masses
      (skillKernel publicBase)
      (fun latentSkill => E.source.takeDecision latentSkill publicBase)
      (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase)
      (E.source.noReportPayoff publicBase) hbest hstrict htakeMass hnoTakeMass
  have hsemantic : ∀ᵐ latentSkill ∂skillKernel publicBase,
      E.source.takeDecision latentSkill publicBase =
        decide (E.source.noReportPayoff publicBase ≤
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase) := by
    exact lg21_bool_choice_eq_semanticUpper_ae_of_strictMono
      (skillKernel publicBase)
      (fun latentSkill => E.source.takeDecision latentSkill publicBase)
      (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase)
      (E.source.noReportPayoff publicBase) hbest hstrict
  have hupper : ∀ ⦃low high : ℝ⦄,
      low ≤ high ->
        decide (E.source.noReportPayoff publicBase ≤
          ∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw low publicBase) = true ->
          decide (E.source.noReportPayoff publicBase ≤
            ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw high publicBase) = true := by
    exact lg21_semanticUpper_upperClosed_of_strictMono
      (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase)
      (E.source.noReportPayoff publicBase) hstrict
  have hsemanticTrue : ∃ latentSkill,
      decide (E.source.noReportPayoff publicBase ≤
        ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase) = true := by
    rcases hcross.1 with ⟨latentSkill, hgain⟩
    exact ⟨latentSkill, by simpa using hgain⟩
  have hsemanticFalse : ∃ latentSkill,
      decide (E.source.noReportPayoff publicBase ≤
        ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase) = false := by
    rcases hcross.2 with ⟨latentSkill, hgain⟩
    exact ⟨latentSkill, by simp [hgain]⟩
  rcases lg21_bool_choice_eq_decide_upperTail_ae_of_upperClosed_nontrivial
      (skillKernel publicBase)
      (fun latentSkill => decide (E.source.noReportPayoff publicBase ≤
        ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase))
      hupper hsemanticTrue hsemanticFalse with ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, ?_⟩
  filter_upwards [hsemantic, hcutoff] with latentSkill hactual hsemanticCutoff
  rw [hactual, hsemanticCutoff]

end

end LG21TestOptionalPolicies
