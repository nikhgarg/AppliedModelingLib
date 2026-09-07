import LG21TestOptionalPolicies.SelectedGaussianSourcePosterior
import LG21TestOptionalPolicies.SelectedGaussianSignalActionTransport

/-!
# Gaussian source laws after a latent action

This file is source-law infrastructure.  A Boolean action is represented only
by its measurable event in `(public base, latent skill)` space.  The results
do not mention a payoff, an equilibrium, a PBO, or an observed latent band.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The latent base--skill event selected by a Boolean source action. -/
def lg21SourceLatentActionEvent
    {Base : Type*} (action : Base -> ℝ -> Bool) : Set (Base × ℝ) :=
  {baseSkill | action baseSkill.1 baseSkill.2 = true}

theorem lg21SourceLatentActionEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (action : Base -> ℝ -> Bool)
    (haction : Measurable (fun baseSkill : Base × ℝ =>
      action baseSkill.1 baseSkill.2)) :
    MeasurableSet (lg21SourceLatentActionEvent action) := by
  change MeasurableSet
    ((fun baseSkill : Base × ℝ => action baseSkill.1 baseSkill.2) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage haction

/--
Selecting a Gaussian source population through an arbitrary measurable
pre-score action, then drawing the signal, factors over the selected public
base law.  The action is retained only as a measurable event; no action shape
or posterior formula is assumed.
-/
theorem lg21_source_selectedAction_base_score_factor_lawOnly
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (action : Base -> ℝ -> Bool)
    (haction : Measurable (fun baseSkill : Base × ℝ =>
      action baseSkill.1 baseSkill.2)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let actionEvent : Set (Base × ℝ) := lg21SourceLatentActionEvent action
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (lg21SourceLatentActionEvent_measurable action haction)
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov
        (κ := skillKernel)
        (lg21SourceLatentActionEvent_measurable action haction)
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov
        selectedSkillPatch noiseVariance
    let selectedLaw := lg21NormalizedRestriction sourceLaw
      {omega | action (base omega) (skill omega) = true}
    let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
      ((base omega, score omega), skill omega)
    selectedLaw.map observationSkill =
      (normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel).map
        MeasurableEquiv.prodAssoc.symm := by
  intro skillKernel actionEvent selectedSkillPatch scoreSkillKernel selectedLaw
    observationSkill
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using
      (lg21SourceLatentActionEvent_measurable action haction)
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) hactionEvent
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch noiseVariance
  let sourceActionEvent : Set Omega :=
    {omega | action (base omega) (skill omega) = true}
  let rawObservationSkill : Omega -> Base × (ℝ × ℝ) := fun omega =>
    (base omega, (score omega, skill omega))
  let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  have hsourceActionEvent : sourceActionEvent =
      (fun omega => (base omega, skill omega)) ⁻¹' actionEvent := by
    rfl
  have hrawObservationSkill : Measurable rawObservationSkill :=
    hbase.prodMk (hscore.prodMk hskill)
  have hobservationSkill : Measurable observationSkill :=
    (hbase.prodMk hscore).prodMk hskill
  have hassociation : Measurable association := MeasurableEquiv.measurable _
  letI : SFinite (selectedBase baseLaw skillKernel actionEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel actionEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hselectedBaseSkill :
      lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) actionEvent =
        normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ
          selectedSkillPatch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := baseLaw) (κ := skillKernel) hactionEvent
  have hrawObservation : sourceLaw.map observationSkill =
      gaussianSignalExtendBaseLatentLaw
        (baseLaw ⊗ₘ skillKernel) noiseVariance := by
    have hrawExtension :
        gaussianSignalExtendBaseLatentLaw (baseLaw ⊗ₘ skillKernel) noiseVariance =
          gaussianSignalBaseScoreLatentLaw
            baseLaw baseMean hbaseMean priorVariance noiseVariance := by
      exact gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        (baseLaw ⊗ₘ skillKernel) (by rfl)
    calc
      sourceLaw.map observationSkill =
          (sourceLaw.map rawObservationSkill).map association := by
            rw [Measure.map_map hassociation hrawObservationSkill]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance).map association := by
            rw [show sourceLaw.map rawObservationSkill =
              baseLaw ⊗ₘ gaussianSignalJointKernel
                baseMean hbaseMean priorVariance noiseVariance by
              simpa [rawObservationSkill] using hsourceFactor]
      _ = gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance := by
            rfl
      _ = gaussianSignalExtendBaseLatentLaw
          (baseLaw ⊗ₘ skillKernel) noiseVariance := hrawExtension.symm
  have hselectedExtension :
      gaussianSignalExtendBaseLatentLaw
        (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) actionEvent)
        noiseVariance =
      (normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel).map
        MeasurableEquiv.prodAssoc.symm := by
    rw [hselectedBaseSkill]
    simpa [scoreSkillKernel] using
      (gaussianSignalExtendBaseLatentLaw_compProd
        (normalizedSelectedBase baseLaw skillKernel actionEvent)
        selectedSkillPatch noiseVariance)
  have hselectionExtension :
      selectedLaw.map observationSkill =
        gaussianSignalExtendBaseLatentLaw
          (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) actionEvent)
          noiseVariance := by
    let extendedActionEvent : Set ((Base × ℝ) × ℝ) :=
      gaussianSignalExtendedSelectionEvent actionEvent
    have hextendedActionEvent : MeasurableSet extendedActionEvent := by
      exact hactionEvent.preimage (by fun_prop)
    have hsourcePreimage : sourceActionEvent =
        observationSkill ⁻¹' extendedActionEvent := by
      rfl
    calc
      selectedLaw.map observationSkill =
          (lg21NormalizedRestriction sourceLaw sourceActionEvent).map
            observationSkill := by rfl
      _ = lg21NormalizedRestriction (sourceLaw.map observationSkill)
          extendedActionEvent := by
            rw [hsourcePreimage]
            exact lg21_normalizedRestriction_map_preimage sourceLaw observationSkill
              hobservationSkill extendedActionEvent hextendedActionEvent
      _ = lg21NormalizedRestriction
          (gaussianSignalExtendBaseLatentLaw
            (baseLaw ⊗ₘ skillKernel) noiseVariance) extendedActionEvent := by
            rw [hrawObservation]
      _ = gaussianSignalExtendBaseLatentLaw
          (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) actionEvent)
          noiseVariance := by
            simpa [extendedActionEvent] using
              (normalizedRestriction_gaussianSignalExtendBaseLatentLaw
                (baseLaw ⊗ₘ skillKernel) noiseVariance actionEvent hactionEvent)
  exact hselectionExtension.trans hselectedExtension

/--
On a base whose selected latent fibre has positive Gaussian mass, the
selected score marginal is the ordinary Gaussian score/posterior law
restricted by that same action fibre.  This is a local law identity, not a
pointwise belief assignment.
-/
theorem lg21_selectedAction_scoreLaw_eq_selectedGaussianScoreLaw_lawOnly
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (action : Base -> ℝ -> Bool)
    (haction : Measurable (fun baseSkill : Base × ℝ =>
      action baseSkill.1 baseSkill.2))
    (publicBase : Base)
    (hactionPositive : selectionMass
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21SourceLatentActionEvent action) publicBase ≠ 0) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let actionEvent : Set (Base × ℝ) := lg21SourceLatentActionEvent action
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (lg21SourceLatentActionEvent_measurable action haction)
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    (scoreSkillKernel.map Prod.fst) publicBase =
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill | action publicBase latentSkill = true}) := by
  intro skillKernel actionEvent selectedSkillPatch scoreSkillKernel
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using
      (lg21SourceLatentActionEvent_measurable action haction)
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) hactionEvent
  let priorLaw : Measure ℝ := gaussianReal (baseMean publicBase)
    priorVariance.toNNReal
  let selected : Set ℝ := {latentSkill | action publicBase latentSkill = true}
  let scoreLaw : Measure ℝ := gaussianReal (baseMean publicBase)
    (priorVariance + noiseVariance).toNNReal
  let posterior : Kernel ℝ ℝ := gaussianSignalPosteriorKernel
    (baseMean publicBase) priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let stage : ℝ × ℝ -> ℝ × ℝ :=
    fun skillNoise => (skillNoise.1 + skillNoise.2, skillNoise.1)
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((action publicBase) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (haction.comp (measurable_const.prodMk measurable_id))
  have hselectedPatch : selectedSkillPatch publicBase =
      lg21NormalizedRestriction priorLaw selected := by
    rw [selectedNormalizedKernelAtPositiveFibres_apply_pos
      (κ := skillKernel) hactionEvent publicBase]
    · rw [selectedNormalizedKernel_apply hactionEvent]
      rw [gaussianLocationKernel_apply]
      congr 1
    · simpa [skillKernel, actionEvent] using hactionPositive
  have hstage : Measurable stage := by
    dsimp [stage]
    fun_prop
  have hscoreSkill : scoreSkillKernel publicBase =
      ((lg21NormalizedRestriction priorLaw selected).prod noiseLaw).map stage := by
    rw [show scoreSkillKernel publicBase =
      ((selectedSkillPatch publicBase).prod noiseLaw).map stage by
        unfold scoreSkillKernel gaussianSignalJointKernelOfLatentKernel
        rw [Kernel.map_apply _ hstage, Kernel.prod_apply, Kernel.const_apply]]
    rw [hselectedPatch]
  have hselectedJoint : lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event =
      ((lg21NormalizedRestriction priorLaw selected).prod noiseLaw).map stage := by
    simpa [priorLaw, scoreLaw, posterior, event, noiseLaw, stage] using
      (normalizedRestriction_gaussianSignal_scoreLatent
        (baseMean publicBase) priorVariance noiseVariance selected
        hpriorVariance hnoiseVariance hselectedMeasurable)
  have hfirst : (lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event).map
      Prod.fst = normalizedSelectedBase scoreLaw posterior event := by
    letI : IsMarkovKernel posterior :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    exact normalizedRestriction_map_fst_eq_normalizedSelectedBase
      (μ := scoreLaw) (κ := posterior)
      (MeasurableSet.univ.prod hselectedMeasurable)
  calc
    (scoreSkillKernel.map Prod.fst) publicBase =
        (scoreSkillKernel publicBase).map Prod.fst := by
          rw [Kernel.map_apply _ measurable_fst]
    _ = (lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event).map Prod.fst := by
          rw [hscoreSkill, hselectedJoint]
    _ = normalizedSelectedBase scoreLaw posterior event := hfirst

/--
The positive-fibre patched posterior used in the global action factor agrees
with the fixed-base selected Gaussian posterior.  The equality follows from
the actual action event and does not make the school observe the latent skill.
-/
theorem lg21_selectedAction_posteriorPatch_eq_fixedSelectedGaussian_lawOnly
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (action : Base -> ℝ -> Bool)
    (haction : Measurable (fun baseSkill : Base × ℝ =>
      action baseSkill.1 baseSkill.2))
    (publicBase : Base) (observedScore : ℝ)
    (hactionPositive : selectionMass
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21SourceLatentActionEvent action) publicBase ≠ 0) :
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let reportEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | action observationSkill.1.1 observationSkill.2 = true}
    let fixedPosterior : Kernel ℝ ℝ := gaussianSignalPosteriorKernel
      (baseMean publicBase) priorVariance noiseVariance
    letI : IsMarkovKernel fixedPosterior :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    let patch := selectedNormalizedKernelAtPositiveFibres
      (κ := posteriorKernel)
      (by
        change MeasurableSet
          ((fun observationSkill : (Base × ℝ) × ℝ =>
            action observationSkill.1.1 observationSkill.2) ⁻¹'
              ({true} : Set Bool))
        exact (measurableSet_singleton true).preimage
          (haction.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    patch (publicBase, observedScore) =
      selectedNormalizedKernel fixedPosterior
        (Set.univ ×ˢ {latentSkill | action publicBase latentSkill = true})
        observedScore := by
  intro posteriorKernel reportEvent fixedPosterior patch
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        action observationSkill.1.1 observationSkill.2) ⁻¹'
          ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (haction.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let selected : Set ℝ := {latentSkill | action publicBase latentSkill = true}
  let fixedEvent : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  letI : IsMarkovKernel fixedPosterior :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  have hselectionMass : selectionMass skillKernel
      (lg21SourceLatentActionEvent action) publicBase =
      gaussianReal (baseMean publicBase) priorVariance.toNNReal selected := by
    rw [selectionMass, gaussianLocationKernel_apply]
    congr 1
  have hpriorSelected : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal selected := by
    rw [← hselectionMass]
    exact pos_iff_ne_zero.mpr hactionPositive
  have hposteriorPositive : selectionMass posteriorKernel reportEvent
      (publicBase, observedScore) ≠ 0 := by
    change posteriorKernel (publicBase, observedScore)
      (selectedFiber reportEvent (publicBase, observedScore)) ≠ 0
    rw [gaussianSignalPosteriorBaseKernel_apply]
    have hfiber : selectedFiber reportEvent (publicBase, observedScore) = selected := by
      ext latentSkill
      simp [selectedFiber, reportEvent, selected]
    rw [hfiber]
    have hpositive := lg21_gaussianSignalPosterior_selected_pos
      (baseMean publicBase) priorVariance noiseVariance selected
      hpriorVariance hnoiseVariance hpriorSelected observedScore
    simpa only [gaussianSignalPosteriorKernel_apply] using ne_of_gt hpositive
  change selectedNormalizedKernelAtPositiveFibres
      (κ := posteriorKernel) hreportEvent (publicBase, observedScore) =
    selectedNormalizedKernel fixedPosterior fixedEvent observedScore
  rw [selectedNormalizedKernelAtPositiveFibres_apply_pos
    (κ := posteriorKernel) hreportEvent (publicBase, observedScore)
    hposteriorPositive]
  rw [selectedNormalizedKernel_apply hreportEvent]
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((fun latentSkill : ℝ =>
      action publicBase latentSkill) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (haction.comp (measurable_const.prodMk measurable_id))
  rw [selectedNormalizedKernel_apply
    (MeasurableSet.univ.prod hselectedMeasurable)]
  rw [gaussianSignalPosteriorBaseKernel_apply]
  congr 1
  · rw [gaussianSignalPosteriorKernel_apply]
  · ext latentSkill
    simp [selectedFiber, reportEvent, fixedEvent, selected]

/--
The unpatched selected posterior itself has the same fixed-base form.  Unlike
the patched version this identity is meaningful as an equality of normalized
restrictions even at a zero selected fibre; later payoff uses remain scoped to
attained positive fibres.
-/
theorem lg21_selectedAction_selectedPosterior_eq_fixedSelectedGaussian_lawOnly
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (action : Base -> ℝ -> Bool)
    (haction : Measurable (fun baseSkill : Base × ℝ =>
      action baseSkill.1 baseSkill.2))
    (publicBase : Base) (observedScore : ℝ) :
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let reportEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | action observationSkill.1.1 observationSkill.2 = true}
    let fixedPosterior : Kernel ℝ ℝ := gaussianSignalPosteriorKernel
      (baseMean publicBase) priorVariance noiseVariance
    letI : IsMarkovKernel fixedPosterior :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    selectedNormalizedKernel posteriorKernel reportEvent
      (publicBase, observedScore) =
      selectedNormalizedKernel fixedPosterior
        (Set.univ ×ˢ {latentSkill | action publicBase latentSkill = true})
        observedScore := by
  intro posteriorKernel reportEvent fixedPosterior
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel fixedPosterior :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        action observationSkill.1.1 observationSkill.2) ⁻¹'
          ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (haction.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let selected : Set ℝ := {latentSkill | action publicBase latentSkill = true}
  let fixedEvent : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((action publicBase) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (haction.comp (measurable_const.prodMk measurable_id))
  rw [selectedNormalizedKernel_apply hreportEvent]
  rw [selectedNormalizedKernel_apply
    (MeasurableSet.univ.prod hselectedMeasurable)]
  rw [gaussianSignalPosteriorBaseKernel_apply]
  congr 1
  · rw [gaussianSignalPosteriorKernel_apply]
  · ext latentSkill
    simp [selectedFiber, reportEvent, fixedEvent, selected]

end

end LG21TestOptionalPolicies
