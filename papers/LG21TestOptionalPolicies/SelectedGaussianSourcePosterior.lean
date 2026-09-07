import AppliedModelingLib.Foundations.Probability.GaussianSignalRCD
import AppliedModelingLib.Foundations.Probability.GaussianSignalKernelRCD
import LG21TestOptionalPolicies.SelectedConditionalPositiveFibresRCD
import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge

/-!
# Selected Gaussian source posterior

This is source-law infrastructure only.  It disintegrates a Gaussian
base/score/skill law after an arbitrary measurable latent action selection.
It does not import an equilibrium carrier, a PBO predicate, or a strategy
adapter.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/--
Conditioning a factorized Gaussian source law on a measurable latent action
gives the selected Gaussian posterior almost everywhere at the attained
observable `(base, score)`.  The conclusion is entirely law-level: no payoff,
equilibrium, or off-path public branch occurs in its statement.
-/
theorem lg21_source_taker_condDistrib_eq_selectedGaussianPosterior_ae_lawOnly
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (take : Base -> ℝ -> Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (htakePositive : 0 < sourceLaw
      {omega | take (base omega) (skill omega) = true}) :
    let scoreKernel := gaussianLocationKernel
      baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let takeEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | take observationSkill.1.1 observationSkill.2 = true}
    let takerLaw := lg21NormalizedRestriction sourceLaw
      {omega | take (base omega) (skill omega) = true}
    letI : IsProbabilityMeasure takerLaw :=
      lg21NormalizedRestriction_isProbability sourceLaw
        {omega | take (base omega) (skill omega) = true}
        (ne_of_gt htakePositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
    ∀ᵐ omega ∂takerLaw,
      condDistrib skill (fun omega => (base omega, score omega)) takerLaw
          (base omega, score omega) =
        selectedNormalizedKernel posteriorKernel takeEvent
          (base omega, score omega) := by
  intro scoreKernel posteriorKernel takeEvent takerLaw
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov
      baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability sourceLaw
      {omega | take (base omega) (skill omega) = true}
      (ne_of_gt htakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  let observedLaw : Measure (Base × ℝ) := baseLaw ⊗ₘ scoreKernel
  let observation : Omega -> Base × ℝ := fun omega => (base omega, score omega)
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    (observation omega, skill omega)
  let sourceTakeEvent : Set Omega :=
    {omega | take (base omega) (skill omega) = true}
  have htakeEvent : MeasurableSet takeEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        take observationSkill.1.1 observationSkill.2) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hobservationSkill : Measurable observationSkill :=
    hobservation.prodMk hskill
  have hsourceTakeEvent : sourceTakeEvent = observationSkill ⁻¹' takeEvent := by
    rfl
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := posteriorKernel) htakeEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := posteriorKernel) htakeEvent
  letI : SFinite (selectedBase observedLaw posteriorKernel takeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel takeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hrawFactor : sourceLaw.map observationSkill =
      observedLaw ⊗ₘ posteriorKernel := by
    let rawObservationSkill : Omega -> Base × (ℝ × ℝ) := fun omega =>
      (base omega, (score omega, skill omega))
    let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
      MeasurableEquiv.prodAssoc.symm
    have hrawObservationSkill : Measurable rawObservationSkill :=
      hbase.prodMk (hscore.prodMk hskill)
    have hassociation : Measurable association := MeasurableEquiv.measurable _
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
      _ = observedLaw ⊗ₘ posteriorKernel := by
            simpa [observedLaw, scoreKernel, posteriorKernel] using
              (gaussianSignalBaseScoreLatentLaw_factorization
                baseLaw baseMean hbaseMean priorVariance noiseVariance
                hpriorVariance hnoiseVariance)
  have hselectedPair : takerLaw.map observationSkill =
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) takeEvent := by
    calc
      takerLaw.map observationSkill =
          (lg21NormalizedRestriction sourceLaw sourceTakeEvent).map
            observationSkill := by rfl
      _ = lg21NormalizedRestriction (sourceLaw.map observationSkill) takeEvent := by
        rw [hsourceTakeEvent]
        exact lg21_normalizedRestriction_map_preimage sourceLaw observationSkill
          hobservationSkill takeEvent htakeEvent
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) takeEvent := by
        rw [hrawFactor]
  have hselectedFactor :
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) takeEvent =
        normalizedSelectedBase observedLaw posteriorKernel takeEvent ⊗ₘ patch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := observedLaw) (κ := posteriorKernel) htakeEvent
  have htakerObservationLaw : takerLaw.map observation =
      normalizedSelectedBase observedLaw posteriorKernel takeEvent := by
    calc
      takerLaw.map observation =
          (takerLaw.map observationSkill).map Prod.fst := by
            rw [Measure.map_map measurable_fst hobservationSkill]
            rfl
      _ = (lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
          takeEvent).map Prod.fst := by rw [hselectedPair]
      _ = (normalizedSelectedBase observedLaw posteriorKernel takeEvent ⊗ₘ patch).map
          Prod.fst := by rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel takeEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint : takerLaw.map observationSkill =
      takerLaw.map observation ⊗ₘ patch := by
    rw [hselectedPair, hselectedFactor, htakerObservationLaw]
  have hcondDistrib : condDistrib skill observation takerLaw =ᵐ[
      takerLaw.map observation] patch := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation hskill hselectedJoint
  have hpatch : patch =ᵐ[takerLaw.map observation]
      selectedNormalizedKernel posteriorKernel takeEvent := by
    rw [htakerObservationLaw]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := observedLaw) (κ := posteriorKernel) htakeEvent
  have hcondDistribSelected : condDistrib skill observation takerLaw =ᵐ[
      takerLaw.map observation]
      selectedNormalizedKernel posteriorKernel takeEvent := hcondDistrib.trans hpatch
  exact ae_of_ae_map hobservation.aemeasurable hcondDistribSelected

end

end LG21TestOptionalPolicies
