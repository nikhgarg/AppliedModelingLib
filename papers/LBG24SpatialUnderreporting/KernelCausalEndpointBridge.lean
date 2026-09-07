import LBG24SpatialUnderreporting.StationaryPalmCausalEndpointBridge
import LBG24SpatialUnderreporting.KernelCausalResponseLaw

/-!
# Kernel-valued causal endpoint response construction

This is the arbitrary-kernel counterpart of the density-only corrected
endpoint construction.  It keeps a stagewise no-lookahead product law explicit
and allows terminal endpoint laws with atoms.

It is deliberately a *resampled endpoint-response model*: its finite product
law supplies a candidate endpoint clock at every visible stage.  The archived
paper instead has one endpoint variable `E`; this module does not claim a
coherence bridge from those stage clocks to that single source variable.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- A one-stage rate-free endpoint response law.  The product-law field is the
explicit causal/no-lookahead condition: the next report gap and candidate
endpoint clock are conditionally independent given the visible prefix. -/
structure FinitePredictableEndpointKernelProductModel
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Prefix : Type*) [MeasurableSpace Prefix] [StandardBorelSpace Prefix]
    [Nonempty Prefix]
    (rate : ℝ) where
  preHistory : Ω -> Prefix
  preHistory_measurable : Measurable preHistory
  nextGap : Ω -> ℝ
  nextGap_measurable : Measurable nextGap
  endTime : Ω -> ℝ
  endTime_measurable : Measurable endTime
  endKernel : Kernel Prefix ℝ
  endKernel_isMarkov : IsMarkovKernel endKernel
  /-- A candidate endpoint is a remaining time, hence cannot be negative. -/
  endKernel_nonnegative_support : ∀ history,
    endKernel history (Set.Iio (0 : ℝ)) = 0
  preHistory_nextGap_end_product :
    P.map (fun omega => (preHistory omega, (nextGap omega, endTime omega))) =
      (P.map preHistory) ⊗ₘ
        ((Kernel.const Prefix (expMeasure rate)) ×ₖ endKernel)

namespace FinitePredictableEndpointKernelProductModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Prefix : Type*} [MeasurableSpace Prefix] [StandardBorelSpace Prefix]
  [Nonempty Prefix] {rate : ℝ}

theorem map_preHistory_nextGap_end_eq_product
    (M : FinitePredictableEndpointKernelProductModel Ω P Prefix rate) :
    P.map (fun omega => (M.preHistory omega, (M.nextGap omega, M.endTime omega))) =
      (P.map M.preHistory) ⊗ₘ
        ((Kernel.const Prefix (expMeasure rate)) ×ₖ M.endKernel) :=
  M.preHistory_nextGap_end_product

/-- Rectangle form of the causal product law. -/
theorem rectangle_factorization
    (M : FinitePredictableEndpointKernelProductModel Ω P Prefix rate)
    {A : Set Prefix} {G E : Set ℝ} (rate_pos : 0 < rate)
    (hA : MeasurableSet A) (hG : MeasurableSet G) (hE : MeasurableSet E) :
    P.map (fun omega => (M.preHistory omega, (M.nextGap omega, M.endTime omega)))
        (A ×ˢ (G ×ˢ E)) =
      ∫⁻ h in A, (expMeasure rate) G * M.endKernel h E ∂P.map M.preHistory := by
  letI : IsMarkovKernel M.endKernel := M.endKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  rw [M.preHistory_nextGap_end_product]
  rw [Measure.compProd_apply_prod hA (hG.prod hE)]
  apply lintegral_congr
  intro h
  rw [Kernel.prod_apply_prod]
  rfl

/-- Survival-event specialization of the causal product law. -/
theorem tail_rectangle_factorization
    (M : FinitePredictableEndpointKernelProductModel Ω P Prefix rate)
    {A : Set Prefix} {E : Set ℝ} (rate_pos : 0 < rate) (elapsed : ℝ)
    (hA : MeasurableSet A) (hE : MeasurableSet E) :
    P.map (fun omega => (M.preHistory omega, (M.nextGap omega, M.endTime omega)))
        (A ×ˢ (Set.Ioi elapsed ×ˢ E)) =
      ∫⁻ h in A, (expMeasure rate) (Set.Ioi elapsed) * M.endKernel h E
        ∂P.map M.preHistory :=
  M.rectangle_factorization rate_pos hA measurableSet_Ioi hE

end FinitePredictableEndpointKernelProductModel

/-- A stagewise endpoint-response package over a stationary/Palm tagged report
carrier, without a hidden absolute-continuity requirement on endpoint clocks.

Each `stage` contains its own candidate clock.  This alone does not establish
that the clocks are conditional views of one endpoint variable. -/
structure CausalPreEndEndpointKernelPackage
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate) where
  stage : ∀ j : Fin (count + 1),
    FinitePredictableEndpointKernelProductModel Ω P (Fin j.1 -> ℝ) rate
  stage_preHistory_eq_visiblePrefix : ∀ j,
    (stage j).preHistory = S.visiblePrefix j
  stage_nextGap_eq_source_nextGap : ∀ j,
    (stage j).nextGap = S.nextGap j
  stageSurvival_measurable : ∀ i : Fin count,
    Measurable (fun gaps : Fin count -> ℝ =>
      (stage i.castSucc).endKernel (finiteArrivalPrefix gaps i.castSucc)
        (Set.Ioi (gaps i)))

namespace CausalPreEndEndpointKernelPackage

variable {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {count : ℕ} {rate : ℝ}
  {S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate}

/-- Turn the stagewise endpoint-response package into the arbitrary-kernel
finite observation model. -/
def toKernelCollapsed (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S) :
    CollapsedFiniteStageEndpointKernelModel count where
  startWeight := S.startWeight
  endKernel := fun j => (K.stage j).endKernel
  endKernel_isMarkov := fun j => (K.stage j).endKernel_isMarkov
  endKernel_nonnegative_support := fun j =>
    (K.stage j).endKernel_nonnegative_support
  stageSurvival_measurable := K.stageSurvival_measurable

theorem toKernelCollapsed_endKernel
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (j : Fin (count + 1)) :
    (K.toKernelCollapsed S).endKernel j = (K.stage j).endKernel :=
  rfl

/-- The finite latent vector of the resampled endpoint-response model:
displayed report gaps, all nonterminal candidate clocks, the terminal
candidate clock, and the next report gap.  It is not the archived source's
single-endpoint state vector. -/
def modelLatent
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S) :
    Ω -> ((Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) :=
  fun omega =>
    ((S.postTagGapTail omega).1,
      ((fun i => (K.stage i.castSucc).endTime omega),
        ((K.stage (Fin.last count)).endTime omega, (S.postTagGapTail omega).2)))

theorem measurable_modelLatent
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S) :
    Measurable (K.modelLatent S) := by
  have hnonterminal : Measurable (fun omega : Ω =>
      fun i : Fin count => (K.stage i.castSucc).endTime omega) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (K.stage i.castSucc).endTime_measurable
  exact S.postTagGapTail_measurable.fst.prodMk
    (hnonterminal.prodMk
      ((K.stage (Fin.last count)).endTime_measurable.prodMk
        S.postTagGapTail_measurable.snd))

/-- A full resampled causal-response law.  Unlike the local stage-product
fields, this controls the joint dependence of every endpoint clock and the
following report gap.  Because `responseKernel` contains a finite kernel
product, it additionally postulates conditional mutual independence of every
nonterminal candidate clock given the displayed gap block.

This is a material corrected-model premise, not a consequence of the printed
Appendix Conditions 1--2, and it does not identify the candidate clocks with
the paper's single endpoint variable `E`. -/
structure FullResampledCausalResponseLaw
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S) where
  modelLatent_law :
    P.map (K.modelLatent S) =
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) ⊗ₘ
        (K.toKernelCollapsed S).responseKernel rate

namespace FullResampledCausalResponseLaw

/-- The fixed-tag weighted likelihood measure of the resampled endpoint model:
restrict its latent law to observed races, project to displayed gaps and the
terminal candidate clock, then apply `startWeight`.  Since `startWeight` is an
arbitrary nonnegative scalar, this need not be a probability measure or the
paper's conditional observation law. -/
def modelObservationLikelihood
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S) :
    Measure ((Fin count -> ℝ) × ℝ) :=
  (K.toKernelCollapsed S).startWeight •
    Measure.map
      (fun p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) =>
        (p.1, p.2.2.1))
      ((P.map (K.modelLatent S)).restrict
        (CollapsedFiniteStageEndpointKernelModel.acceptedGapResponseSet
          (count := count)))

/-- The resampled-model restricted pushforward is the generated atom-safe
response law under the explicit full response-law premise. -/
theorem modelObservationLikelihood_eq_generatedObservationLaw
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (J : FullResampledCausalResponseLaw S K) :
    modelObservationLikelihood S K =
      (K.toKernelCollapsed S).generatedObservationLawFrom
        (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) rate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure S.rate_pos
  letI : ∀ _ : Fin count, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure S.rate_pos
  letI : IsProbabilityMeasure
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) := by
    unfold CollapsedFiniteStageEndpointModel.iidGapLaw
    infer_instance
  unfold modelObservationLikelihood
  rw [J.modelLatent_law]
  rw [CollapsedFiniteStageEndpointKernelModel.map_restrict_responseLaw_eq_compProd_acceptedTail
    (K.toKernelCollapsed S)
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) S.rate_pos]
  rfl

/-- The full resampled endpoint-response model has the collapsed observation
law as its weighted restricted pushforward, including atomic endpoint clocks. -/
theorem modelObservationLikelihood_eq_collapsedObservationLaw
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (J : FullResampledCausalResponseLaw S K) :
    modelObservationLikelihood S K =
      (K.toKernelCollapsed S).collapsedObservationLaw rate := by
  rw [modelObservationLikelihood_eq_generatedObservationLaw S K J]
  exact (K.toKernelCollapsed S).generatedObservationLaw_eq_collapsedObservationLaw
    S.rate_pos

end FullResampledCausalResponseLaw

/-- The model-carrier law of a visible prefix, next report gap, and candidate
endpoint clock has the explicit product form supplied by the package. -/
theorem model_stage_product_law
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (j : Fin (count + 1)) :
    P.map (fun omega => (S.visiblePrefix j omega,
      (S.nextGap j omega, (K.stage j).endTime omega))) =
      (P.map (S.visiblePrefix j)) ⊗ₘ
        ((Kernel.const (Fin j.1 -> ℝ) (expMeasure rate)) ×ₖ
          (K.toKernelCollapsed S).endKernel j) := by
  rw [← K.stage_preHistory_eq_visiblePrefix j,
    ← K.stage_nextGap_eq_source_nextGap j]
  simpa [toKernelCollapsed] using (K.stage j).preHistory_nextGap_end_product

/-- The model-stage survival probability factors into a Poisson no-arrival
tail and an endpoint-kernel mass. -/
theorem model_stage_tail_rectangle_factorization
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (j : Fin (count + 1)) {A : Set (Fin j.1 -> ℝ)} {E : Set ℝ}
    (elapsed : ℝ) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    P.map (fun omega => (S.visiblePrefix j omega,
      (S.nextGap j omega, (K.stage j).endTime omega)))
        (A ×ˢ (Set.Ioi elapsed ×ˢ E)) =
      ∫⁻ h in A, (expMeasure rate) (Set.Ioi elapsed) *
        (K.toKernelCollapsed S).endKernel j h E ∂P.map (S.visiblePrefix j) := by
  rw [← K.stage_preHistory_eq_visiblePrefix j,
    ← K.stage_nextGap_eq_source_nextGap j]
  simpa [toKernelCollapsed] using
    (FinitePredictableEndpointKernelProductModel.tail_rectangle_factorization
      (K.stage j) S.rate_pos elapsed hA hE)

/-- The finite observation law associated with the corrected causal package
has an explicit density relative to the terminal endpoint kernel. -/
theorem collapsedObservationLaw_eq_withDensity
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointKernelPackage S) :
    (K.toKernelCollapsed S).collapsedObservationLaw rate =
      ((volume : Measure (Fin count -> ℝ)) ⊗ₘ
        (K.toKernelCollapsed S).terminalEndpointKernel).withDensity
        ((K.toKernelCollapsed S).rawEndpointKernelDensity rate) := by
  exact CollapsedFiniteStageEndpointKernelModel.collapsedObservationLaw_eq_withDensity_rawEndpointKernelDensity
    (K.toKernelCollapsed S) S.rate_pos

end CausalPreEndEndpointKernelPackage

end

end LBG24SpatialUnderreporting
