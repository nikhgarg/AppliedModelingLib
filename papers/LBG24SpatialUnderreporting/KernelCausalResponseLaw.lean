import LBG24SpatialUnderreporting.KernelCausalObservationLaw
import AppliedModelingLib.Foundations.Probability.FiniteKernelProduct
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Atom-safe finite causal response law

This module constructs the finite endpoint-clock response law used by the
corrected LBG observation model without requiring endpoint clocks to admit
Lebesgue densities.  It samples all nonterminal clocks, the terminal clock,
and the following report gap conditionally on the displayed gap block, then
restricts to the races that generate the observed report sequence.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

namespace CollapsedFiniteStageEndpointKernelModel

variable {count : ℕ}

/-- Conditional endpoint clocks for the nonterminal visible prefixes. -/
def nonterminalEndpointKernel (M : CollapsedFiniteStageEndpointKernelModel count) :
    Kernel (Fin count -> ℝ) (Fin count -> ℝ) :=
  finiteKernelProduct count fun i =>
    Kernel.comap (M.endKernel i.castSucc)
      (fun gaps => finiteArrivalPrefix gaps i.castSucc)
      (measurable_kernelFiniteArrivalPrefix i.castSucc)

/-- The nonterminal endpoint-clock kernel is Markov. -/
theorem nonterminalEndpointKernel_isMarkov
    (M : CollapsedFiniteStageEndpointKernelModel count) :
    IsMarkovKernel M.nonterminalEndpointKernel := by
  apply finiteKernelProduct_isMarkov
  intro i
  letI : IsMarkovKernel (M.endKernel i.castSucc) :=
    M.endKernel_isMarkov i.castSucc
  infer_instance

/-- Latent endpoint clocks followed by the terminal next report gap. -/
def responseKernel (M : CollapsedFiniteStageEndpointKernelModel count) (rate : ℝ) :
    Kernel (Fin count -> ℝ) ((Fin count -> ℝ) × (ℝ × ℝ)) :=
  M.nonterminalEndpointKernel ×ₖ
    (M.terminalEndpointKernel ×ₖ
      Kernel.const (Fin count -> ℝ) (expMeasure rate))

/-- The latent response kernel is Markov at a positive report rate. -/
theorem responseKernel_isMarkov
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    IsMarkovKernel (M.responseKernel rate) := by
  letI : IsMarkovKernel M.nonterminalEndpointKernel :=
    M.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  unfold responseKernel
  infer_instance

/-- At fixed displayed gaps, the response kernel is the product of the
nonterminal endpoint clocks, terminal endpoint clock, and next report gap. -/
theorem responseKernel_apply
    (M : CollapsedFiniteStageEndpointKernelModel count) {rate : ℝ}
    (rate_pos : 0 < rate) (gaps : Fin count -> ℝ) :
    M.responseKernel rate gaps =
      (M.nonterminalEndpointKernel gaps).prod
        ((M.terminalEndpointKernel gaps).prod (expMeasure rate)) := by
  letI : IsMarkovKernel M.nonterminalEndpointKernel :=
    M.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  unfold responseKernel
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.const_apply]

/-- Nonterminal endpoint clocks that occur after all displayed report gaps. -/
def nonterminalSurvivalSet (gaps : Fin count -> ℝ) :
    Set (Fin count -> ℝ) :=
  Set.pi Set.univ fun i => Set.Ioi (gaps i)

theorem measurableSet_nonterminalSurvivalSet (gaps : Fin count -> ℝ) :
    MeasurableSet (nonterminalSurvivalSet gaps) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioi

/-- The nonterminal clock block evaluates on the survival rectangle as the
product of its stagewise endpoint-survival masses. -/
theorem nonterminalEndpointKernel_apply_survivalSet
    (M : CollapsedFiniteStageEndpointKernelModel count)
    (gaps : Fin count -> ℝ) :
    M.nonterminalEndpointKernel gaps (nonterminalSurvivalSet gaps) =
      ∏ i : Fin count, M.stageSurvival gaps i := by
  let kappa : Fin count -> Kernel (Fin count -> ℝ) ℝ := fun i =>
    Kernel.comap (M.endKernel i.castSucc)
      (fun block => finiteArrivalPrefix block i.castSucc)
      (measurable_kernelFiniteArrivalPrefix i.castSucc)
  have hkappa : ∀ i, IsMarkovKernel (kappa i) := by
    intro i
    letI : IsMarkovKernel (M.endKernel i.castSucc) :=
      M.endKernel_isMarkov i.castSucc
    infer_instance
  simpa [nonterminalEndpointKernel, nonterminalSurvivalSet, kappa,
    stageSurvival] using
    finiteKernelProduct_apply_pi count kappa hkappa gaps
      (fun i => Set.Ioi (gaps i)) (fun _ => measurableSet_Ioi)

/-- The product of nonterminal endpoint-survival masses is measurable in the
displayed gap block. -/
theorem measurable_nonterminalSurvival
    (M : CollapsedFiniteStageEndpointKernelModel count) :
    Measurable (fun gaps : Fin count -> ℝ => ∏ i : Fin count, M.stageSurvival gaps i) :=
  Finset.measurable_prod Finset.univ fun i _ => M.stageSurvival_measurable i

/-- A latent response is accepted exactly when every displayed report wins
its nonterminal race and the terminal endpoint wins the final race. -/
def acceptedGapResponseSet :
    Set ((Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) :=
  {p | (∀ i, p.1 i < p.2.1 i) ∧ p.2.2.1 < p.2.2.2}

theorem measurableSet_acceptedGapResponseSet :
    MeasurableSet (acceptedGapResponseSet (count := count)) := by
  unfold acceptedGapResponseSet
  have hnonterminal : MeasurableSet
      {p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) |
        ∀ i, p.1 i < p.2.1 i} := by
    rw [show {p :
        (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) |
          ∀ i, p.1 i < p.2.1 i} =
        ⋂ i, {p :
          (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) |
            p.1 i < p.2.1 i} by
      ext p
      simp]
    refine MeasurableSet.iInter fun i => ?_
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hterminal : MeasurableSet
      {p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) |
        p.2.2.1 < p.2.2.2} := by
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  exact hnonterminal.inter hterminal

theorem acceptedGapResponseSet_section (gaps : Fin count -> ℝ) :
    Prod.mk gaps ⁻¹' acceptedGapResponseSet =
      nonterminalSurvivalSet gaps ×ˢ reportWinsEvent := by
  ext response
  simp [acceptedGapResponseSet, nonterminalSurvivalSet, reportWinsEvent]

/-- Indicator density that restricts the response kernel to accepted races. -/
def acceptanceWeight (gaps : Fin count -> ℝ)
    (response : (Fin count -> ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
  (acceptedGapResponseSet (count := count)).indicator 1 (gaps, response)

theorem measurable_acceptanceWeight :
    Measurable (Function.uncurry (acceptanceWeight (count := count))) :=
  measurable_const.indicator measurableSet_acceptedGapResponseSet

theorem acceptanceWeight_eq_indicator_section (gaps : Fin count -> ℝ) :
    acceptanceWeight gaps =
      (nonterminalSurvivalSet gaps ×ˢ reportWinsEvent).indicator 1 := by
  funext response
  by_cases h : (∀ i, gaps i < response.1 i) ∧ response.2.1 < response.2.2
  · simp [acceptanceWeight, acceptedGapResponseSet, nonterminalSurvivalSet,
      reportWinsEvent, h]
  · simp [acceptanceWeight, acceptedGapResponseSet, nonterminalSurvivalSet,
      reportWinsEvent, h]

/-- Accepted latent responses, projected to the terminal endpoint clock. -/
def acceptedTailKernel (M : CollapsedFiniteStageEndpointKernelModel count)
    (rate : ℝ) : Kernel (Fin count -> ℝ) ℝ :=
  letI : IsMarkovKernel M.nonterminalEndpointKernel :=
    M.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  letI : IsSFiniteKernel (M.responseKernel rate) := by
    unfold responseKernel
    infer_instance
  Kernel.map
      (Kernel.withDensity (M.responseKernel rate) acceptanceWeight)
      (fun response => response.2.1)

/-- At fixed displayed gaps, accepted responses retain the terminal endpoint
law tilted by the exact exponential race probability and the nonterminal
survival product. -/
theorem acceptedTailKernel_apply
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) (gaps : Fin count -> ℝ) :
    M.acceptedTailKernel rate gaps =
      (∏ i : Fin count, M.stageSurvival gaps i) •
        (M.terminalEndpointKernel gaps).withDensity
          (terminalRaceTail rate) := by
  letI : IsMarkovKernel M.nonterminalEndpointKernel :=
    M.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  letI : IsSFiniteKernel (M.responseKernel rate) := by
    unfold responseKernel
    infer_instance
  unfold acceptedTailKernel
  rw [Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.withDensity_apply _ measurable_acceptanceWeight]
  rw [acceptanceWeight_eq_indicator_section]
  rw [MeasureTheory.withDensity_indicator_one
    ((measurableSet_nonterminalSurvivalSet gaps).prod measurableSet_reportWinsEvent)]
  rw [M.responseKernel_apply rate_pos gaps]
  rw [map_terminal_restrict_product_response]
  rw [M.nonterminalEndpointKernel_apply_survivalSet]
  rfl

/-- Restricting a Markov response kernel by accepted races and projecting to
the terminal endpoint gives a finite kernel. -/
theorem acceptedTailKernel_isFinite
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    IsFiniteKernel (M.acceptedTailKernel rate) := by
  letI : IsMarkovKernel (M.responseKernel rate) :=
    M.responseKernel_isMarkov rate_pos
  have hweight : ∀ (gaps : Fin count -> ℝ)
      (response : (Fin count -> ℝ) × (ℝ × ℝ)),
      acceptanceWeight (count := count) gaps response ≤ (1 : ℝ≥0∞) := by
    intro gaps response
    by_cases h : (gaps, response) ∈ acceptedGapResponseSet
    · simp [acceptanceWeight, h]
    · simp [acceptanceWeight, h]
  letI : IsFiniteKernel
      (Kernel.withDensity (M.responseKernel rate) acceptanceWeight) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (M.responseKernel rate) ENNReal.one_ne_top hweight
  unfold acceptedTailKernel
  infer_instance

/- The terminal endpoint kernel tilted by the observed nonterminal survival
events and the exact terminal race probability. -/
noncomputable def tiltedTerminalEndpointKernel
    (M : CollapsedFiniteStageEndpointKernelModel count) (rate : ℝ) :
    Kernel (Fin count -> ℝ) ℝ := by
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  exact Kernel.withDensity M.terminalEndpointKernel
    (fun gaps tail =>
      (∏ i : Fin count, M.stageSurvival gaps i) * terminalRaceTail rate tail)

/-- The accepted-tail kernel is the terminal endpoint kernel tilted by the
nonterminal survival product and the exact terminal exponential-race tail. -/
theorem acceptedTailKernel_eq_tiltedTerminalEndpointKernel
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    M.acceptedTailKernel rate = M.tiltedTerminalEndpointKernel rate := by
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  ext gaps : 1
  rw [M.acceptedTailKernel_apply rate_pos gaps]
  unfold tiltedTerminalEndpointKernel
  rw [Kernel.withDensity_apply _
    ((M.measurable_nonterminalSurvival.comp measurable_fst).mul
      ((measurable_terminalRaceTail rate_pos).comp measurable_snd))]
  change (∏ i : Fin count, M.stageSurvival gaps i) •
      (M.terminalEndpointKernel gaps).withDensity (terminalRaceTail rate) =
    (M.terminalEndpointKernel gaps).withDensity
      ((∏ i : Fin count, M.stageSurvival gaps i) • terminalRaceTail rate)
  rw [MeasureTheory.withDensity_smul _ (measurable_terminalRaceTail rate_pos)]

/-- Restricting the joint gap/response law to observed races and projecting
the terminal endpoint is exactly the composition-product with the accepted
tail kernel. -/
theorem map_restrict_responseLaw_eq_compProd_acceptedTail
    (M : CollapsedFiniteStageEndpointKernelModel count)
    (gapLaw : Measure (Fin count -> ℝ)) [SFinite gapLaw]
    {rate : ℝ} (rate_pos : 0 < rate) :
    Measure.map (fun p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) =>
      (p.1, p.2.2.1))
      ((gapLaw ⊗ₘ M.responseKernel rate).restrict
        (acceptedGapResponseSet (count := count))) =
      gapLaw ⊗ₘ M.acceptedTailKernel rate := by
  letI : IsMarkovKernel (M.responseKernel rate) :=
    M.responseKernel_isMarkov rate_pos
  have hweight : ∀ (gaps : Fin count -> ℝ)
      (response : (Fin count -> ℝ) × (ℝ × ℝ)),
      acceptanceWeight (count := count) gaps response ≤ (1 : ℝ≥0∞) := by
    intro gaps response
    by_cases h : (gaps, response) ∈ acceptedGapResponseSet
    · simp [acceptanceWeight, h]
    · simp [acceptanceWeight, h]
  letI : IsFiniteKernel
      (Kernel.withDensity (M.responseKernel rate) acceptanceWeight) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (M.responseKernel rate) ENNReal.one_ne_top hweight
  symm
  unfold acceptedTailKernel
  rw [Measure.compProd_map (by fun_prop)]
  rw [Measure.compProd_withDensity measurable_acceptanceWeight]
  rw [show (fun p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) =>
      acceptanceWeight p.1 p.2) =
        (acceptedGapResponseSet (count := count)).indicator 1 by rfl]
  rw [MeasureTheory.withDensity_indicator_one measurableSet_acceptedGapResponseSet]
  congr 1

/-- A report-gap law and the accepted response kernel generate the observed
gap/terminal-endpoint law before applying any source-to-model bridge. -/
def generatedObservationLawFrom
    (M : CollapsedFiniteStageEndpointKernelModel count)
    (gapLaw : Measure (Fin count -> ℝ)) (rate : ℝ) :
    Measure ((Fin count -> ℝ) × ℝ) :=
  M.startWeight • (gapLaw ⊗ₘ M.acceptedTailKernel rate)

/-- The generated response law has the exact density relative to the input
gap law and the terminal endpoint kernel; this retains endpoint atoms. -/
theorem generatedObservationLawFrom_eq_withDensity
    (M : CollapsedFiniteStageEndpointKernelModel count)
    (gapLaw : Measure (Fin count -> ℝ)) [SFinite gapLaw]
    {rate : ℝ} (rate_pos : 0 < rate) :
    M.generatedObservationLawFrom gapLaw rate =
      (gapLaw ⊗ₘ M.terminalEndpointKernel).withDensity
        (fun p => M.startWeight *
          (∏ i : Fin count, M.stageSurvival p.1 i) * terminalRaceTail rate p.2) := by
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  letI : IsFiniteKernel (M.acceptedTailKernel rate) :=
    M.acceptedTailKernel_isFinite rate_pos
  letI : IsSFiniteKernel (M.tiltedTerminalEndpointKernel rate) := by
    rw [← M.acceptedTailKernel_eq_tiltedTerminalEndpointKernel rate_pos]
    infer_instance
  letI : IsSFiniteKernel
      (Kernel.withDensity M.terminalEndpointKernel
        (fun gaps tail =>
          (∏ i : Fin count, M.stageSurvival gaps i) * terminalRaceTail rate tail)) := by
    change IsSFiniteKernel (M.tiltedTerminalEndpointKernel rate)
    infer_instance
  unfold generatedObservationLawFrom
  rw [M.acceptedTailKernel_eq_tiltedTerminalEndpointKernel rate_pos]
  unfold tiltedTerminalEndpointKernel
  rw [Measure.compProd_withDensity
    ((M.measurable_nonterminalSurvival.comp measurable_fst).mul
      ((measurable_terminalRaceTail rate_pos).comp measurable_snd))]
  let base : Measure ((Fin count -> ℝ) × ℝ) :=
    gapLaw ⊗ₘ M.terminalEndpointKernel
  let density : (Fin count -> ℝ) × ℝ -> ℝ≥0∞ := fun p =>
    (∏ i : Fin count, M.stageSurvival p.1 i) * terminalRaceTail rate p.2
  have hdensity : Measurable density := by
    exact (M.measurable_nonterminalSurvival.comp measurable_fst).mul
      ((measurable_terminalRaceTail rate_pos).comp measurable_snd)
  change M.startWeight • base.withDensity density =
    base.withDensity (fun p =>
      (M.startWeight * ∏ i : Fin count, M.stageSurvival p.1 i) *
        terminalRaceTail rate p.2)
  rw [← MeasureTheory.withDensity_smul M.startWeight hdensity]
  congr 1
  funext p
  simp [density, Pi.smul_apply, mul_assoc]

/-- Sampling an iid exponential report-gap block and the atom-safe causal
response kernel yields the collapsed finite observation law. -/
theorem generatedObservationLaw_eq_collapsedObservationLaw
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    M.generatedObservationLawFrom
        (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) rate =
      M.collapsedObservationLaw rate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  letI : ∀ _ : Fin count, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure rate_pos
  letI : IsProbabilityMeasure
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) := by
    unfold CollapsedFiniteStageEndpointModel.iidGapLaw
    infer_instance
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  rw [M.generatedObservationLawFrom_eq_withDensity
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) rate_pos]
  unfold collapsedObservationLaw weightedGapLaw
  rw [Measure.compProd_withDensity_left M.measurable_gapWeight]
  change
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ M.terminalEndpointKernel).withDensity
        (fun p =>
          (M.startWeight * ∏ i : Fin count, M.stageSurvival p.1 i) *
            terminalRaceTail rate p.2) =
      ((CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ M.terminalEndpointKernel).withDensity
        (M.gapWeight ∘ Prod.fst)).withDensity
          (terminalRaceTail rate ∘ Prod.snd)
  rw [← MeasureTheory.withDensity_mul
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ M.terminalEndpointKernel)
    (M.measurable_gapWeight.comp measurable_fst)
    ((measurable_terminalRaceTail rate_pos).comp measurable_snd)]
  congr 1

end CollapsedFiniteStageEndpointKernelModel

end

end LBG24SpatialUnderreporting
