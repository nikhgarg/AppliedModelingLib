import LBG24SpatialUnderreporting.CausalEndpointDensitySource
import LBG24SpatialUnderreporting.StationaryPalmCausalEndpointBridge
import AppliedModelingLib.Foundations.Probability.FiniteKernelProduct
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Tactic

/-!
# Global causal observation law from a stationary/Palm report source

A finite vector of endpoint clocks is sampled conditionally and independently
from the visible report prefixes.  The observation accepts paths on which each
displayed report precedes its nonterminal endpoint clock and the terminal
endpoint precedes the next report.  Projecting the accepted latent law gives
the finite gap-tail observation measure.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

namespace FiniteCausalEndpointDensitySource

variable {count : ℕ}

/-- Conditional endpoint clocks for the nonterminal visible prefixes. -/
def nonterminalEndpointKernel (S : FiniteCausalEndpointDensitySource count) :
    Kernel (Fin count → ℝ) (Fin count → ℝ) :=
  finiteKernelProduct count fun i =>
    Kernel.comap (S.endpointKernel i.castSucc)
      (fun gaps => finiteArrivalPrefix gaps i.castSucc)
      (measurable_finiteArrivalPrefix i.castSucc)

/-- The nonterminal endpoint-clock kernel is Markov. -/
theorem nonterminalEndpointKernel_isMarkov
    (S : FiniteCausalEndpointDensitySource count) :
    IsMarkovKernel S.nonterminalEndpointKernel := by
  apply finiteKernelProduct_isMarkov
  intro i
  letI : IsMarkovKernel (S.endpointKernel i.castSucc) :=
    S.endpointKernel_isMarkov i.castSucc
  infer_instance

/-- Conditional terminal endpoint clock after the displayed gap block. -/
def terminalEndpointKernel (S : FiniteCausalEndpointDensitySource count) :
    Kernel (Fin count → ℝ) ℝ :=
  Kernel.comap (S.endpointKernel (Fin.last count))
    (fun gaps => finiteArrivalPrefix gaps (Fin.last count))
    (measurable_finiteArrivalPrefix (Fin.last count))

/-- The terminal endpoint-clock kernel is Markov. -/
theorem terminalEndpointKernel_isMarkov
    (S : FiniteCausalEndpointDensitySource count) :
    IsMarkovKernel S.terminalEndpointKernel := by
  letI : IsMarkovKernel (S.endpointKernel (Fin.last count)) :=
    S.endpointKernel_isMarkov (Fin.last count)
  unfold terminalEndpointKernel
  infer_instance

/-- Latent response kernel: nonterminal endpoint clocks, followed by a
terminal endpoint clock and the next report gap. -/
def responseKernel (S : FiniteCausalEndpointDensitySource count) (rate : ℝ) :
    Kernel (Fin count → ℝ) ((Fin count → ℝ) × (ℝ × ℝ)) :=
  S.nonterminalEndpointKernel ×ₖ
    (S.terminalEndpointKernel ×ₖ
      Kernel.const (Fin count → ℝ) (expMeasure rate))

/-- The latent response kernel is Markov at a positive report rate. -/
theorem responseKernel_isMarkov
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate) :
    IsMarkovKernel (S.responseKernel rate) := by
  letI : IsMarkovKernel S.nonterminalEndpointKernel :=
    S.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel S.terminalEndpointKernel :=
    S.terminalEndpointKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  unfold responseKernel
  infer_instance

/-- At fixed displayed gaps, the response kernel is the product of the
nonterminal clock block, terminal endpoint clock, and next report gap. -/
theorem responseKernel_apply
    (S : FiniteCausalEndpointDensitySource count) {rate : ℝ}
    (h_rate : 0 < rate)
    (gaps : Fin count → ℝ) :
    S.responseKernel rate gaps =
      (S.nonterminalEndpointKernel gaps).prod
        ((S.terminalEndpointKernel gaps).prod (expMeasure rate)) := by
  letI : IsMarkovKernel S.nonterminalEndpointKernel :=
    S.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel S.terminalEndpointKernel :=
    S.terminalEndpointKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  unfold responseKernel
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.const_apply]

/-- Nonterminal clocks that occur after all displayed report gaps. -/
def nonterminalSurvivalSet (gaps : Fin count → ℝ) :
    Set (Fin count → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioi (gaps i)

theorem measurableSet_nonterminalSurvivalSet (gaps : Fin count → ℝ) :
    MeasurableSet (nonterminalSurvivalSet gaps) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioi

/-- The nonterminal clock block evaluates on the survival rectangle as the
product of the stagewise endpoint survival masses. -/
theorem nonterminalEndpointKernel_apply_survivalSet
    (S : FiniteCausalEndpointDensitySource count)
    (gaps : Fin count → ℝ) :
    S.nonterminalEndpointKernel gaps (nonterminalSurvivalSet gaps) =
      ∏ i : Fin count,
        S.endpointKernel i.castSucc
          (finiteArrivalPrefix gaps i.castSucc) (Set.Ioi (gaps i)) := by
  let kappa : Fin count → Kernel (Fin count → ℝ) ℝ := fun i =>
    Kernel.comap (S.endpointKernel i.castSucc)
      (fun block => finiteArrivalPrefix block i.castSucc)
      (measurable_finiteArrivalPrefix i.castSucc)
  have hkappa : ∀ i, IsMarkovKernel (kappa i) := by
    intro i
    letI : IsMarkovKernel (S.endpointKernel i.castSucc) :=
      S.endpointKernel_isMarkov i.castSucc
    infer_instance
  simpa [nonterminalEndpointKernel, nonterminalSurvivalSet, kappa] using
    finiteKernelProduct_apply_pi count kappa hkappa gaps
      (fun i => Set.Ioi (gaps i)) (fun _ => measurableSet_Ioi)

/-- The latent response is accepted precisely when every displayed report
wins its nonterminal race and the endpoint wins the terminal race. -/
def acceptedGapResponseSet :
    Set ((Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ))) :=
  {p | (∀ i, p.1 i < p.2.1 i) ∧ p.2.2.1 < p.2.2.2}

theorem measurableSet_acceptedGapResponseSet :
    MeasurableSet (acceptedGapResponseSet (count := count)) := by
  unfold acceptedGapResponseSet
  have hnonterminal : MeasurableSet
      {p : (Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ)) |
        ∀ i, p.1 i < p.2.1 i} := by
    rw [show {p :
        (Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ)) |
          ∀ i, p.1 i < p.2.1 i} =
        ⋂ i, {p :
          (Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ)) |
            p.1 i < p.2.1 i} by
      ext p
      simp]
    refine MeasurableSet.iInter fun i => ?_
    have hgap : Measurable (fun p :
        (Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ)) => p.1 i) := by
      fun_prop
    have hclock : Measurable (fun p :
        (Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ)) => p.2.1 i) := by
      fun_prop
    exact measurableSet_lt hgap hclock
  have hterminal : MeasurableSet
      {p : (Fin count → ℝ) × ((Fin count → ℝ) × (ℝ × ℝ)) |
        p.2.2.1 < p.2.2.2} := by
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  exact hnonterminal.inter hterminal

theorem acceptedGapResponseSet_section (gaps : Fin count → ℝ) :
    Prod.mk gaps ⁻¹' acceptedGapResponseSet =
      nonterminalSurvivalSet gaps ×ˢ reportWinsEvent := by
  ext response
  simp [acceptedGapResponseSet, nonterminalSurvivalSet, reportWinsEvent]

/-- Indicator density that restricts the response kernel to accepted races. -/
def acceptanceWeight (gaps : Fin count → ℝ)
    (response : (Fin count → ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
  (acceptedGapResponseSet (count := count)).indicator 1 (gaps, response)

theorem measurable_acceptanceWeight :
    Measurable (Function.uncurry (acceptanceWeight (count := count))) := by
  exact measurable_const.indicator measurableSet_acceptedGapResponseSet

theorem acceptanceWeight_eq_indicator_section (gaps : Fin count → ℝ) :
    acceptanceWeight gaps =
      (nonterminalSurvivalSet gaps ×ˢ reportWinsEvent).indicator 1 := by
  funext response
  by_cases h : (∀ i, gaps i < response.1 i) ∧ response.2.1 < response.2.2
  · simp [acceptanceWeight, acceptedGapResponseSet, nonterminalSurvivalSet,
      reportWinsEvent, h]
  · simp [acceptanceWeight, acceptedGapResponseSet, nonterminalSurvivalSet,
      reportWinsEvent, h]

/-- Accepted latent responses, projected to the terminal endpoint tail. -/
def acceptedTailKernel (S : FiniteCausalEndpointDensitySource count)
    (rate : ℝ) : Kernel (Fin count → ℝ) ℝ :=
  letI : IsMarkovKernel S.nonterminalEndpointKernel :=
    S.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel S.terminalEndpointKernel :=
    S.terminalEndpointKernel_isMarkov
  letI : IsSFiniteKernel (S.responseKernel rate) := by
    unfold responseKernel
    infer_instance
  Kernel.map
      (Kernel.withDensity (S.responseKernel rate) acceptanceWeight)
      (fun response => response.2.1)

/-- At fixed displayed gaps, accepted responses have the endpoint-tail tilt
and the product of nonterminal endpoint survival masses. -/
theorem acceptedTailKernel_apply
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate) (gaps : Fin count → ℝ) :
    S.acceptedTailKernel rate gaps =
      (∏ i : Fin count,
        S.endpointKernel i.castSucc
          (finiteArrivalPrefix gaps i.castSucc) (Set.Ioi (gaps i))) •
        (S.endpointKernel (Fin.last count)
          (finiteArrivalPrefix gaps (Fin.last count))).withDensity
            (fun tail => expMeasure rate (Set.Ioi tail)) := by
  letI : IsMarkovKernel S.nonterminalEndpointKernel :=
    S.nonterminalEndpointKernel_isMarkov
  letI : IsMarkovKernel S.terminalEndpointKernel :=
    S.terminalEndpointKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  letI : IsSFiniteKernel (S.responseKernel rate) := by
    unfold responseKernel
    infer_instance
  unfold acceptedTailKernel
  rw [Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.withDensity_apply _ measurable_acceptanceWeight]
  rw [acceptanceWeight_eq_indicator_section]
  rw [MeasureTheory.withDensity_indicator_one
    ((measurableSet_nonterminalSurvivalSet gaps).prod measurableSet_reportWinsEvent)]
  rw [S.responseKernel_apply h_rate gaps]
  rw [map_terminal_restrict_product_response]
  rw [S.nonterminalEndpointKernel_apply_survivalSet]
  rfl

/-- Restricting a Markov response kernel by an acceptance indicator and then
projecting gives a finite kernel. -/
theorem acceptedTailKernel_isFinite
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate) :
    IsFiniteKernel (S.acceptedTailKernel rate) := by
  letI : IsMarkovKernel (S.responseKernel rate) :=
    S.responseKernel_isMarkov h_rate
  have hweight : ∀ (gaps : Fin count → ℝ)
      (response : (Fin count → ℝ) × (ℝ × ℝ)),
      acceptanceWeight (count := count) gaps response ≤ (1 : ℝ≥0∞) := by
    intro gaps response
    by_cases h : (gaps, response) ∈ acceptedGapResponseSet
    · simp [acceptanceWeight, h]
    · simp [acceptanceWeight, h]
  letI : IsFiniteKernel
      (Kernel.withDensity (S.responseKernel rate) acceptanceWeight) :=
    Kernel.isFiniteKernel_withDensity_of_bounded
      (S.responseKernel rate) ENNReal.one_ne_top hweight
  unfold acceptedTailKernel
  infer_instance

/-- Nonnegative endpoint support identifies the exponential next-gap tail
with the terminal no-arrival factor wherever the endpoint density is nonzero. -/
theorem terminalDensity_mul_expTail_eq_terminalNoArrivalTail
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate)
    (history : Fin count → ℝ) (tail : ℝ) :
    (S.endpointDensity (Fin.last count)).density history tail *
        expMeasure rate (Set.Ioi tail) =
      (S.endpointDensity (Fin.last count)).density history tail *
        CollapsedFiniteStageEndpointModel.terminalNoArrivalTail rate tail := by
  by_cases htail : 0 ≤ tail
  · rw [CollapsedFiniteStageEndpointModel.expMeasure_Ioi_eq_terminalNoArrivalTail
      h_rate htail]
  · have hneg : tail < 0 := lt_of_not_ge htail
    rw [S.endpointDensity_eq_zero_of_neg (Fin.last count) history tail hneg]
    simp

/-- Density of the accepted terminal response conditional on displayed gaps. -/
def acceptedTailDensity (S : FiniteCausalEndpointDensitySource count)
    (rate : ℝ) (gaps : Fin count → ℝ) (tail : ℝ) : ℝ≥0∞ :=
  (∏ i : Fin count,
      S.endpointKernel i.castSucc
        (finiteArrivalPrefix gaps i.castSucc) (Set.Ioi (gaps i))) *
    (S.endpointDensity (Fin.last count)).density
      (finiteArrivalPrefix gaps (Fin.last count)) tail *
    CollapsedFiniteStageEndpointModel.terminalNoArrivalTail rate tail

theorem measurable_acceptedTailDensity
    (S : FiniteCausalEndpointDensitySource count) (rate : ℝ) :
    Measurable (Function.uncurry (S.acceptedTailDensity rate)) := by
  let M := S.toCollapsedFiniteStageEndpointModel
  have hsurvival : Measurable (fun gaps : Fin count → ℝ =>
      ∏ i : Fin count,
        S.endpointKernel i.castSucc
          (finiteArrivalPrefix gaps i.castSucc) (Set.Ioi (gaps i))) := by
    exact Finset.measurable_prod Finset.univ fun i _ =>
      M.stageSurvival_measurable i
  have hdensity : Measurable (fun p : (Fin count → ℝ) × ℝ =>
      (S.endpointDensity (Fin.last count)).density
        (finiteArrivalPrefix p.1 (Fin.last count)) p.2) := by
    exact M.terminalDensity_measurable
  exact ((hsurvival.comp measurable_fst).mul hdensity).mul
    ((CollapsedFiniteStageEndpointModel.measurable_terminalNoArrivalTail rate).comp
      measurable_snd)

/-- The accepted-response kernel has the product of the endpoint-clock
survival factors, terminal endpoint density, and next-report survival tail. -/
theorem acceptedTailKernel_eq_withDensity
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate) :
    S.acceptedTailKernel rate =
      Kernel.withDensity
        (Kernel.const (Fin count → ℝ) (volume : Measure ℝ))
        (S.acceptedTailDensity rate) := by
  ext gaps : 1
  rw [S.acceptedTailKernel_apply h_rate gaps]
  rw [Kernel.withDensity_apply _ (S.measurable_acceptedTailDensity rate)]
  rw [Kernel.const_apply]
  let history := finiteArrivalPrefix gaps (Fin.last count)
  let terminalDensity := fun tail : ℝ =>
    (S.endpointDensity (Fin.last count)).density history tail
  let survival := ∏ i : Fin count,
    S.endpointKernel i.castSucc (finiteArrivalPrefix gaps i.castSucc)
      (Set.Ioi (gaps i))
  let tailMass := fun tail : ℝ => expMeasure rate (Set.Ioi tail)
  have hdensity : Measurable terminalDensity := by
    exact (S.endpointDensity (Fin.last count)).density_measurable.comp
      (measurable_const.prodMk measurable_id)
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  have htail : Measurable tailMass := measurable_measure_Ioi (expMeasure rate)
  have hterminal :
      S.endpointKernel (Fin.last count) history =
        (volume : Measure ℝ).withDensity terminalDensity := by
    unfold endpointKernel NormalizedKernelDensity.toKernel
    rw [Kernel.withDensity_apply _
      (S.endpointDensity (Fin.last count)).density_measurable]
    rw [Kernel.const_apply]
  rw [show finiteArrivalPrefix gaps (Fin.last count) = history by rfl]
  rw [hterminal]
  change survival •
      ((volume : Measure ℝ).withDensity terminalDensity).withDensity tailMass = _
  rw [← MeasureTheory.withDensity_mul (volume : Measure ℝ) hdensity htail]
  have hmul : terminalDensity * tailMass =
      (fun tail => terminalDensity tail * tailMass tail) := by
    rfl
  rw [hmul]
  rw [← MeasureTheory.withDensity_smul
    (μ := (volume : Measure ℝ)) survival (hdensity.mul htail)]
  congr 1
  funext tail
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [S.terminalDensity_mul_expTail_eq_terminalNoArrivalTail h_rate history tail]
  simp [acceptedTailDensity, survival, history, mul_assoc]

/-- A report-gap law and the causal response kernel generate an observation
law before the fixed selected-start density is applied. -/
def generatedObservationLawFrom
    (S : FiniteCausalEndpointDensitySource count)
    (gapLaw : Measure (Fin count → ℝ)) (rate : ℝ) :
    Measure ((Fin count → ℝ) × ℝ) :=
  S.selectedStartDensity • (gapLaw ⊗ₘ S.acceptedTailKernel rate)

/-- Density of the generated gap-tail law relative to a gap law times
Lebesgue measure. -/
def generatedGapTailDensity
    (S : FiniteCausalEndpointDensitySource count) (rate : ℝ)
    (p : (Fin count → ℝ) × ℝ) : ℝ≥0∞ :=
  S.selectedStartDensity * S.acceptedTailDensity rate p.1 p.2

theorem measurable_generatedGapTailDensity
    (S : FiniteCausalEndpointDensitySource count) (rate : ℝ) :
    Measurable (S.generatedGapTailDensity rate) :=
  measurable_const.mul (S.measurable_acceptedTailDensity rate)

/-- The latent response construction yields an explicit density relative to
the supplied report-gap law and Lebesgue measure on the endpoint tail. -/
theorem generatedObservationLawFrom_eq_withDensity
    (S : FiniteCausalEndpointDensitySource count)
    (gapLaw : Measure (Fin count → ℝ)) [SFinite gapLaw]
    {rate : ℝ} (h_rate : 0 < rate) :
    S.generatedObservationLawFrom gapLaw rate =
      (gapLaw.prod (volume : Measure ℝ)).withDensity
        (S.generatedGapTailDensity rate) := by
  letI : IsFiniteKernel (S.acceptedTailKernel rate) :=
    S.acceptedTailKernel_isFinite h_rate
  letI : IsSFiniteKernel
      (Kernel.withDensity
        (Kernel.const (Fin count → ℝ) (volume : Measure ℝ))
        (S.acceptedTailDensity rate)) := by
    rw [← S.acceptedTailKernel_eq_withDensity h_rate]
    infer_instance
  unfold generatedObservationLawFrom
  rw [S.acceptedTailKernel_eq_withDensity h_rate]
  rw [Measure.compProd_withDensity (S.measurable_acceptedTailDensity rate)]
  rw [Measure.compProd_const]
  rw [show (fun p : (Fin count → ℝ) × ℝ =>
      S.acceptedTailDensity rate p.1 p.2) =
      Function.uncurry (S.acceptedTailDensity rate) by rfl]
  rw [← MeasureTheory.withDensity_smul
    (μ := gapLaw.prod (volume : Measure ℝ)) S.selectedStartDensity
      (S.measurable_acceptedTailDensity rate)]
  congr 1

/-- The generated density is exactly the collapsed model's terminal weight. -/
theorem generatedGapTailDensity_eq_terminalWeight
    (S : FiniteCausalEndpointDensitySource count) (rate : ℝ) :
    S.generatedGapTailDensity rate =
      S.toCollapsedFiniteStageEndpointModel.terminalWeight rate := by
  funext p
  simp [generatedGapTailDensity, acceptedTailDensity,
    CollapsedFiniteStageEndpointModel.terminalWeight,
    CollapsedFiniteStageEndpointModel.endpointWeight,
    CollapsedFiniteStageEndpointModel.stageSurvival,
    CollapsedFiniteStageEndpointModel.terminalDensity, mul_assoc]

/-- Sampling the Palm iid report block, all causal endpoint clocks, and the
following report gap gives the collapsed observation law. -/
theorem generatedObservationLaw_eq_collapsedObservationLaw
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate) :
    S.generatedObservationLawFrom
        (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) rate =
      S.toCollapsedFiniteStageEndpointModel.collapsedObservationLaw rate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  letI : ∀ _ : Fin count, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure h_rate
  letI : IsProbabilityMeasure
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) := by
    unfold CollapsedFiniteStageEndpointModel.iidGapLaw
    infer_instance
  rw [S.generatedObservationLawFrom_eq_withDensity
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) h_rate]
  rw [S.generatedGapTailDensity_eq_terminalWeight]
  rfl

end FiniteCausalEndpointDensitySource

/-- A stationary/Palm report source together with normalized causal endpoint
densities at every finite visible prefix. -/
structure StationaryPalmCausalObservationModel
    (OmegaBase Omega : Type*) [MeasurableSpace OmegaBase] [MeasurableSpace Omega]
    (P : Measure Omega) (count : ℕ) (rate : ℝ) where
  reportSource :
    StationaryPalmTaggedArrivalSource OmegaBase Omega P count rate
  endpointSource : FiniteCausalEndpointDensitySource count
  selectedStartDensity_eq_startWeight :
    endpointSource.selectedStartDensity = reportSource.startWeight

namespace StationaryPalmCausalObservationModel

variable {OmegaBase Omega : Type*}
  [MeasurableSpace OmegaBase] [MeasurableSpace Omega]
  {P : Measure Omega} {count : ℕ} {rate : ℝ}

/-- The verified stationary Poisson suspension and any source-valid causal
endpoint-density family instantiate the complete observation model. -/
noncomputable def ofPoissonSuspension
    (rate : ℝ) (rate_pos : 0 < rate) (count : ℕ)
    (endpointSource : FiniteCausalEndpointDensitySource count) :
    StationaryPalmCausalObservationModel
      GoodSuspensionState (ℤ → ℝ)
      (candidateTaggedArrivalAtZero rate rate_pos).Ptag count rate where
  reportSource := StationaryPalmTaggedArrivalSource.ofPoissonSuspension
    rate rate_pos count endpointSource.selectedStartDensity
  endpointSource := endpointSource
  selectedStartDensity_eq_startWeight := rfl

/-- The observation law obtained from the Palm post-tag report block and the
global causal endpoint-response kernel. -/
def sourceObservationLaw
    (M : StationaryPalmCausalObservationModel OmegaBase Omega P count rate) :
    Measure ((Fin count → ℝ) × ℝ) :=
  M.endpointSource.generatedObservationLawFrom
    (P.map (fun omega => (M.reportSource.postTagGapTail omega).1)) rate

/-- The collapsed model retains the start density carried by the Palm source. -/
theorem collapsed_startWeight_eq_reportSource
    (M : StationaryPalmCausalObservationModel OmegaBase Omega P count rate) :
    M.endpointSource.toCollapsedFiniteStageEndpointModel.startWeight =
      M.reportSource.startWeight := by
  rw [FiniteCausalEndpointDensitySource.toCollapsed_startWeight]
  exact M.selectedStartDensity_eq_startWeight

/-- The Palm source-to-model bridge: the restricted pushforward of the global
causal response law equals the collapsed finite observation measure. -/
theorem sourceObservationLaw_eq_collapsedObservationLaw
    (M : StationaryPalmCausalObservationModel OmegaBase Omega P count rate) :
    M.sourceObservationLaw =
      M.endpointSource.toCollapsedFiniteStageEndpointModel.collapsedObservationLaw rate := by
  unfold sourceObservationLaw
  rw [M.reportSource.postTagGapBlock_law]
  exact M.endpointSource.generatedObservationLaw_eq_collapsedObservationLaw
    M.reportSource.rate_pos

/-- The source-generated observation law has the explicit Poisson gap density,
endpoint survival product, terminal endpoint density, and response tail. -/
theorem sourceObservationLaw_eq_withDensity_rawGapTailDensity
    (M : StationaryPalmCausalObservationModel OmegaBase Omega P count rate) :
    M.sourceObservationLaw =
      ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (M.endpointSource.toCollapsedFiniteStageEndpointModel.rawGapTailDensity rate) := by
  rw [M.sourceObservationLaw_eq_collapsedObservationLaw]
  exact CollapsedFiniteStageEndpointModel.collapsedObservationLaw_eq_withDensity_rawGapTailDensity
      M.endpointSource.toCollapsedFiniteStageEndpointModel
      M.reportSource.rate_pos

/-- The fixed-timeline density associated with the source-generated
observation law. -/
def conditionalLikelihoodDensity
    (T : OrderedFiniteJumpTimeline)
    (M : StationaryPalmCausalObservationModel
      OmegaBase Omega P T.count rate) : ℝ :=
  M.endpointSource.conditionalLikelihoodDensity T rate

/-- The stationary/Palm source construction satisfies the corrected Eq. (8)
factorization at every positive-exposure ordered timeline. -/
theorem conditionalLikelihoodDensity_factorizes_corrected_eq8
    (T : OrderedFiniteJumpTimeline)
    (M : StationaryPalmCausalObservationModel
      OmegaBase Omega P T.count rate)
    (h_exposure : 0 < T.window.exposure) :
    M.conditionalLikelihoodDensity T =
      M.endpointSource.toCollapsedFiniteStageEndpointModel.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  exact M.endpointSource.conditionalLikelihoodDensity_factorizes_corrected_eq8
    T M.reportSource.rate_pos h_exposure

/-- The concrete stationary Poisson suspension generates exactly the
collapsed causal observation law from source endpoint densities. -/
theorem poissonSuspension_sourceObservationLaw_eq_collapsedObservationLaw
    (rate : ℝ) (rate_pos : 0 < rate)
    (S : FiniteCausalEndpointDensitySource count) :
    (ofPoissonSuspension rate rate_pos count S).sourceObservationLaw =
      S.toCollapsedFiniteStageEndpointModel.collapsedObservationLaw rate := by
  simpa [ofPoissonSuspension] using
    (ofPoissonSuspension rate rate_pos count S).sourceObservationLaw_eq_collapsedObservationLaw

/-- The concrete stationary Poisson suspension has the explicit causal
gap-tail observation density. -/
theorem poissonSuspension_sourceObservationLaw_eq_withDensity
    (rate : ℝ) (rate_pos : 0 < rate)
    (S : FiniteCausalEndpointDensitySource count) :
    (ofPoissonSuspension rate rate_pos count S).sourceObservationLaw =
      ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (S.toCollapsedFiniteStageEndpointModel.rawGapTailDensity rate) := by
  simpa [ofPoissonSuspension] using
    (ofPoissonSuspension rate rate_pos count S).sourceObservationLaw_eq_withDensity_rawGapTailDensity

/-- The source-constructed stationary Poisson observation model satisfies the
corrected Eq. (8) density factorization. -/
theorem poissonSuspension_conditionalLikelihoodDensity_factorizes_corrected_eq8
    (T : OrderedFiniteJumpTimeline) (rate : ℝ) (rate_pos : 0 < rate)
    (S : FiniteCausalEndpointDensitySource T.count)
    (h_exposure : 0 < T.window.exposure) :
    conditionalLikelihoodDensity T
        (ofPoissonSuspension rate rate_pos T.count S) =
      S.toCollapsedFiniteStageEndpointModel.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  simpa [ofPoissonSuspension] using
    (ofPoissonSuspension rate rate_pos T.count S).conditionalLikelihoodDensity_factorizes_corrected_eq8
      T h_exposure

end StationaryPalmCausalObservationModel

end

end LBG24SpatialUnderreporting
