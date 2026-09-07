import LBG24SpatialUnderreporting.CorrectedTheorem2Causal
import AppliedModelingLib.Foundations.Probability.NormalizedKernelDensity

/-!
# Source densities for a finite causal endpoint policy

At a fixed selected start and pre-start report history, the source contributes
one evaluated start-density factor.  At every later visible report prefix, a
jointly measurable normalized density specifies the remaining time to the
endpoint before the next report gap is observed.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Rate-free source densities for a finite causal endpoint observation. -/
structure FiniteCausalEndpointDensitySource (count : ℕ) where
  /-- The selected-start density evaluated at the observed start. -/
  selectedStartDensity : ℝ≥0∞
  /-- Conditional remaining-endpoint densities after every visible prefix. -/
  endpointDensity : ∀ j : Fin (count + 1),
    NormalizedKernelDensity (Fin j.1 → ℝ) ℝ (volume : Measure ℝ)
  /-- Remaining endpoint times are supported on the nonnegative half-line. -/
  endpointDensity_eq_zero_of_neg : ∀ j history tail,
    tail < 0 → (endpointDensity j).density history tail = 0

private theorem measurable_finiteGapPrefix
    {count : ℕ} (j : Fin (count + 1)) :
    Measurable (fun gaps : Fin count → ℝ => finiteGapPrefix gaps j) := by
  refine measurable_pi_iff.2 fun k => ?_
  change Measurable (fun gaps : Fin count → ℝ =>
    gaps ⟨k.1, lt_of_lt_of_le k.2 (Nat.lt_succ_iff.mp j.2)⟩)
  fun_prop

private theorem measurable_cumulativeArrivalVector (q : ℕ) :
    Measurable (cumulativeArrivalVector q) := by
  rw [show cumulativeArrivalVector q = cumulativeArrivalLinearMap q by
    funext gaps
    exact (cumulativeArrivalLinearMap_apply q gaps).symm]
  exact (cumulativeArrivalLinearMap_volume_preserving q).measurable

theorem measurable_finiteArrivalPrefix
    {count : ℕ} (j : Fin (count + 1)) :
    Measurable (fun gaps : Fin count → ℝ => finiteArrivalPrefix gaps j) := by
  exact (measurable_cumulativeArrivalVector j.1).comp
    (measurable_finiteGapPrefix j)

namespace FiniteCausalEndpointDensitySource

variable {count : ℕ}

/-- The normalized conditional endpoint kernel at a visible prefix length. -/
def endpointKernel (S : FiniteCausalEndpointDensitySource count)
    (j : Fin (count + 1)) : Kernel (Fin j.1 → ℝ) ℝ :=
  (S.endpointDensity j).toKernel

theorem endpointKernel_isMarkov
    (S : FiniteCausalEndpointDensitySource count) (j : Fin (count + 1)) :
    IsMarkovKernel (S.endpointKernel j) :=
  (S.endpointDensity j).toKernel_isMarkov

/-- The source density data construct the finite causal endpoint model. -/
def toCollapsedFiniteStageEndpointModel
    (S : FiniteCausalEndpointDensitySource count) :
    CollapsedFiniteStageEndpointModel count where
  startWeight := S.selectedStartDensity
  endKernel := S.endpointKernel
  endKernel_isMarkov := S.endpointKernel_isMarkov
  endDensity := fun j => (S.endpointDensity j).density
  endDensity_measurable := fun j => (S.endpointDensity j).density_measurable
  endKernel_eq_withDensity := fun _ => rfl
  stageSurvival_measurable := fun i => by
    exact (S.endpointDensity i.castSucc).measurable_tailMass.comp
      ((measurable_finiteArrivalPrefix i.castSucc).prodMk
        (measurable_pi_apply i))
  terminalDensity_measurable := by
    exact (S.endpointDensity (Fin.last count)).density_measurable.comp
      (((measurable_finiteArrivalPrefix (Fin.last count)).comp measurable_fst).prodMk
        measurable_snd)

@[simp] theorem toCollapsed_startWeight
    (S : FiniteCausalEndpointDensitySource count) :
    S.toCollapsedFiniteStageEndpointModel.startWeight = S.selectedStartDensity :=
  rfl

@[simp] theorem toCollapsed_endDensity
    (S : FiniteCausalEndpointDensitySource count)
    (j : Fin (count + 1)) :
    S.toCollapsedFiniteStageEndpointModel.endDensity j =
      (S.endpointDensity j).density :=
  rfl

@[simp] theorem toCollapsed_endKernel
    (S : FiniteCausalEndpointDensitySource count)
    (j : Fin (count + 1)) :
    S.toCollapsedFiniteStageEndpointModel.endKernel j = S.endpointKernel j :=
  rfl

/-- The collapsed observation law associated with the start and endpoint densities. -/
def observationLaw (S : FiniteCausalEndpointDensitySource count)
    (rate : ℝ) : Measure ((Fin count → ℝ) × ℝ) :=
  S.toCollapsedFiniteStageEndpointModel.collapsedObservationLaw rate

/-- The fixed-history collapsed-model likelihood density at an observed timeline. -/
def conditionalLikelihoodDensity
    (T : OrderedFiniteJumpTimeline)
    (S : FiniteCausalEndpointDensitySource T.count) (rate : ℝ) : ℝ :=
  S.toCollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood T rate

/-- The associated collapsed observation law has the explicit gap-tail density. -/
theorem observationLaw_eq_withDensity
    (S : FiniteCausalEndpointDensitySource count)
    {rate : ℝ} (h_rate : 0 < rate) :
    S.observationLaw rate =
      ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (S.toCollapsedFiniteStageEndpointModel.rawGapTailDensity rate) :=
  S.toCollapsedFiniteStageEndpointModel.collapsedObservationLaw_eq_withDensity_rawGapTailDensity
    h_rate

/-- The associated fixed-history density satisfies the corrected Eq. (8) factorization. -/
theorem conditionalLikelihoodDensity_factorizes_corrected_eq8
    (T : OrderedFiniteJumpTimeline)
    (S : FiniteCausalEndpointDensitySource T.count)
    {rate : ℝ} (h_rate : 0 < rate) (h_exposure : 0 < T.window.exposure) :
    conditionalLikelihoodDensity T S rate =
      S.toCollapsedFiniteStageEndpointModel.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  exact
    S.toCollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood_factorizes_corrected_eq8
      T h_rate h_exposure

end FiniteCausalEndpointDensitySource

end

end LBG24SpatialUnderreporting
