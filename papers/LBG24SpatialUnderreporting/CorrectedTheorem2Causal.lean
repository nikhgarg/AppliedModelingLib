import LBG24SpatialUnderreporting.ForwardTheorem2PredictableEndpointProduct
import LBG24SpatialUnderreporting.CollapsedCausalObservationLaw
import LBG24SpatialUnderreporting.MainTheorems

/-!
# Corrected causal proof of LBG Appendix Theorem 2

This module formalizes the finite likelihood calculation in Appendix B.2 of
Liu, Bhandaram, and Garg.  The multi-report calculation uses:

* its first gap must be `t_{m+1} - s`, rather than `t_{m+1} - t_m`; and
* after matching the Poisson PMF, the residual contains
  `M! / (e - s)^M`, rather than its reciprocal.

The endpoint condition is represented by a finite causal endpoint-clock
policy: at every visible report prefix it selects a rate-free endpoint clock
before the next exponential interarrival gap is drawn.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
A finite causal endpoint-clock policy along an observed ordered timeline.

At stage `j`, the policy has seen exactly `j` post-start report epochs.  Its
endpoint kernel is a function of that visible prefix and is rate-free.
`stageProductKernel` pairs the endpoint clock with the next exponential gap.
-/
structure FiniteStageCausalEndpointProfile (T : OrderedFiniteJumpTimeline) where
  /-- The rate-free selected-start density factor `g(s | H)`. -/
  startDensity : ℝ
  /-- A conditional probability density is nonnegative at the selected start. -/
  startDensity_nonnegative : 0 ≤ startDensity
  /-- A rate-free endpoint-clock kernel after every visible finite prefix. -/
  endKernel : ∀ j : Fin (T.count + 1), Kernel (Fin j.1 → ℝ) ℝ
  endKernel_isMarkov : ∀ j, IsMarkovKernel (endKernel j)
  /-- Lebesgue densities for the endpoint-clock kernels. -/
  endDensity : ∀ j : Fin (T.count + 1), (Fin j.1 → ℝ) → ℝ → ℝ≥0∞
  endDensity_measurable : ∀ j,
    Measurable (Function.uncurry (endDensity j))
  endKernel_eq_withDensity : ∀ j,
    endKernel j = Kernel.withDensity
      (Kernel.const (Fin j.1 → ℝ) (volume : Measure ℝ))
      (endDensity j)

namespace FiniteStageCausalEndpointProfile

/-- The report epochs visible immediately before stage `j`. -/
def observedPrefix (T : OrderedFiniteJumpTimeline)
    (j : Fin (T.count + 1)) : Fin j.1 → ℝ :=
  finiteArrivalPrefix T.gap j

/--
The conditional law of a fresh next gap and a candidate endpoint clock.
-/
def stageProductKernel (M : FiniteStageCausalEndpointProfile T)
    (rate : ℝ) (j : Fin (T.count + 1)) :
    Kernel (Fin j.1 → ℝ) (ℝ × ℝ) :=
  (Kernel.const (Fin j.1 → ℝ) (expMeasure rate)) ×ₖ M.endKernel j

/--
Setwise expression of the causal product law.  Conditionally on a visible
prefix, a next-gap event and an endpoint-clock event multiply.
-/
theorem stageProductKernel_apply_prod
    (M : FiniteStageCausalEndpointProfile T) (rate : ℝ)
    (j : Fin (T.count + 1)) (visiblePrefix : Fin j.1 → ℝ)
    (nextGapEvent endpointEvent : Set ℝ) (rate_pos : 0 < rate) :
    M.stageProductKernel rate j visiblePrefix (nextGapEvent ×ˢ endpointEvent) =
      (expMeasure rate) nextGapEvent *
        M.endKernel j visiblePrefix endpointEvent := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  letI : IsMarkovKernel (M.endKernel j) := M.endKernel_isMarkov j
  simpa [stageProductKernel] using
    (Kernel.prod_apply_prod
      (κ := Kernel.const (Fin j.1 → ℝ) (expMeasure rate))
      (η := M.endKernel j)
      (a := visiblePrefix) (s := nextGapEvent) (t := endpointEvent))

/--
At a nonterminal observed stage the endpoint clock survives the next observed
gap.  In the source's absolute-time notation this is the corresponding
`∫_{t_{m+i}}^T h_{m+i-1}(u) du`; remaining-time coordinates make it the mass
of `Ioi (t_{m+i} - t_{m+i-1})`.
-/
def stageSurvival (M : FiniteStageCausalEndpointProfile T)
    (i : Fin T.count) : ℝ :=
  (M.endKernel i.castSucc (observedPrefix T i.castSucc)
    (Set.Ioi (T.gap i))).toReal

/-- The terminal endpoint-clock density after the final observed report. -/
def terminalEndpointDensity (M : FiniteStageCausalEndpointProfile T) : ℝ :=
  (M.endDensity (Fin.last T.count) (observedPrefix T (Fin.last T.count))
    T.tail).toReal

/-- All rate-free factors in the corrected finite endpoint likelihood. -/
def endpointWeight (M : FiniteStageCausalEndpointProfile T) : ℝ :=
  M.startDensity * M.terminalEndpointDensity *
    ∏ i : Fin T.count, M.stageSurvival i

/--
The exact-timeline likelihood under the causal endpoint-clock policy.  Its
Poisson component is the product of `T.count` interarrival densities and a
terminal no-arrival tail.  `OrderedFiniteJumpTimeline.gap` stores the first
gap as `t_{m+1} - s`, so this product telescopes over the full exposure
`e - s`.
-/
def rawLikelihood (M : FiniteStageCausalEndpointProfile T) (rate : ℝ) : ℝ :=
  M.endpointWeight *
    theorem2InterarrivalTailLikelihood
      (Finset.univ : Finset (Fin T.count)) rate T.gap T.tail

/-- The corrected rate-free residual in Eq. (8). -/
def correctedResidual (M : FiniteStageCausalEndpointProfile T) : ℝ :=
  M.endpointWeight *
    ((T.count.factorial : ℝ) / T.window.exposure ^ T.count)

/--
The endpoint factor multiplied by the raw Poisson timeline kernel.
-/
theorem rawLikelihood_eq_rawPoissonKernel
    (M : FiniteStageCausalEndpointProfile T) (rate : ℝ) :
    M.rawLikelihood rate =
      M.endpointWeight * rate ^ T.count *
        Real.exp (-(rate * T.window.exposure)) := by
  unfold rawLikelihood
  rw [theorem2_orderedTimeline_interarrival_tail_collects]
  ring

/--
Corrected Appendix Theorem 2 / Eq. (8) for an arbitrary finite ordered report
timeline.  All endpoint-policy factors are rate-free and the sole rate
dependence is the Poisson count likelihood on `(s,e]`.
-/
theorem rawLikelihood_factorizes_corrected_eq8
    (M : FiniteStageCausalEndpointProfile T) (rate : ℝ)
    (h_exposure : T.window.exposure ≠ 0) :
    M.rawLikelihood rate =
      M.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  unfold rawLikelihood correctedResidual
  rw [theorem2_orderedTimeline_interarrival_tail_factorizes T rate h_exposure]
  ring

/--
The same Eq. (8) factorization with the paper-natural positive-duration
premise.
-/
theorem rawLikelihood_factorizes_corrected_eq8_of_pos_exposure
    (M : FiniteStageCausalEndpointProfile T) (rate : ℝ)
    (h_exposure : 0 < T.window.exposure) :
    M.rawLikelihood rate =
      M.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count :=
  M.rawLikelihood_factorizes_corrected_eq8 rate h_exposure.ne'

end FiniteStageCausalEndpointProfile

namespace CollapsedFiniteStageEndpointModel

variable {T : OrderedFiniteJumpTimeline}

/--
The finite causal endpoint model supplies the rate-free factors used by the
fixed-timeline Eq. (8) calculation.
-/
def toFiniteStageCausalEndpointProfile
    (M : CollapsedFiniteStageEndpointModel T.count) :
    FiniteStageCausalEndpointProfile T where
  startDensity := M.startWeight.toReal
  startDensity_nonnegative := ENNReal.toReal_nonneg
  endKernel := M.endKernel
  endKernel_isMarkov := M.endKernel_isMarkov
  endDensity := M.endDensity
  endDensity_measurable := M.endDensity_measurable
  endKernel_eq_withDensity := M.endKernel_eq_withDensity

private theorem exponentialBlockDensity_toReal_eq_pdfReal_prod
    (count : ℕ) (rate : ℝ) (h_rate : 0 < rate)
    (gaps : Fin count → ℝ) :
    (exponentialBlockDensity rate count gaps).toReal =
      ∏ i : Fin count,
        (AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).pdfReal (gaps i) := by
  simp only [exponentialBlockDensity, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [ProbabilityTheory.exponentialPDF,
    AppliedModelingLib.Probability.Exponential.Model.pdfReal]
  rw [ENNReal.toReal_ofReal
    (ProbabilityTheory.exponentialPDFReal_nonneg h_rate (gaps i))]

private theorem endpointWeight_toReal_eq_profile_endpointWeight
    (T : OrderedFiniteJumpTimeline)
    (M : CollapsedFiniteStageEndpointModel T.count) :
    (M.endpointWeight (T.gap, T.tail)).toReal =
      M.toFiniteStageCausalEndpointProfile.endpointWeight := by
  simp only [CollapsedFiniteStageEndpointModel.endpointWeight,
    CollapsedFiniteStageEndpointModel.terminalDensity,
    CollapsedFiniteStageEndpointModel.stageSurvival,
    FiniteStageCausalEndpointProfile.endpointWeight,
    FiniteStageCausalEndpointProfile.terminalEndpointDensity,
    FiniteStageCausalEndpointProfile.stageSurvival,
    FiniteStageCausalEndpointProfile.observedPrefix,
    CollapsedFiniteStageEndpointModel.toFiniteStageCausalEndpointProfile,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  ring

/--
At a fixed ordered timeline, the real-valued density of the finite causal
observation likelihood measure is exactly the corrected endpoint-clock
likelihood.
-/
theorem rawGapTailDensity_toReal_eq_rawLikelihood
    (T : OrderedFiniteJumpTimeline)
    (M : CollapsedFiniteStageEndpointModel T.count)
    {rate : ℝ} (h_rate : 0 < rate) :
    (M.rawGapTailDensity rate (T.gap, T.tail)).toReal =
      M.toFiniteStageCausalEndpointProfile.rawLikelihood rate := by
  have hblock :=
    exponentialBlockDensity_toReal_eq_pdfReal_prod T.count rate h_rate T.gap
  have hweight := endpointWeight_toReal_eq_profile_endpointWeight T M
  have htail :
      (CollapsedFiniteStageEndpointModel.terminalNoArrivalTail rate T.tail).toReal =
        ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
          (Set.Ioi T.tail)).toReal := by
    rw [← CollapsedFiniteStageEndpointModel.expMeasure_Ioi_eq_terminalNoArrivalTail
      h_rate T.tail_nonneg]
    rfl
  rw [CollapsedFiniteStageEndpointModel.rawGapTailDensity,
    CollapsedFiniteStageEndpointModel.terminalWeight,
    ENNReal.toReal_mul, ENNReal.toReal_mul, hblock, hweight, htail]
  unfold FiniteStageCausalEndpointProfile.rawLikelihood
  rw [show theorem2InterarrivalTailLikelihood
      (Finset.univ : Finset (Fin T.count)) rate T.gap T.tail =
      (∏ j : Fin T.count,
        (AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).pdfReal (T.gap j)) *
          ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
            (Set.Ioi T.tail)).toReal by
      exact interarrivalTailLikelihood_eq_exponential_pdfReal_prod_mul_tail
        (Finset.univ : Finset (Fin T.count)) rate h_rate T.gap T.tail
        (by intro j _; exact T.gap_nonneg j) T.tail_nonneg]
  ring

/--
The fixed-timeline density of the finite causal observation likelihood measure
has the corrected Appendix-Theorem-2 / Eq. (8) factorization.
-/
theorem rawGapTailDensity_toReal_factorizes_corrected_eq8
    (T : OrderedFiniteJumpTimeline)
    (M : CollapsedFiniteStageEndpointModel T.count)
    {rate : ℝ} (h_rate : 0 < rate)
    (h_exposure : 0 < T.window.exposure) :
    (M.rawGapTailDensity rate (T.gap, T.tail)).toReal =
      M.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  rw [M.rawGapTailDensity_toReal_eq_rawLikelihood T h_rate]
  exact FiniteStageCausalEndpointProfile.rawLikelihood_factorizes_corrected_eq8_of_pos_exposure
    M.toFiniteStageCausalEndpointProfile rate h_exposure

/--
The model-level density used for a fixed observed history. At a fixed history
before the selected start, `startWeight` is an evaluated selected-start factor,
the stage kernels are causal endpoint clocks, and the timeline stores the
observed post-start reports and terminal endpoint. Exact real-valued
realizations are represented by a likelihood density rather than a literal
singleton-event probability.
-/
def theorem2CausalConditionalLikelihood
    (T : OrderedFiniteJumpTimeline)
    (M : CollapsedFiniteStageEndpointModel T.count) (rate : ℝ) : ℝ :=
  (M.rawGapTailDensity rate (T.gap, T.tail)).toReal

/-- The model-level fixed-history likelihood density agrees with the finite
causal endpoint-clock likelihood. -/
theorem theorem2CausalConditionalLikelihood_eq_rawLikelihood
    (T : OrderedFiniteJumpTimeline)
    (M : CollapsedFiniteStageEndpointModel T.count)
    {rate : ℝ} (h_rate : 0 < rate) :
    theorem2CausalConditionalLikelihood T M rate =
      M.toFiniteStageCausalEndpointProfile.rawLikelihood rate :=
  M.rawGapTailDensity_toReal_eq_rawLikelihood T h_rate

/-- Corrected Appendix Theorem 2 / Eq. (8) for the model-level fixed-history
causal likelihood density. -/
theorem theorem2CausalConditionalLikelihood_factorizes_corrected_eq8
    (T : OrderedFiniteJumpTimeline)
    (M : CollapsedFiniteStageEndpointModel T.count)
    {rate : ℝ} (h_rate : 0 < rate)
    (h_exposure : 0 < T.window.exposure) :
    theorem2CausalConditionalLikelihood T M rate =
      M.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count :=
  M.rawGapTailDensity_toReal_factorizes_corrected_eq8 T h_rate h_exposure

/--
Corrected Eq. (8) for the finite causal endpoint model.  The model's
fixed-history observation likelihood measure is given by
`collapsedObservationLaw_eq_withDensity_rawGapTailDensity`; this theorem
collects its finite ordered-timeline rate dependence into the Poisson PMF.
-/
theorem rawLikelihood_factorizes_corrected_eq8
    (M : CollapsedFiniteStageEndpointModel T.count) (rate : ℝ)
    (h_exposure : T.window.exposure ≠ 0) :
    M.toFiniteStageCausalEndpointProfile.rawLikelihood rate =
      M.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count :=
  M.toFiniteStageCausalEndpointProfile.rawLikelihood_factorizes_corrected_eq8
    rate h_exposure

/-- Corrected Eq. (8) with positive observation exposure. -/
theorem rawLikelihood_factorizes_corrected_eq8_of_pos_exposure
    (M : CollapsedFiniteStageEndpointModel T.count) (rate : ℝ)
    (h_exposure : 0 < T.window.exposure) :
    M.toFiniteStageCausalEndpointProfile.rawLikelihood rate =
      M.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count :=
  M.rawLikelihood_factorizes_corrected_eq8 rate h_exposure.ne'

end CollapsedFiniteStageEndpointModel

end

end LBG24SpatialUnderreporting
