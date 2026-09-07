import LBG24SpatialUnderreporting.CollapsedCausalObservationLaw
import AppliedModelingLib.Foundations.Probability.KernelCompProdDensity

/-!
# Kernel-valued finite causal endpoint observations

The source applications use deterministic administrative caps as well as
random endpoint decisions.  This module retains an arbitrary rate-free endpoint
kernel as the reference law for the terminal endpoint instead of requiring a
Lebesgue density.  The Poisson part of the likelihood remains an ordinary
density on the report-gap coordinate.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

private theorem measurable_kernelFiniteGapPrefix
    {count : ℕ} (j : Fin (count + 1)) :
    Measurable (fun gaps : Fin count -> ℝ => finiteGapPrefix gaps j) := by
  refine measurable_pi_iff.2 fun k => ?_
  change Measurable (fun gaps : Fin count -> ℝ =>
    gaps ⟨k.1, lt_of_lt_of_le k.2 (Nat.lt_succ_iff.mp j.2)⟩)
  fun_prop

private theorem measurable_kernelCumulativeArrivalVector (q : ℕ) :
    Measurable (cumulativeArrivalVector q) := by
  rw [show cumulativeArrivalVector q = cumulativeArrivalLinearMap q by
    funext gaps
    exact (cumulativeArrivalLinearMap_apply q gaps).symm]
  exact (cumulativeArrivalLinearMap_volume_preserving q).measurable

theorem measurable_kernelFiniteArrivalPrefix
    {count : ℕ} (j : Fin (count + 1)) :
    Measurable (fun gaps : Fin count -> ℝ => finiteArrivalPrefix gaps j) := by
  exact (measurable_kernelCumulativeArrivalVector j.1).comp
    (measurable_kernelFiniteGapPrefix j)

/-- A finite causal endpoint policy with arbitrary rate-free endpoint
response kernels.  At nonterminal stages the endpoint kernel contributes only
its survival mass; at the terminal stage it remains part of the reference
measure, so atoms such as fixed caps are preserved. -/
structure CollapsedFiniteStageEndpointKernelModel (count : ℕ) where
  /-- Rate-free selected-start contribution at the fixed observed history. -/
  startWeight : ℝ≥0∞
  /-- Remaining endpoint-clock law after each visible report prefix. -/
  endKernel : ∀ j : Fin (count + 1), Kernel (Fin j.1 -> ℝ) ℝ
  endKernel_isMarkov : ∀ j, IsMarkovKernel (endKernel j)
  /-- Candidate remaining endpoint clocks cannot occur before the visible
  prefix at which they are selected.  This support condition is needed to
  identify the terminal exponential-race tail with `terminalNoArrivalTail`. -/
  endKernel_nonnegative_support : ∀ j history,
    endKernel j history (Set.Iio (0 : ℝ)) = 0
  /-- Measurability of the nonterminal endpoint-survival factors. -/
  stageSurvival_measurable : ∀ i : Fin count,
    Measurable (fun gaps : Fin count -> ℝ =>
      endKernel i.castSucc (finiteArrivalPrefix gaps i.castSucc)
        (Set.Ioi (gaps i)))

namespace CollapsedFiniteStageEndpointKernelModel

variable {count : ℕ}

/-- The exact probability that an exponential next-report gap exceeds a
candidate endpoint clock.  Unlike the density-only presentation, this is
well-defined for every real endpoint value. -/
def terminalRaceTail (rate : ℝ) : ℝ → ℝ≥0∞ :=
  fun tail => expMeasure rate (Set.Ioi tail)

theorem measurable_terminalRaceTail {rate : ℝ} (rate_pos : 0 < rate) :
    Measurable (terminalRaceTail rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  exact measurable_measure_Ioi (expMeasure rate)

/-- On a physical nonnegative remaining endpoint time, the exact race tail
coincides with the density-model no-arrival factor. -/
theorem terminalRaceTail_eq_terminalNoArrivalTail
    {rate tail : ℝ} (rate_pos : 0 < rate) (tail_nonneg : 0 ≤ tail) :
    terminalRaceTail rate tail =
      CollapsedFiniteStageEndpointModel.terminalNoArrivalTail rate tail :=
  CollapsedFiniteStageEndpointModel.expMeasure_Ioi_eq_terminalNoArrivalTail
    rate_pos tail_nonneg

/-- The survival mass of the candidate endpoint clock at a nonterminal stage. -/
def stageSurvival (M : CollapsedFiniteStageEndpointKernelModel count)
    (gaps : Fin count -> ℝ) (i : Fin count) : ℝ≥0∞ :=
  M.endKernel i.castSucc (finiteArrivalPrefix gaps i.castSucc)
    (Set.Ioi (gaps i))

/-- All rate-free factors accumulated before the terminal endpoint is drawn. -/
def gapWeight (M : CollapsedFiniteStageEndpointKernelModel count)
    (gaps : Fin count -> ℝ) : ℝ≥0∞ :=
  M.startWeight * ∏ i : Fin count, M.stageSurvival gaps i

theorem measurable_gapWeight (M : CollapsedFiniteStageEndpointKernelModel count) :
    Measurable M.gapWeight := by
  unfold gapWeight
  exact measurable_const.mul
    (Finset.measurable_prod Finset.univ fun i _ => M.stageSurvival_measurable i)

/-- The terminal endpoint kernel, indexed by a raw gap block through its
visible arrival-prefix transform. -/
noncomputable def terminalEndpointKernel
    (M : CollapsedFiniteStageEndpointKernelModel count) :
    Kernel (Fin count -> ℝ) ℝ :=
  Kernel.comap (M.endKernel (Fin.last count))
    (fun gaps : Fin count -> ℝ =>
      finiteArrivalPrefix gaps (Fin.last count))
    (measurable_kernelFiniteArrivalPrefix (Fin.last count))

theorem terminalEndpointKernel_isMarkov
    (M : CollapsedFiniteStageEndpointKernelModel count) :
    IsMarkovKernel M.terminalEndpointKernel := by
  unfold terminalEndpointKernel
  letI : IsMarkovKernel (M.endKernel (Fin.last count)) :=
    M.endKernel_isMarkov _
  infer_instance

/-- The terminal endpoint kernel inherits the nonnegative remaining-time
support of the stagewise endpoint policy. -/
theorem terminalEndpointKernel_nonnegative_support
    (M : CollapsedFiniteStageEndpointKernelModel count)
    (gaps : Fin count -> ℝ) :
    M.terminalEndpointKernel gaps (Set.Iio (0 : ℝ)) = 0 := by
  unfold terminalEndpointKernel
  rw [Kernel.comap_apply]
  exact M.endKernel_nonnegative_support (Fin.last count)
    (finiteArrivalPrefix gaps (Fin.last count))

/-- The terminal kernel's exact exponential-race weighting reduces to the
usual no-arrival factor under the explicit endpoint support condition. -/
theorem terminalEndpointKernel_withDensity_terminalRaceTail_eq_noArrivalTail
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) (gaps : Fin count -> ℝ) :
    (M.terminalEndpointKernel gaps).withDensity (terminalRaceTail rate) =
      (M.terminalEndpointKernel gaps).withDensity
        (CollapsedFiniteStageEndpointModel.terminalNoArrivalTail rate) := by
  apply MeasureTheory.withDensity_congr_ae
  have hnonneg : ∀ᵐ tail ∂M.terminalEndpointKernel gaps, 0 ≤ tail := by
    rw [ae_iff]
    have hset : {tail : ℝ | ¬ 0 ≤ tail} = Set.Iio 0 := by
      ext tail
      simp
    rw [hset]
    exact M.terminalEndpointKernel_nonnegative_support gaps
  filter_upwards [hnonneg] with tail htail
  exact terminalRaceTail_eq_terminalNoArrivalTail rate_pos htail

/-- The report-gap law after integrating out all nonterminal endpoint clocks. -/
def weightedGapLaw (M : CollapsedFiniteStageEndpointKernelModel count)
    (rate : ℝ) : Measure (Fin count -> ℝ) :=
  (CollapsedFiniteStageEndpointModel.iidGapLaw count rate).withDensity M.gapWeight

/-- The finite observation law keeps the terminal endpoint's kernel as part of
its base measure, then weights it by the final no-report survival factor. -/
def collapsedObservationLaw (M : CollapsedFiniteStageEndpointKernelModel count)
    (rate : ℝ) : Measure ((Fin count -> ℝ) × ℝ) :=
  ((M.weightedGapLaw rate) ⊗ₘ M.terminalEndpointKernel).withDensity
    (fun p => terminalRaceTail rate p.2)

/-- The likelihood density relative to the gap-volume/terminal-kernel base
measure.  It is meaningful even when the terminal endpoint law is atomic. -/
def rawEndpointKernelDensity (M : CollapsedFiniteStageEndpointKernelModel count)
    (rate : ℝ) (p : (Fin count -> ℝ) × ℝ) : ℝ≥0∞ :=
  exponentialBlockDensity rate count p.1 * M.gapWeight p.1 *
    terminalRaceTail rate p.2

theorem measurable_rawEndpointKernelDensity
    (M : CollapsedFiniteStageEndpointKernelModel count) {rate : ℝ}
    (rate_pos : 0 < rate) :
    Measurable (M.rawEndpointKernelDensity rate) := by
  unfold rawEndpointKernelDensity
  simpa only [Function.comp_apply, mul_assoc] using
    ((measurable_exponentialBlockDensity rate count).comp measurable_fst).mul
      ((M.measurable_gapWeight.comp measurable_fst).mul
        ((measurable_terminalRaceTail rate_pos).comp
          measurable_snd))

/-- The weighted gap law has the rate-dependent exponential block density and
the rate-free nonterminal endpoint-survival contribution. -/
theorem weightedGapLaw_eq_withDensity
    (M : CollapsedFiniteStageEndpointKernelModel count) {rate : ℝ}
    (rate_pos : 0 < rate) :
    M.weightedGapLaw rate =
      (volume : Measure (Fin count -> ℝ)).withDensity
        (fun gaps => exponentialBlockDensity rate count gaps * M.gapWeight gaps) := by
  unfold weightedGapLaw CollapsedFiniteStageEndpointModel.iidGapLaw
  rw [pi_expMeasure_eq_withDensity_exponentialBlock rate_pos count]
  simpa only [Function.comp_def] using
    (MeasureTheory.withDensity_mul (volume : Measure (Fin count -> ℝ))
      (measurable_exponentialBlockDensity rate count)
      M.measurable_gapWeight).symm

/-- The arbitrary-kernel causal observation law has an explicit density
relative to volume on the report gaps and the terminal endpoint response
kernel.  Thus endpoint atoms do not alter the exact Poisson rate factor. -/
theorem collapsedObservationLaw_eq_withDensity_rawEndpointKernelDensity
    (M : CollapsedFiniteStageEndpointKernelModel count) {rate : ℝ}
    (rate_pos : 0 < rate) :
    M.collapsedObservationLaw rate =
      ((volume : Measure (Fin count -> ℝ)) ⊗ₘ M.terminalEndpointKernel).withDensity
        (M.rawEndpointKernelDensity rate) := by
  letI : IsMarkovKernel M.terminalEndpointKernel :=
    M.terminalEndpointKernel_isMarkov
  unfold collapsedObservationLaw rawEndpointKernelDensity
  rw [weightedGapLaw_eq_withDensity M rate_pos]
  rw [Measure.compProd_withDensity_left
    ((measurable_exponentialBlockDensity rate count).mul M.measurable_gapWeight)]
  let base : Measure ((Fin count -> ℝ) × ℝ) :=
    (volume : Measure (Fin count -> ℝ)) ⊗ₘ M.terminalEndpointKernel
  let gapDensity : (Fin count -> ℝ) × ℝ -> ℝ≥0∞ := fun p =>
    exponentialBlockDensity rate count p.1 * M.gapWeight p.1
  let tailDensity : (Fin count -> ℝ) × ℝ -> ℝ≥0∞ := fun p =>
    terminalRaceTail rate p.2
  have hgap : Measurable gapDensity := by
    exact ((measurable_exponentialBlockDensity rate count).mul M.measurable_gapWeight).comp
      measurable_fst
  have htail : Measurable tailDensity := by
    exact (measurable_terminalRaceTail rate_pos).comp
      measurable_snd
  have hraw :
      (fun p : (Fin count -> ℝ) × ℝ =>
        exponentialBlockDensity rate count p.1 * M.gapWeight p.1 *
          terminalRaceTail rate p.2) =
        gapDensity * tailDensity := by
    funext p
    simp only [gapDensity, tailDensity, Pi.mul_apply, mul_assoc]
  change (base.withDensity gapDensity).withDensity tailDensity =
    base.withDensity (fun p =>
      exponentialBlockDensity rate count p.1 * M.gapWeight p.1 *
        terminalRaceTail rate p.2)
  rw [hraw, ← MeasureTheory.withDensity_mul base hgap htail]

end CollapsedFiniteStageEndpointKernelModel

end

end LBG24SpatialUnderreporting
