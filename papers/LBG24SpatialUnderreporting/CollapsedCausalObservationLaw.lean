import LBG24SpatialUnderreporting.ForwardTheorem2PredictableEndpointProduct
import Mathlib.Tactic

/-!
# Finite causal endpoint observation likelihood

This module constructs a finite endpoint-selected observation likelihood measure from
rate-free endpoint-clock kernels and exponential report gaps.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- A report occurs before a candidate endpoint clock. -/
def reportWinsEvent : Set (ℝ × ℝ) := {p | p.1 < p.2}

theorem measurableSet_reportWinsEvent : MeasurableSet reportWinsEvent :=
  measurableSet_lt measurable_fst measurable_snd

/-- A candidate endpoint occurs before the next report gap. -/
def endpointWinsEvent : Set (ℝ × ℝ) := {p | p.2 < p.1}

theorem measurableSet_endpointWinsEvent : MeasurableSet endpointWinsEvent :=
  measurableSet_lt measurable_snd measurable_fst

private theorem swap_preimage_reportWinsEvent :
    Prod.swap ⁻¹' reportWinsEvent = endpointWinsEvent := by
  ext p
  simp [reportWinsEvent, endpointWinsEvent]

private theorem reportWins_slice (B : Set ℝ) (x : ℝ) :
    Prod.mk x ⁻¹' (Prod.fst ⁻¹' B ∩ reportWinsEvent) =
      {y | x ∈ B ∧ x < y} := by
  ext y
  simp [reportWinsEvent]

/--
Projecting an accepted gap-clock pair onto the gap coordinate tilts its law by
the endpoint-clock survival mass.
-/
theorem map_fst_restrict_reportWins_eq_withDensity
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measure.map Prod.fst ((μ.prod ν).restrict reportWinsEvent) =
      μ.withDensity (fun x => ν (Set.Ioi x)) := by
  apply Measure.ext
  intro B hB
  calc
    Measure.map Prod.fst ((μ.prod ν).restrict reportWinsEvent) B =
        ((μ.prod ν).restrict reportWinsEvent) (Prod.fst ⁻¹' B) := by
      rw [Measure.map_apply measurable_fst hB]
    _ = (μ.prod ν) (Prod.fst ⁻¹' B ∩ reportWinsEvent) := by
      rw [Measure.restrict_apply (measurable_fst hB)]
    _ = ∫⁻ x, ν
        (Prod.mk x ⁻¹' (Prod.fst ⁻¹' B ∩ reportWinsEvent)) ∂μ := by
      rw [Measure.prod_apply
        ((measurable_fst hB).inter measurableSet_reportWinsEvent)]
    _ = ∫⁻ x, B.indicator (fun x => ν (Set.Ioi x)) x ∂μ := by
      classical
      apply lintegral_congr
      intro x
      rw [reportWins_slice B x]
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        congr 1
        ext y
        simp [hx]
      · simp [hx]
    _ = ∫⁻ x in B, ν (Set.Ioi x) ∂μ := by
      rw [MeasureTheory.lintegral_indicator hB]
    _ = μ.withDensity (fun x => ν (Set.Ioi x)) B := by
      exact (MeasureTheory.withDensity_apply _ hB).symm

/-- Projecting an accepted endpoint-clock pair onto the endpoint coordinate
tilts its law by the no-report survival mass.  This remains valid when the
endpoint law has atoms. -/
theorem map_snd_restrict_endpointWins_eq_withDensity
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measure.map Prod.snd ((μ.prod ν).restrict endpointWinsEvent) =
      ν.withDensity (fun y => μ (Set.Ioi y)) := by
  have hswap :
      Measure.map Prod.swap ((μ.prod ν).restrict endpointWinsEvent) =
        (ν.prod μ).restrict reportWinsEvent := by
    rw [← swap_preimage_reportWinsEvent]
    rw [← Measure.restrict_map measurable_swap measurableSet_reportWinsEvent,
      Measure.prod_swap]
  calc
    Measure.map Prod.snd ((μ.prod ν).restrict endpointWinsEvent) =
        Measure.map Prod.fst
          (Measure.map Prod.swap ((μ.prod ν).restrict endpointWinsEvent)) := by
      rw [Measure.map_map measurable_fst measurable_swap]
      rfl
    _ = Measure.map Prod.fst ((ν.prod μ).restrict reportWinsEvent) := by
      rw [hswap]
    _ = ν.withDensity (fun y => μ (Set.Ioi y)) := by
      exact map_fst_restrict_reportWins_eq_withDensity ν μ

/-- Upper-tail masses of an s-finite measure on the line vary measurably. -/
theorem measurable_measure_Ioi (mu : Measure ℝ) [SFinite mu] :
    Measurable (fun tail : ℝ => mu (Set.Ioi tail)) := by
  have hindicator : Measurable (fun p : ℝ × ℝ =>
      (Set.Ioi p.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2) := by
    apply Measurable.indicator measurable_const
    exact measurableSet_lt measurable_fst measurable_snd
  have hlintegral := Measurable.lintegral_prod_right
    (ν := mu) (f := fun tail y : ℝ =>
      (Set.Ioi tail).indicator (fun _ => (1 : ℝ≥0∞)) y) hindicator
  convert hlintegral using 1
  funext tail
  rw [MeasureTheory.lintegral_indicator measurableSet_Ioi]
  simp

/-- Marginalizing an accepted product response leaves the nonterminal
acceptance mass and the terminal endpoint's exponential-race tilt. -/
theorem map_terminal_restrict_product_response
    {beta : Type*} [MeasurableSpace beta]
    (mu : Measure beta) (nu xi : Measure ℝ)
    [SFinite mu] [SFinite nu] [SFinite xi]
    (A : Set beta) :
    Measure.map (fun p : beta × (ℝ × ℝ) => p.2.1)
        ((mu.prod (nu.prod xi)).restrict (A ×ˢ reportWinsEvent)) =
      mu A • nu.withDensity (fun tail => xi (Set.Ioi tail)) := by
  rw [← Measure.prod_restrict]
  rw [show (fun p : beta × (ℝ × ℝ) => p.2.1) = Prod.fst ∘ Prod.snd by rfl]
  rw [← Measure.map_map measurable_fst measurable_snd]
  rw [Measure.map_snd_prod]
  rw [Measure.map_smul]
  rw [map_fst_restrict_reportWins_eq_withDensity]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp

/-- The first `j` gaps of a finite gap block. -/
def finiteGapPrefix {count : ℕ} (gaps : Fin count → ℝ)
    (j : Fin (count + 1)) : Fin j.1 → ℝ :=
  fun k => gaps ⟨k.1,
    lt_of_lt_of_le k.2 (Nat.lt_succ_iff.mp j.2)⟩

/-- The arrival epochs visible after the first `j` gaps. -/
def finiteArrivalPrefix {count : ℕ} (gaps : Fin count → ℝ)
    (j : Fin (count + 1)) : Fin j.1 → ℝ :=
  cumulativeArrivalVector j.1 (finiteGapPrefix gaps j)

/--
A finite family of endpoint-clock kernels indexed by the visible arrival
prefix.  The fields specify kernels, their densities, and regularity only.
-/
structure CollapsedFiniteStageEndpointModel (count : ℕ) where
  /-- The rate-free initial factor. -/
  startWeight : ℝ≥0∞
  /-- Candidate remaining-endpoint clocks. -/
  endKernel : ∀ j : Fin (count + 1), Kernel (Fin j.1 → ℝ) ℝ
  endKernel_isMarkov : ∀ j, IsMarkovKernel (endKernel j)
  endDensity : ∀ j : Fin (count + 1), (Fin j.1 → ℝ) → ℝ → ℝ≥0∞
  endDensity_measurable : ∀ j,
    Measurable (Function.uncurry (endDensity j))
  endKernel_eq_withDensity : ∀ j,
    endKernel j = Kernel.withDensity
      (Kernel.const (Fin j.1 → ℝ) (volume : Measure ℝ))
      (endDensity j)
  /-- Measurability of each survival factor evaluated along a finite gap block. -/
  stageSurvival_measurable : ∀ i : Fin count,
    Measurable (fun gaps : Fin count → ℝ =>
      endKernel i.castSucc (finiteArrivalPrefix gaps i.castSucc)
        (Set.Ioi (gaps i)))
  /-- Measurability of the terminal density evaluated at the terminal tail. -/
  terminalDensity_measurable :
    Measurable (fun p : (Fin count → ℝ) × ℝ =>
      endDensity (Fin.last count)
        (finiteArrivalPrefix p.1 (Fin.last count)) p.2)

namespace CollapsedFiniteStageEndpointModel

variable {count : ℕ}

/-- Survival mass of the stage-`i` endpoint clock. -/
def stageSurvival (M : CollapsedFiniteStageEndpointModel count)
    (gaps : Fin count → ℝ) (i : Fin count) : ℝ≥0∞ :=
  M.endKernel i.castSucc (finiteArrivalPrefix gaps i.castSucc)
    (Set.Ioi (gaps i))

/--
At a fixed visible prefix, integrating out the endpoint clock on the
report-wins event leaves the survival tilt on the exponential gap law.
-/
theorem local_reportWins_step_eq_withDensity
    (M : CollapsedFiniteStageEndpointModel count) (rate : ℝ) (h_rate : 0 < rate)
    (i : Fin (count + 1)) (history : Fin i.1 → ℝ) :
    Measure.map Prod.fst
      (((expMeasure rate).prod (M.endKernel i history)).restrict reportWinsEvent) =
        (expMeasure rate).withDensity
          (fun gap => M.endKernel i history (Set.Ioi gap)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  letI : IsMarkovKernel (M.endKernel i) := M.endKernel_isMarkov i
  exact map_fst_restrict_reportWins_eq_withDensity _ _

/-- Terminal endpoint density in remaining-time coordinates. -/
def terminalDensity (M : CollapsedFiniteStageEndpointModel count)
    (p : (Fin count → ℝ) × ℝ) : ℝ≥0∞ :=
  M.endDensity (Fin.last count)
    (finiteArrivalPrefix p.1 (Fin.last count)) p.2

/-- Rate-free factors after integrating out nonterminal endpoint clocks. -/
def endpointWeight (M : CollapsedFiniteStageEndpointModel count)
    (p : (Fin count → ℝ) × ℝ) : ℝ≥0∞ :=
  M.startWeight *
    (∏ i : Fin count, M.stageSurvival p.1 i) *
      M.terminalDensity p

theorem measurable_endpointWeight (M : CollapsedFiniteStageEndpointModel count) :
    Measurable M.endpointWeight := by
  unfold endpointWeight
  exact (measurable_const.mul
    (Finset.measurable_prod Finset.univ fun i _ =>
      (M.stageSurvival_measurable i).comp measurable_fst)).mul
        M.terminalDensity_measurable

/-- The probability density of no additional report before a nonnegative tail. -/
def terminalNoArrivalTail (rate : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ici (0 : ℝ)).indicator
    (fun tail => ENNReal.ofReal (Real.exp (-(rate * tail))))

theorem measurable_terminalNoArrivalTail (rate : ℝ) :
    Measurable (terminalNoArrivalTail rate) := by
  unfold terminalNoArrivalTail
  apply Measurable.indicator
  · fun_prop
  · exact measurableSet_Ici

/-- The terminal no-report factor equals the mass of a surviving exponential gap. -/
theorem expMeasure_Ioi_eq_terminalNoArrivalTail
    {rate tail : ℝ} (h_rate : 0 < rate) (h_tail : 0 ≤ tail) :
    expMeasure rate (Set.Ioi tail) = terminalNoArrivalTail rate tail := by
  unfold terminalNoArrivalTail
  rw [Set.indicator_of_mem (show tail ∈ Set.Ici (0 : ℝ) from h_tail)]
  let model : AppliedModelingLib.Probability.Exponential.Model := ⟨rate, h_rate⟩
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure h_rate
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  change (model.measure (Set.Ioi tail)).toReal =
    (ENNReal.ofReal (Real.exp (-(rate * tail)))).toReal
  rw [model.measure_Ioi_toReal h_tail]
  exact (ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))).symm

/-- Endpoint factors including the terminal no-report tail. -/
def terminalWeight (M : CollapsedFiniteStageEndpointModel count)
    (rate : ℝ) (p : (Fin count → ℝ) × ℝ) : ℝ≥0∞ :=
  M.endpointWeight p * terminalNoArrivalTail rate p.2

theorem measurable_terminalWeight (M : CollapsedFiniteStageEndpointModel count)
    (rate : ℝ) : Measurable (M.terminalWeight rate) :=
  M.measurable_endpointWeight.mul
    ((measurable_terminalNoArrivalTail rate).comp measurable_snd)

/-- The iid law of a finite block of exponential report gaps. -/
def iidGapLaw (count : ℕ) (rate : ℝ) : Measure (Fin count → ℝ) :=
  Measure.pi (fun _ : Fin count => expMeasure rate)

/--
The finite fixed-history observation likelihood measure in gap-plus-terminal-tail
coordinates.  Its initial factor is a density evaluated at a selected start,
so this need not be a submeasure of a probability law.
-/
def collapsedObservationLaw (M : CollapsedFiniteStageEndpointModel count)
    (rate : ℝ) : Measure ((Fin count → ℝ) × ℝ) :=
  ((iidGapLaw count rate).prod (volume : Measure ℝ)).withDensity
    (M.terminalWeight rate)

/-- The density of the fixed-history observation likelihood measure. -/
def rawGapTailDensity (M : CollapsedFiniteStageEndpointModel count)
    (rate : ℝ) (p : (Fin count → ℝ) × ℝ) : ℝ≥0∞ :=
  exponentialBlockDensity rate count p.1 * M.terminalWeight rate p

/--
The fixed-history observation likelihood measure has the product density of
its exponential gaps, endpoint-clock survival factors, terminal endpoint
density, and terminal no-report tail.
-/
theorem collapsedObservationLaw_eq_withDensity_rawGapTailDensity
    (M : CollapsedFiniteStageEndpointModel count) {rate : ℝ}
    (h_rate : 0 < rate) :
    M.collapsedObservationLaw rate =
      ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (M.rawGapTailDensity rate) := by
  unfold collapsedObservationLaw iidGapLaw rawGapTailDensity
  rw [pi_expMeasure_eq_withDensity_exponentialBlock h_rate count]
  rw [MeasureTheory.prod_withDensity_left
    (measurable_exponentialBlockDensity rate count)]
  simpa [Function.comp_def] using
    (MeasureTheory.withDensity_mul
    ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ))
    ((measurable_exponentialBlockDensity rate count).comp measurable_fst)
    (M.measurable_terminalWeight rate)).symm

end CollapsedFiniteStageEndpointModel

end

end LBG24SpatialUnderreporting
