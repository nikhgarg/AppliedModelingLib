import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalShift
import Mathlib.Tactic

/-!
# Predecessor-gap factors for a marked two-sided renewal input

The one-arrival Lindley update at a Palm tag uses one innovation that the
predecessor's causal queue state does not read: the physical interarrival gap
from the predecessor to the current tag.  This module separates that gap from
the predecessor's *actual causal input* on the direct marked-renewal carrier.

The full recentered marked sample is deliberately not used as the second
factor: its arrival coordinate at index zero is exactly the displayed gap.
Only the work at the predecessor and the still older work/gap tails are kept.
No queue state, fixed-point law, or response-time tail is asserted here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Split the negative half of a two-sided gap path at its most recent
coordinate.  The first component is the gap with integer index `-1`; the
tail starts at integer index `-2`. -/
def twoSidedPredecessorGapOlderPastFactors (omega : ℤ → ℝ) :
    ℝ × (ℕ → ℝ) :=
  headTail (twoSidedHeadPositiveNegative omega).2

theorem twoSidedPredecessorGapOlderPastFactors_apply (omega : ℤ → ℝ) :
    twoSidedPredecessorGapOlderPastFactors omega =
      (twoSidedGap (Int.negSucc 0) omega,
        fun n => twoSidedGap (Int.negSucc (n + 1)) omega) := by
  rfl

theorem measurable_twoSidedPredecessorGapOlderPastFactors :
    Measurable twoSidedPredecessorGapOlderPastFactors := by
  exact measurable_headTail.comp
    (measurable_snd.comp measurable_twoSidedHeadPositiveNegative)

/-- The literal predecessor gap and the older negative tail have the product
of their iid exponential laws.  Positive and central path coordinates have
been integrated out, not identified with either factor. -/
theorem map_twoSidedPredecessorGapOlderPastFactors_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map twoSidedPredecessorGapOlderPastFactors
      (twoSidedInterarrivalMeasure rate) =
      (expMeasure rate).prod (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  calc
    Measure.map twoSidedPredecessorGapOlderPastFactors
        (twoSidedInterarrivalMeasure rate) =
        Measure.map headTail
          (Measure.map Prod.snd
            (Measure.map twoSidedHeadPositiveNegative
              (twoSidedInterarrivalMeasure rate))) := by
          symm
          rw [Measure.map_map measurable_headTail measurable_snd,
            Measure.map_map
              (measurable_headTail.comp measurable_snd)
              measurable_twoSidedHeadPositiveNegative]
          rfl
    _ = Measure.map headTail (exponentialInterarrivalMeasure rate) := by
          rw [map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure hrate,
            Measure.map_snd_prod, measure_univ, one_smul]
    _ = (expMeasure rate).prod (exponentialInterarrivalMeasure rate) :=
          map_headTail_exponentialInterarrivalMeasure hrate

/-- The predecessor-to-current physical gap, followed by exactly the causal
input read by a predecessor-centered FCFS replay: its own work, older work,
and older interarrival gaps. -/
def markedRenewalPredecessorGapShiftedPastFactors
    (z : TwoSidedMarkedRenewalSample) :
    ℝ × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
  let arrival := twoSidedPredecessorGapOlderPastFactors z.1
  let work := twoSidedPredecessorGapOlderPastFactors z.2
  (arrival.1, (work, arrival.2))

theorem measurable_markedRenewalPredecessorGapShiftedPastFactors :
    Measurable markedRenewalPredecessorGapShiftedPastFactors := by
  unfold markedRenewalPredecessorGapShiftedPastFactors
  exact
    (measurable_fst.comp
      (measurable_twoSidedPredecessorGapOlderPastFactors.comp measurable_fst)).prodMk
      ((measurable_twoSidedPredecessorGapOlderPastFactors.comp measurable_snd).prodMk
        (measurable_snd.comp
          (measurable_twoSidedPredecessorGapOlderPastFactors.comp measurable_fst)))

/-- The harmless reassociation/swap that turns independent arrival and work
factor pairs into a predecessor gap followed by its causal input. -/
private def predecessorGapFactorRearrange :
    ((ℝ × (ℕ → ℝ)) × (ℝ × (ℕ → ℝ))) →
      ℝ × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
  fun x => (x.1.1, (x.2, x.1.2))

private theorem measurable_predecessorGapFactorRearrange :
    Measurable predecessorGapFactorRearrange := by
  exact (measurable_id.prodMap measurable_swap).comp
    MeasurableEquiv.prodAssoc.measurable

private theorem map_predecessorGapFactorRearrange
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map predecessorGapFactorRearrange
      (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
        ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ)))) =
      (expMeasure rate).prod
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure rate)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  calc
    Measure.map predecessorGapFactorRearrange
        (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ)))) =
        Measure.map (Prod.map id Prod.swap)
          (Measure.map MeasurableEquiv.prodAssoc
            (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
              ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))))) := by
          symm
          rw [Measure.map_map
            (measurable_id.prodMap measurable_swap)
            MeasurableEquiv.prodAssoc.measurable]
          rfl
    _ = Measure.map (Prod.map id Prod.swap)
          ((expMeasure rate).prod
            ((exponentialInterarrivalMeasure rate).prod
              ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))))) := by
          rw [Measure.prodAssoc_prod]
    _ = (expMeasure rate).prod
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure rate)) := by
          rw [← Measure.map_prod_map _ _ measurable_id measurable_swap,
            Measure.map_id, Measure.prod_swap]

/-- Exact direct-source product law for the predecessor gap and the complete
input used by the predecessor-centered causal replay.  In particular, this
does not incorrectly claim independence from a full shifted sample that
still exposes the predecessor gap at its arrival coordinate zero. -/
theorem map_markedRenewalPredecessorGapShiftedPastFactors_twoSidedMarkedRenewalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map markedRenewalPredecessorGapShiftedPastFactors
      (twoSidedMarkedRenewalMeasure rate) =
      (expMeasure rate).prod
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure rate)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let arrival := twoSidedPredecessorGapOlderPastFactors
  let work := twoSidedPredecessorGapOlderPastFactors
  have hfactor :
      Measure.map (Prod.map arrival work) (twoSidedMarkedRenewalMeasure rate) =
        (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ)))) := by
    change Measure.map (Prod.map arrival work)
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) = _
    rw [← Measure.map_prod_map _ _
      measurable_twoSidedPredecessorGapOlderPastFactors
      measurable_twoSidedPredecessorGapOlderPastFactors,
      map_twoSidedPredecessorGapOlderPastFactors_twoSidedInterarrivalMeasure hrate,
      map_twoSidedPredecessorGapOlderPastFactors_twoSidedInterarrivalMeasure (by norm_num)]
  calc
    Measure.map markedRenewalPredecessorGapShiftedPastFactors
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map predecessorGapFactorRearrange
          (Measure.map (Prod.map arrival work)
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map measurable_predecessorGapFactorRearrange
            (measurable_twoSidedPredecessorGapOlderPastFactors.prodMap
              measurable_twoSidedPredecessorGapOlderPastFactors)]
          rfl
    _ = Measure.map predecessorGapFactorRearrange
        (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ)))) := by
          rw [hfactor]
    _ = (expMeasure rate).prod
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure rate)) :=
      map_predecessorGapFactorRearrange hrate

/-- The displayed second factor is exactly the part of a one-arrival
recentered sample consumed by the direct pre-tag replay: tag work, older
work, and older gaps. -/
theorem markedRenewalPredecessorGapShiftedPastFactors_eq_shiftedCausalFactors
    (z : TwoSidedMarkedRenewalSample) :
    markedRenewalPredecessorGapShiftedPastFactors z =
      (markedRenewalPastGap z 0,
        markedRenewalTagWorkPastFactors
          (twoSidedMarkedRenewalIndexShift (-1) z)) := by
  rcases z with ⟨arrival, work⟩
  change
    (twoSidedGap (Int.negSucc 0) arrival,
      ((twoSidedGap (Int.negSucc 0) work,
        fun n => twoSidedGap (Int.negSucc (n + 1)) work),
        fun n => twoSidedGap (Int.negSucc (n + 1)) arrival)) =
      (twoSidedGap (Int.negSucc 0) arrival,
        ((twoSidedGap (0 + (-1)) work,
          fun n => twoSidedGap (Int.negSucc n + (-1)) work),
          fun n => twoSidedGap (Int.negSucc n + (-1)) arrival))
  congr 1

end

end AppliedModelingLib.Probability.PoissonProcess
