import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalPredecessorFactors
import Mathlib.Tactic

/-!
# Three-way predecessor innovations for a marked two-sided renewal input

The one-arrival Lindley update at a Palm tag has three logically distinct
pieces of input: the physical predecessor-to-current gap, the predecessor
job's own work mark, and the older marked history that determines the
predecessor's pre-arrival state.  This module exposes their literal product
law on the direct two-sided marked-renewal carrier.

The result deliberately retains the older work and gap paths rather than a
full recentered sample: the latter would expose the displayed physical gap at
its arrival coordinate zero and would not be independent of it.  No workload,
fixed point, or response-time tail is asserted here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The physical predecessor-to-current gap, the predecessor job's own work,
and the strictly older work/gap paths.  The last component is exactly the
causal input from which the predecessor's pre-arrival workload can be
replayed. -/
def markedRenewalPredecessorInnovationStateFactors
    (z : TwoSidedMarkedRenewalSample) :
    ℝ × (ℝ × ((ℕ → ℝ) × (ℕ → ℝ))) :=
  let x := markedRenewalPredecessorGapShiftedPastFactors z
  (x.1, (x.2.1.1, (x.2.1.2, x.2.2)))

theorem measurable_markedRenewalPredecessorInnovationStateFactors :
    Measurable markedRenewalPredecessorInnovationStateFactors := by
  unfold markedRenewalPredecessorInnovationStateFactors
  let h := measurable_markedRenewalPredecessorGapShiftedPastFactors
  have hsecond : Measurable (fun z : TwoSidedMarkedRenewalSample =>
      (markedRenewalPredecessorGapShiftedPastFactors z).2) :=
    measurable_snd.comp h
  exact
    (measurable_fst.comp h).prodMk
      ((measurable_fst.comp (measurable_fst.comp hsecond)).prodMk
        ((measurable_snd.comp (measurable_fst.comp hsecond)).prodMk
          (measurable_snd.comp hsecond)))

/-- Reassociate the already-proved predecessor factor pair into the three
literal innovations used by a one-arrival workload update. -/
private def predecessorInnovationStateReassociate :
    ℝ × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) →
      ℝ × (ℝ × ((ℕ → ℝ) × (ℕ → ℝ))) :=
  fun x => (x.1, (x.2.1.1, (x.2.1.2, x.2.2)))

private theorem measurable_predecessorInnovationStateReassociate :
    Measurable predecessorInnovationStateReassociate := by
  let hsecond : Measurable (fun x : ℝ × ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) => x.2) :=
    measurable_snd
  exact measurable_fst.prodMk
    ((measurable_fst.comp (measurable_fst.comp hsecond)).prodMk
      ((measurable_snd.comp (measurable_fst.comp hsecond)).prodMk
        (measurable_snd.comp hsecond)))

/-- Exact product law for the gap `A_{-1}`, predecessor work `B_{-1}`, and
the strictly older causal marked history.  Both innovations are independent
of that older history, and the theorem does not identify a full shifted
sample with the causal history. -/
theorem map_markedRenewalPredecessorInnovationStateFactors_twoSidedMarkedRenewalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map markedRenewalPredecessorInnovationStateFactors
      (twoSidedMarkedRenewalMeasure rate) =
      (expMeasure rate).prod
        ((expMeasure (1 : ℝ)).prod
          ((exponentialInterarrivalMeasure (1 : ℝ)).prod
            (exponentialInterarrivalMeasure rate))) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  calc
    Measure.map markedRenewalPredecessorInnovationStateFactors
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map predecessorInnovationStateReassociate
          (Measure.map markedRenewalPredecessorGapShiftedPastFactors
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map measurable_predecessorInnovationStateReassociate
            measurable_markedRenewalPredecessorGapShiftedPastFactors]
          rfl
    _ = Measure.map predecessorInnovationStateReassociate
        ((expMeasure rate).prod
          (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
            (exponentialInterarrivalMeasure rate))) := by
          rw [map_markedRenewalPredecessorGapShiftedPastFactors_twoSidedMarkedRenewalMeasure
            hrate]
    _ = (expMeasure rate).prod
        ((expMeasure (1 : ℝ)).prod
          ((exponentialInterarrivalMeasure (1 : ℝ)).prod
            (exponentialInterarrivalMeasure rate))) := by
          change Measure.map (Prod.map id MeasurableEquiv.prodAssoc)
            ((expMeasure rate).prod
              (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
                (exponentialInterarrivalMeasure rate))) = _
          rw [← Measure.map_prod_map _ _ measurable_id
            MeasurableEquiv.prodAssoc.measurable, Measure.map_id,
            Measure.prodAssoc_prod]

/-- Coordinate form of the three-way factor.  In particular the older paths
start at index `-2`, while the displayed job work and physical gap are both
at index `-1`. -/
theorem markedRenewalPredecessorInnovationStateFactors_apply
    (z : TwoSidedMarkedRenewalSample) :
    markedRenewalPredecessorInnovationStateFactors z =
      (markedRenewalPastGap z 0,
        (markedRenewalPastWork z 0,
          ((fun n => markedRenewalPastWork z (n + 1)),
            fun n => markedRenewalPastGap z (n + 1)))) := by
  rfl

end

end AppliedModelingLib.Probability.PoissonProcess
