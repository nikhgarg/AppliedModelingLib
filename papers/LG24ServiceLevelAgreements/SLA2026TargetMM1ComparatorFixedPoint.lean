import AppliedModelingLib.Queueing.Lindley.RemotePastShift
import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalShift
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorResponse
import Mathlib.Tactic

/-!
# Causal fixed point for the direct target M/M/1 comparator

This module proves the first stationary recursion on the actual direct
Poisson/exponential marked-renewal carrier.  Recentring the tag one literal
arrival into the past leaves the iid input law unchanged.  On samples where
the remote-past constructions coalesce, the present pre-tag workload is the
one-step reflected update of that earlier tag's completed workload.

This is a source-native causal identity only.  It does not solve the
fixed-point law, assert an exponential response tail, or invoke the legacy
uniformized M/M/1 carrier.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace DirectMarkedRenewalComparator

/-- Moving the tag one arrival into the literal past turns its remote work
coordinates into the tail of the original remote work sequence. -/
theorem remotePastBatch_indexShift_negOne_eq_remotePastTail
    (z : TwoSidedMarkedRenewalSample) :
    remotePastBatch (twoSidedMarkedRenewalIndexShift (-1) z) =
      remotePastTail (remotePastBatch z) := by
  funext n
  unfold remotePastBatch markedRenewalPastWork twoSidedMarkedRenewalIndexShift
    twoSidedGapIndexShift remotePastTail twoSidedGap
  congr 1

/-- The same one-step recentering identity holds for the literal service
amounts between target arrivals. -/
theorem remotePastService_indexShift_negOne_eq_remotePastTail
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) :
    remotePastService serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) =
      remotePastTail (remotePastService serviceRate z) := by
  funext n
  unfold remotePastService markedRenewalPastGap twoSidedMarkedRenewalIndexShift
    twoSidedGapIndexShift remotePastTail twoSidedGap
  congr 2

/-- A finite literal replay with one extra past job is the exact reflected
update of the replay seen from the predecessor tag.  The final service is
the actual gap from that predecessor to the current tag. -/
theorem finitePreTagWorkload_succ_eq_indexShift_negOne_update
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) (N : Nat) :
    finitePreTagWorkload serviceRate z (N + 1) =
      max
        (finitePreTagWorkload serviceRate
          (twoSidedMarkedRenewalIndexShift (-1) z) N +
          remotePastBatch z 0 - remotePastService serviceRate z 0) 0 := by
  unfold finitePreTagWorkload
  rw [lateBatchPreWorkload_reverseRemotePast_succ_eq_tail_update]
  rw [← remotePastBatch_indexShift_negOne_eq_remotePastTail,
    ← remotePastService_indexShift_negOne_eq_remotePastTail]

/-- On coalescent samples, the literal pre-tag workload satisfies the
causal one-arrival Lindley fixed-point equation.  The predecessor response
uses no information from the gap leading to the current tag. -/
theorem preTagWorkload_eq_indexShift_negOne_update_of_coalesces
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z)
    (hshiftcoal : PreTagCoalesces serviceRate
      (twoSidedMarkedRenewalIndexShift (-1) z)) :
    preTagWorkload serviceRate z =
      max
        (preTagWorkload serviceRate
          (twoSidedMarkedRenewalIndexShift (-1) z) +
          remotePastBatch z 0 - remotePastService serviceRate z 0) 0 := by
  rcases preTagWorkload_eq_finite_of_coalesces serviceRate z hcoal with
    ⟨K, hK⟩
  rcases preTagWorkload_eq_finite_of_coalesces serviceRate
    (twoSidedMarkedRenewalIndexShift (-1) z) hshiftcoal with ⟨Kshift, hKshift⟩
  let N := max K Kshift
  have hN : K ≤ N + 1 := by
    exact (le_max_left _ _).trans (Nat.le_succ _)
  have hNshift : Kshift ≤ N := by
    exact le_max_right _ _
  calc
    preTagWorkload serviceRate z = finitePreTagWorkload serviceRate z (N + 1) :=
      hK (N + 1) hN
    _ = max
        (finitePreTagWorkload serviceRate
          (twoSidedMarkedRenewalIndexShift (-1) z) N +
          remotePastBatch z 0 - remotePastService serviceRate z 0) 0 :=
      finitePreTagWorkload_succ_eq_indexShift_negOne_update serviceRate z N
    _ = max
        (preTagWorkload serviceRate
          (twoSidedMarkedRenewalIndexShift (-1) z) +
          remotePastBatch z 0 - remotePastService serviceRate z 0) 0 := by
      rw [hKshift N hNshift]

/-- Under strict direct stability, the causal one-arrival fixed point holds
almost surely on the literal marked-renewal source measure. -/
theorem ae_preTagWorkload_eq_indexShift_negOne_update_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      preTagWorkload serviceRate z =
        max
          (preTagWorkload serviceRate
            (twoSidedMarkedRenewalIndexShift (-1) z) +
            remotePastBatch z 0 - remotePastService serviceRate z 0) 0 := by
  have hcoal : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      PreTagCoalesces serviceRate z :=
    ae_preTagCoalesces_of_rate_lt hrate hstable
  have hshiftMap : MeasurePreserving (twoSidedMarkedRenewalIndexShift (-1))
      (twoSidedMarkedRenewalMeasure rate) (twoSidedMarkedRenewalMeasure rate) :=
    twoSidedMarkedRenewalIndexShift_measurePreserving hrate (-1)
  have hshiftCoalMap : ∀ᵐ x ∂Measure.map
      (twoSidedMarkedRenewalIndexShift (-1)) (twoSidedMarkedRenewalMeasure rate),
      PreTagCoalesces serviceRate x := by
    rw [hshiftMap.map_eq]
    exact hcoal
  have hshiftCoal : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      PreTagCoalesces serviceRate (twoSidedMarkedRenewalIndexShift (-1) z) :=
    Measure.tendsto_ae_map hshiftMap.measurable.aemeasurable hshiftCoalMap
  filter_upwards [hcoal, hshiftCoal] with z hz hzshift
  exact preTagWorkload_eq_indexShift_negOne_update_of_coalesces
    serviceRate z hz hzshift

/-- The corresponding source-tag response identity keeps the current tag's
own work outside the predecessor update.  In particular, the tagged job is
not accidentally replayed as a past batch. -/
theorem response_eq_indexShift_negOne_update_of_coalesces
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z)
    (hshiftcoal : PreTagCoalesces serviceRate
      (twoSidedMarkedRenewalIndexShift (-1) z)) :
    response serviceRate z =
      (max
        (preTagWorkload serviceRate
          (twoSidedMarkedRenewalIndexShift (-1) z) +
          remotePastBatch z 0 - remotePastService serviceRate z 0) 0 +
        tagWork z) / serviceRate := by
  unfold response
  rw [preTagWorkload_eq_indexShift_negOne_update_of_coalesces
    serviceRate z hcoal hshiftcoal]

/-- Strict direct stability makes the literal tagged response satisfy the
same causal update almost surely. -/
theorem ae_response_eq_indexShift_negOne_update_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      response serviceRate z =
        (max
          (preTagWorkload serviceRate
            (twoSidedMarkedRenewalIndexShift (-1) z) +
            remotePastBatch z 0 - remotePastService serviceRate z 0) 0 +
          tagWork z) / serviceRate := by
  filter_upwards [ae_preTagWorkload_eq_indexShift_negOne_update_of_rate_lt
    hrate hstable] with z hz
  unfold response
  rw [hz]

/-- The response observed after a deterministic one-arrival recentering has
the same direct source law as the original response.  This is an iid
arrival-index symmetry, not an asserted closed form for that law. -/
theorem response_indexShift_negOne_hasLaw_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    HasLaw
      (fun z : TwoSidedMarkedRenewalSample =>
        response serviceRate (twoSidedMarkedRenewalIndexShift (-1) z))
      (Measure.map (response serviceRate) (twoSidedMarkedRenewalMeasure rate))
      (twoSidedMarkedRenewalMeasure rate) := by
  exact (response_hasLaw_of_rate_lt hrate hstable).comp
    (twoSidedMarkedRenewalIndexShift_measurePreserving hrate (-1)).hasLaw

end DirectMarkedRenewalComparator

end

end LG24ServiceLevelAgreements
