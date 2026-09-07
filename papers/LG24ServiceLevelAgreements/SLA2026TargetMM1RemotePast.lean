import AppliedModelingLib.Queueing.Lindley.RemotePastCutoff
import LG24ServiceLevelAgreements.SLA2026TargetPalmPastRenewalReward
import Mathlib.Tactic

/-!
# Direct target-class remote-past comparator input

This module builds the scalar remote-past input needed for the target-class
constant-rate comparator directly from the SLA target Palm gap and work
paths.  The past job with label `Int.negSucc n` contributes its literal work,
then receives comparator service over the literal gap from that job to its
newer neighbour.  Thus reversing the outward past enumeration is a genuine
chronological service-before-arrival execution; no multiclass event merge,
virtual terminal batch, or uniformized M/M/1 carrier is used here.

The resulting cutoff/coalescence statements construct only a scalar
same-source comparator state.  They do not yet identify its stationary law,
its response functional, or a GPS response-tail bound.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal work of the `n`th target arrival before the Palm tag, with
`n = 0` the arrival immediately before time zero. -/
def stationaryAdmittedTargetPalmRemotePastBatch
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  markedRenewalPastWork (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- Constant-rate comparator service available after the `n`th target past
arrival and before its newer neighbour.  For `n = 0`, this is service on the
literal interval from the final past target arrival to the Palm epoch. -/
def stationaryAdmittedTargetPalmRemotePastService
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  serviceRate *
    markedRenewalPastGap (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- The target-only net increment in outward-from-the-tag order. -/
def stationaryAdmittedTargetPalmRemotePastNetIncrement
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  stationaryAdmittedTargetPalmRemotePastBatch target z n -
    stationaryAdmittedTargetPalmRemotePastService target serviceRate z n

/-- The past-gap service interval is the literal physical-time interval from
the indicated target arrival to its newer target neighbour (the Palm tag when
`n = 0`). -/
theorem stationaryAdmittedTargetPalmRemotePastGap_eq_newerArrival_sub_arrival
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) :
    markedRenewalPastGap (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n =
      candidatePalmArrival z.1.1 (Int.negSucc n + 1) -
        candidatePalmArrival z.1.1 (Int.negSucc n) := by
  have hstep := candidatePalmArrival_add_one z.1.1 (Int.negSucc n)
  change z.1.1 (Int.negSucc n) =
    candidatePalmArrival z.1.1 (Int.negSucc n + 1) -
      candidatePalmArrival z.1.1 (Int.negSucc n)
  linarith

/-- The comparator service amount is its declared constant rate times that
literal source interval. -/
theorem stationaryAdmittedTargetPalmRemotePastService_eq_rate_mul_newerArrival_sub_arrival
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) :
    stationaryAdmittedTargetPalmRemotePastService target serviceRate z n =
      serviceRate *
        (candidatePalmArrival z.1.1 (Int.negSucc n + 1) -
          candidatePalmArrival z.1.1 (Int.negSucc n)) := by
  rw [stationaryAdmittedTargetPalmRemotePastService,
    stationaryAdmittedTargetPalmRemotePastGap_eq_newerArrival_sub_arrival]

/-- The first `n + 1` outward target increments are exactly the marked
renewal net input over the literal target source history. -/
theorem stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_succ
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (n : Nat) :
    remotePastCumulativeNetInput
      (stationaryAdmittedTargetPalmRemotePastNetIncrement target serviceRate z)
      (n + 1) =
      markedRenewalPastCumulativeNetWork serviceRate
        (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n := by
  rfl

/-- The direct target-Palm source has the marked-renewal net-input average
specified by its own rate and work marks. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmPastCumulativeNetWork_div_nat_succ
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : Nat =>
          markedRenewalPastCumulativeNetWork serviceRate
            (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n /
            ((n + 1 : Nat) : Real))
        atTop (nhds (1 - serviceRate / M.admittedRate target)) := by
  have hlaw := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hmap : ∀ᵐ x ∂Measure.map
      (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : Nat =>
          markedRenewalPastCumulativeNetWork serviceRate x n /
            ((n + 1 : Nat) : Real))
        atTop (nhds (1 - serviceRate / M.admittedRate target)) := by
    rw [hlaw.map_eq]
    exact ae_tendsto_markedRenewalPastCumulativeNetWork_div_nat_succ
      (M.admittedRate_pos target)
  exact Measure.tendsto_ae_map hlaw.aemeasurable hmap

/-- The same average law expressed through the actual scalar remote-past
comparator increments. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_succ_div
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : Nat =>
          remotePastCumulativeNetInput
            (stationaryAdmittedTargetPalmRemotePastNetIncrement
              target serviceRate z) (n + 1) /
            ((n + 1 : Nat) : Real))
        atTop (nhds (1 - serviceRate / M.admittedRate target)) := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPalmPastCumulativeNetWork_div_nat_succ
      target serviceRate] with z hz
  have heq :
      (fun n : Nat =>
        remotePastCumulativeNetInput
          (stationaryAdmittedTargetPalmRemotePastNetIncrement
            target serviceRate z) (n + 1) /
          ((n + 1 : Nat) : Real)) =
        fun n : Nat =>
          markedRenewalPastCumulativeNetWork serviceRate
            (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n /
            ((n + 1 : Nat) : Real) := by
    funext n
    rw [stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_succ]
  rw [heq]
  exact hz

/-- If the target's own direct admitted rate is below the comparison service
rate, its literal remote-past scalar net input tends to `-∞`. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_atBot_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (remotePastCumulativeNetInput
          (stationaryAdmittedTargetPalmRemotePastNetIncrement
            target serviceRate z))
        atTop atBot := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_succ_div
      target serviceRate] with z hz
  have hlimit_neg : 1 - serviceRate / M.admittedRate target < 0 :=
    M.stationaryAdmittedTargetPalmNetWorkLimit_neg_of_admittedRate_lt
      target serviceRate hstable
  have hsucc_atBot : Tendsto
      (fun n : Nat =>
        remotePastCumulativeNetInput
          (stationaryAdmittedTargetPalmRemotePastNetIncrement
            target serviceRate z) (n + 1))
      atTop atBot :=
    tendsto_atBot_of_tendsto_div_nat_succ_neg _ _ hz hlimit_neg
  exact tendsto_atBot_of_tendsto_succ_atBot _ hsucc_atBot

/-- With strictly stable target-class load, a direct target-Palm sample has a
finite literal pre-batch cutoff for the same-source scalar comparator.  The
zero state is before a target arrival batch, so this statement does not claim
that the batch at that source epoch is empty. -/
theorem ae_exists_stationaryAdmittedTargetPalmRemotePastComparatorCutoff_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ K, ∀ N ≥ K,
        lateBatchPreWorkload
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z) N)
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastService target serviceRate z) N)
          (N - K) = 0 := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_atBot_of_admittedRate_lt
      target serviceRate hstable] with z hz
  exact exists_lateBatchPreWorkload_reverseRemotePast_cutoff_of_tendsto_atBot
    (stationaryAdmittedTargetPalmRemotePastBatch target z)
    (stationaryAdmittedTargetPalmRemotePastService target serviceRate z) hz

/-- The target-only comparator has a source-defined pre-tag workload that
coalesces across all sufficiently remote literal start points. -/
theorem ae_exists_stationaryAdmittedTargetPalmRemotePastComparatorCoalescence_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ K, ∀ N ≥ K,
        lateBatchPreWorkload
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z) N)
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastService target serviceRate z) N) N =
          lateBatchPreWorkload
            (reverseRemotePastIncrement
              (stationaryAdmittedTargetPalmRemotePastBatch target z) K)
            (reverseRemotePastIncrement
              (stationaryAdmittedTargetPalmRemotePastService target serviceRate z) K) K := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPalmRemotePastCumulativeNetInput_atBot_of_admittedRate_lt
      target serviceRate hstable] with z hz
  exact exists_lateBatchPreWorkload_reverseRemotePast_coalescence_at_present_of_tendsto_atBot
    (stationaryAdmittedTargetPalmRemotePastBatch target z)
    (stationaryAdmittedTargetPalmRemotePastService target serviceRate z) hz

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
