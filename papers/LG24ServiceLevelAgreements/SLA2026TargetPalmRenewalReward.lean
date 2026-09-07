import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalReward
import LG24ServiceLevelAgreements.SLA2026StationaryAdmittedPalmInputs

/-!
# Target Palm marked renewal-reward laws for the SLA source

This module transports the generic marked two-sided renewal-reward laws to
the literal direct-admitted target coordinate of the SLA target/passive Palm
carrier.  It is source-input only: it contains no GPS state, reset,
completion, response, or stationary-queue claim.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal target gap/work pair retained by the target/passive Palm
carrier.  The passive coordinates remain in the ambient sample and are not
replaced by a synthetic target input. -/
def stationaryAdmittedTargetPalmMarkedRenewalSample
    (target : Category) :
    StationaryAdmittedTargetPassiveTaggedInput target →
      TwoSidedMarkedRenewalSample :=
  fun z => z.1

/-- The forward renewal endpoint after the target work-mark labels
`0, ..., n`.  In the Palm indexing this is the physical target arrival
labelled `n + 1`; the endpoint convention is recorded explicitly below. -/
def stationaryAdmittedTargetPalmArrivalEpoch
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (n : ℕ) : ℝ :=
  markedRenewalArrivalEpoch (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- Cumulative source work of the target work-mark labels `0, ..., n`. -/
def stationaryAdmittedTargetPalmCumulativeWork
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (n : ℕ) : ℝ :=
  markedRenewalCumulativeWork (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- Cumulative target source work less `mu` times elapsed target interarrival
time.  This is a source-input net process, not a workload recursion. -/
def stationaryAdmittedTargetPalmCumulativeNetWork
    (target : Category) (mu : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (n : ℕ) : ℝ :=
  markedRenewalCumulativeNetWork mu
    (stationaryAdmittedTargetPalmMarkedRenewalSample target z) n

/-- The work sum in the marked-renewal adapter is literally the target
work-mark sum over labels `0, ..., n`. -/
theorem stationaryAdmittedTargetPalmCumulativeWork_eq_sum
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : ℕ) :
    stationaryAdmittedTargetPalmCumulativeWork target z n =
      ∑ j ∈ Finset.range (n + 1), z.1.2 (Int.ofNat j) := rfl

/-- The marked-renewal denominator is exactly the target Palm arrival epoch
with label `n + 1`.  Thus the source-only SLLNs below have no implicit
endpoint or index shift. -/
theorem stationaryAdmittedTargetPalmArrivalEpoch_eq_candidatePalmArrival_succ
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : ℕ) :
    stationaryAdmittedTargetPalmArrivalEpoch target z n =
      candidatePalmArrival z.1.1 (Int.ofNat (n + 1)) := by
  simpa [stationaryAdmittedTargetPalmArrivalEpoch,
    stationaryAdmittedTargetPalmMarkedRenewalSample,
    markedRenewalArrivalEpoch, candidatePalmArrival_ofNat] using
    (congrFun (candidateFutureEpoch_succ_eq_arrivalTime n) z.1.1).symm

/-- The direct target gap/work coordinate has exactly the generic marked
renewal source law under the genuine target/passive Palm product. -/
theorem stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    HasLaw (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (twoSidedMarkedRenewalMeasure (M.admittedRate target))
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  simpa [stationaryAdmittedTargetPalmMarkedRenewalSample,
    stationaryAdmittedTargetPassiveTaggedInput,
    targetPassiveTaggedArrivalAtZero, targetTag, passiveBase,
    twoSidedMarkedRenewalMeasure,
    stationaryAdmittedTargetTaggedArrivalAtZero,
    stationaryPoissonWorkTaggedArrivalAtZero] using
    ((measurePreserving_fst : MeasurePreserving Prod.fst
      (targetTag.Ptag.prod passiveBase.Pbase) targetTag.Ptag).hasLaw)

/-- Along the actual tagged target source, the work labels `0, ..., n` per
the explicitly recorded post-label-`n` renewal endpoint converge almost
surely to the direct admitted rate.  This is an input law and does not assert
a queue workload or service conclusion. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmWork_div_arrivalEpoch
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : ℕ =>
          stationaryAdmittedTargetPalmCumulativeWork target z n /
            stationaryAdmittedTargetPalmArrivalEpoch target z n)
        atTop (nhds (M.admittedRate target)) := by
  have hlaw := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hmap : ∀ᵐ x ∂Measure.map
      (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : ℕ =>
          markedRenewalCumulativeWork x n / markedRenewalArrivalEpoch x n)
        atTop (nhds (M.admittedRate target)) := by
    rw [hlaw.map_eq]
    exact ae_tendsto_markedRenewalWork_div_arrivalEpoch (M.admittedRate_pos target)
  simpa [stationaryAdmittedTargetPalmCumulativeWork,
    stationaryAdmittedTargetPalmArrivalEpoch] using
    (Measure.tendsto_ae_map hlaw.aemeasurable hmap)

/-- Along the actual tagged target source, the net marked input per target
arrival converges to the literal source drift `1 - mu / s_target`.  The
quantity is deliberately indexed by target arrivals; it is not a GPS
workload recursion. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmCumulativeNetWork_div_nat_succ
    (M : SLA2026BoroughQueueingInput Category) (target : Category) (mu : ℝ) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : ℕ =>
          stationaryAdmittedTargetPalmCumulativeNetWork target mu z n /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 - mu / M.admittedRate target)) := by
  have hlaw := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hmap : ∀ᵐ x ∂Measure.map
      (stationaryAdmittedTargetPalmMarkedRenewalSample target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : ℕ =>
          markedRenewalCumulativeNetWork mu x n / ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 - mu / M.admittedRate target)) := by
    rw [hlaw.map_eq]
    exact ae_tendsto_markedRenewalCumulativeNetWork_div_nat_succ
      (M.admittedRate_pos target)
  simpa [stationaryAdmittedTargetPalmCumulativeNetWork] using
    (Measure.tendsto_ae_map hlaw.aemeasurable hmap)

/-- If the supplied comparison service rate strictly exceeds the direct
admitted target rate, the target source's exact net-input limit is strictly
negative.  This establishes a source drift sign only, not a reset or
stationarity result. -/
theorem stationaryAdmittedTargetPalmNetWorkLimit_neg_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category) (mu : ℝ)
    (hmu : M.admittedRate target < mu) :
    1 - mu / M.admittedRate target < 0 := by
  rw [sub_neg]
  exact (lt_div_iff₀ (M.admittedRate_pos target)).2 (by simpa using hmu)

/-- The actual tagged target source has a negative marked-net-input limit
whenever its direct admitted rate is below the supplied comparison service
rate.  This bundles the source SLLN with its sign, and still contains no
queue-state conclusion. -/
theorem ae_tendsto_stationaryAdmittedTargetPalmCumulativeNetWork_div_nat_succ_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category) (mu : ℝ)
    (hmu : M.admittedRate target < mu) :
    (∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun n : ℕ =>
          stationaryAdmittedTargetPalmCumulativeNetWork target mu z n /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 - mu / M.admittedRate target))) ∧
      1 - mu / M.admittedRate target < 0 := by
  exact ⟨M.ae_tendsto_stationaryAdmittedTargetPalmCumulativeNetWork_div_nat_succ
      target mu,
    M.stationaryAdmittedTargetPalmNetWorkLimit_neg_of_admittedRate_lt target mu hmu⟩

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
