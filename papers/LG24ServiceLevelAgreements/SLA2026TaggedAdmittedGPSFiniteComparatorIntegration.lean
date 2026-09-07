import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGlobalPastTargetRemoteStart
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCompatibleCompletionBridge
import AppliedModelingLib.Queueing.Lindley.RemotePastMonotonicity
import Mathlib.Tactic

/-!
# Finite GPS witness at the literal target-comparator deadline

This module composes three already source-facing finite facts:

* the aggregate remote-past construction produces an actual physical reset;
* the reset can be paired with the finite literal target-predecessor window;
* an explicit FCFS front-work inequality on the concrete post-tag GPS trace
  yields a literal finite completion witness.

The unresolved GPS comparison is deliberately an explicit hypothesis below.
It is a pathwise inequality over the concrete finite source/fence trace, not
a stationarity, response-time, or tail-law certificate.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A concrete finite post-tag GPS trace completes the literal target job by
the finite target-only comparator deadline whenever its actual initial active
prefix supplies enough target guaranteed-rate service for the literal FCFS
front work.  No stationary GPS response functional occurs in this statement.

The `before`, `admissionStep`, and `after` lists are an exact split of the
source/fence executor at the literal `(target, 0)` endpoint.  The only
comparison premise is the displayed front-work inequality over that concrete
suffix. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_finiteComparatorResponse_of_frontWork
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (resetTime : ℝ) (remoteStart : Nat)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_zero : resetTime ≤ 0)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      resetTime
      (stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart)
      target z htarget_good G.capacity G.weight =
        before ++ admissionStep :: after)
    (htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target)
    (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
        some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration : frontWork ≤ G.capacity * G.weight target *
      finiteGPSFCFSSegmentStepsTotalDuration
        (finiteGPSFCFSSegmentStepsInitialActivePrefix target after)) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        resetTime
        (stationaryAdmittedTargetPalmFiniteComparatorResponse
          target (G.capacity * G.weight target) z remoteStart)
        target z htarget_good G.capacity G.weight,
      witness.completion.completionTime ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart ∧
        witness.response ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart := by
  have hrate_pos : 0 < G.capacity * G.weight target :=
    mul_pos (G.capacity_pos target) (G.weight_pos target)
  have hpre_nonneg : 0 ≤ stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target (G.capacity * G.weight target) z remoteStart :=
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
      target (G.capacity * G.weight target) z remoteStart
  have hhorizon_pos : 0 < stationaryAdmittedTargetPalmFiniteComparatorResponse
      target (G.capacity * G.weight target) z remoteStart := by
    rw [stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div]
    exact div_pos (add_pos_of_nonneg_of_pos hpre_nonneg htagged_work_pos) hrate_pos
  have hreset_le_horizon : resetTime ≤
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart :=
    hreset_zero.trans hhorizon_pos.le
  have htagged_source_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0) := by
    simpa [stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using htagged_work_pos
  exact taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_by_horizon_of_initialActivePrefixFrontWork_le_floorDuration
    resetTime
    (stationaryAdmittedTargetPalmFiniteComparatorResponse
      target (G.capacity * G.weight target) z remoteStart)
    target z htarget_good G.capacity G.weight hreset_le_horizon
    (G.capacity_pos target) G.weight_pos G.total_weight_le_one hsource_work_nonneg
    before admissionStep after hsplit htag_admitted htagged_source_work_pos
    frontWork hfront hfront_pos hfront_le_floor_duration

/-- Extending the literal target remote history cannot decrease its finite
pre-tag scalar workload.  This is the deterministic carried-state monotonicity
of the exact same source batch/service sequence, not a stationarity claim. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_mono
    (target : Category) (serviceRate : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    {K N : Nat} (hKN : K ≤ N) :
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        target serviceRate z K ≤
      stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        target serviceRate z N := by
  simpa [stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload] using
    (lateBatchPreWorkload_reverseRemotePast_mono
      (stationaryAdmittedTargetPalmRemotePastBatch target z)
      (stationaryAdmittedTargetPalmRemotePastService target serviceRate z)
      K N hKN)

/-- At positive constant target service rate, extending the exact finite
target predecessor replay cannot decrease its tagged comparator response. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorResponse_mono
    (target : Category) (serviceRate : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    {K N : Nat} (hKN : K ≤ N) (hserviceRate : 0 < serviceRate) :
    stationaryAdmittedTargetPalmFiniteComparatorResponse
        target serviceRate z K ≤
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target serviceRate z N := by
  unfold stationaryAdmittedTargetPalmFiniteComparatorResponse
  exact div_le_div_of_nonneg_right
    (add_le_add
      (stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_mono
        target serviceRate z hKN)
      (le_refl _))
    hserviceRate.le

/-- A finite target comparator at a physical reset window is bounded by the
coalesced source-defined comparator response.  The proof deliberately moves
to `max remoteStart K`; it never identifies the reset-window replay with the
coalesced replay unless it is actually beyond the cutoff. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorResponse_le_comparatorResponse_of_coalesces
    (target : Category) (serviceRate : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (hserviceRate : 0 < serviceRate)
    (hcoalesces : StationaryAdmittedTargetPalmComparatorPreTagCoalesces
      target serviceRate z) :
    stationaryAdmittedTargetPalmFiniteComparatorResponse
        target serviceRate z remoteStart ≤
      stationaryAdmittedTargetPalmComparatorResponse target serviceRate z := by
  rcases stationaryAdmittedTargetPalmComparatorResponse_eq_finite_of_coalesces
      target serviceRate z hcoalesces with ⟨K, hK⟩
  calc
    stationaryAdmittedTargetPalmFiniteComparatorResponse
        target serviceRate z remoteStart ≤
        stationaryAdmittedTargetPalmFiniteComparatorResponse
          target serviceRate z (max remoteStart K) :=
      stationaryAdmittedTargetPalmFiniteComparatorResponse_mono
        target serviceRate z (le_max_left _ _) hserviceRate
    _ = stationaryAdmittedTargetPalmComparatorResponse target serviceRate z :=
      (hK (max remoteStart K) (le_max_right _ _)).symm

/-- The global physical-reset event yields an almost-sure finite tagged GPS
completion witness once the remaining, fully explicit source-side front-work
comparison is available for that reset window.

The premise does **not** assert a GPS response random variable, a stationary
GPS state, or a tail law.  For each actual reset it must exhibit the literal
post-tag source/fence split and prove that its initial active prefix supplies
enough guaranteed-rate service for its concrete FCFS front work.  The output
retains both deadlines: the witness is first bounded by the finite comparator
at the physical reset window, then by the source-defined coalesced comparator
through proved remote-start monotonicity. -/
theorem ae_exists_taggedAdmittedFiniteGPSHorizonFenceResponseWitness_le_comparatorResponse_of_closedFrontWork
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hclosed_frontWork :
      ∀ (z : StationaryAdmittedTargetPassiveTaggedInput target)
        (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
        (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
        (start resetTime : ℝ) (remoteStart : Nat)
        (hstart_reset : start ≤ resetTime) (hstart_zero : start ≤ 0)
        (hboundary : resetTime ∈
          taggedAdmittedPastBoundaryCandidates start 0 target z)
        (hreset_zero : resetTime ≤ 0)
        (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
          resetTime target z remoteStart)
        (hclosed : ∀ i,
          (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
            G.capacity G.weight (fun _ => 0) hstart_reset).workload i = 0)
        (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z),
        ∃ (before : List (FiniteGPSFCFSSegmentJobStep Category
            (TaggedAdmittedSourceJobId Category)))
          (admissionStep : FiniteGPSFCFSSegmentJobStep Category
            (TaggedAdmittedSourceJobId Category))
          (after : List (FiniteGPSFCFSSegmentJobStep Category
            (TaggedAdmittedSourceJobId Category)))
          (frontWork : ℝ),
          taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps resetTime
            (stationaryAdmittedTargetPalmFiniteComparatorResponse
              target (G.capacity * G.weight target) z remoteStart)
            target z htarget_good G.capacity G.weight =
              before ++ admissionStep :: after ∧
          taggedAdmittedFCFSJob target z (target, 0) ∈
            admissionStep.endpointJobs.jobs target ∧
          finiteGPSFCFSFrontWork
            (fun identifier : TaggedAdmittedSourceJobId Category =>
              decide (identifier = (target, 0)))
            ((taggedAdmittedFiniteGPSPostAdmissionLedger
              before admissionStep).residualJobs target) = some frontWork ∧
          0 < frontWork ∧
          frontWork ≤ G.capacity * G.weight target *
            finiteGPSFCFSSegmentStepsTotalDuration
              (finiteGPSFCFSSegmentStepsInitialActivePrefix target after)) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ htarget_good : palmTaggedArrivalGoodCarrier z.1.1,
        ∃ hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z,
          ∃ start resetTime remoteStart,
            ∃ hstart_reset : start ≤ resetTime,
              start ≤ 0 ∧
                resetTime ∈ taggedAdmittedPastBoundaryCandidates start 0 target z ∧
                resetTime ≤ 0 ∧
                TaggedAdmittedTargetPastWindowCoversRemoteStart
                  resetTime target z remoteStart ∧
                (∀ i,
                  (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
                    G.capacity G.weight (fun _ => 0) hstart_reset).workload i = 0) ∧
                ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
                    resetTime
                    (stationaryAdmittedTargetPalmFiniteComparatorResponse
                      target (G.capacity * G.weight target) z remoteStart)
                    target z htarget_good G.capacity G.weight,
                  witness.completion.completionTime ≤
                    stationaryAdmittedTargetPalmFiniteComparatorResponse
                      target (G.capacity * G.weight target) z remoteStart ∧
                  witness.response ≤ stationaryAdmittedTargetPalmComparatorResponse
                    target (G.capacity * G.weight target) z := by
  filter_upwards [
    M.ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_targetRemoteStart G target,
    M.ae_stationaryAdmittedTargetPassivePalmWorkAtZero_positive target,
    M.ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_gpsParameters
      G target hstable]
    with z hreset htagged_work_pos hcoalesces
  rcases hreset with ⟨htarget_good, hsource_work_nonneg, start, resetTime,
    remoteStart, hstart_reset, hstart_zero, hboundary, hreset_zero, hcoverage,
    hclosed⟩
  rcases hclosed_frontWork z htarget_good hsource_work_nonneg start resetTime
      remoteStart hstart_reset hstart_zero hboundary hreset_zero hcoverage hclosed
      htagged_work_pos with
      ⟨before, admissionStep, after, frontWork, hsplit, htag_admitted, hfront,
        hfront_pos, hfront_le_floor_duration⟩
  rcases taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_finiteComparatorResponse_of_frontWork
      M G target z resetTime remoteStart htarget_good hsource_work_nonneg hreset_zero
      htagged_work_pos before admissionStep after hsplit htag_admitted frontWork hfront
      hfront_pos hfront_le_floor_duration with
      ⟨witness, hcompletion, hfinite_response⟩
  refine ⟨htarget_good, hsource_work_nonneg, start, resetTime, remoteStart,
    hstart_reset, hstart_zero, hboundary, hreset_zero, hcoverage, hclosed,
    witness, hcompletion, ?_⟩
  exact hfinite_response.trans
    (stationaryAdmittedTargetPalmFiniteComparatorResponse_le_comparatorResponse_of_coalesces
      target (G.capacity * G.weight target) z remoteStart
      ((M.admittedRate_pos target).trans hstable)
      hcoalesces)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
