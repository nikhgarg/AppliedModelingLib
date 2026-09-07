import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGlobalPastReset
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedTargetSourceOrder
import Mathlib.Tactic

/-!
# Physical GPS reset paired with a target comparator start

The aggregate GPS cutoff is allowed to occur at any actual source boundary,
including a passive-source boundary.  This module pairs that physical reset
with the finite target-only comparator history selected by literal target
arrival order.  It is source/accounting provenance only: it does not yet
prove the dynamic GPS-versus-comparator workload inequality or a response
tail.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal global GPS reset can almost surely be paired with a finite
target-only remote start whose labels are exactly the target source jobs in
`[resetTime, 0)`.  The reset itself remains the actual source boundary chosen
by the aggregate construction; this theorem does not replace it by a target
arrival or add a virtual batch. -/
theorem ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_targetRemoteStart
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
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
                ∀ i,
                  (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
                    G.capacity G.weight (fun _ => 0) hstart_reset).workload i = 0 := by
  filter_upwards [M.ae_exists_taggedAdmittedPastGlobalClosedPrefix G target,
    M.ae_tendsto_neg_stationaryAdmittedTargetPalmPastStart_atTop target]
    with z hclosed hlimit
  rcases hclosed with ⟨htarget_good, hsource_work_nonneg, start, resetTime,
    hstart_reset, hstart_zero, hboundary, hreset_zero, hclosed_workload⟩
  rcases exists_taggedAdmittedTargetPastWindowCoversRemoteStart_of_goodCarrier_and_tendsto
      resetTime target z htarget_good hlimit with ⟨remoteStart, hcoverage⟩
  exact ⟨htarget_good, hsource_work_nonneg, start, resetTime, remoteStart,
    hstart_reset, hstart_zero, hboundary, hreset_zero, hcoverage,
    hclosed_workload⟩

/-- The target-comparator remote start can be paired with the same physical
global-reset certificate, rather than with a separately selected reset.  The
retained global maximum is needed when a later diagonal replay begins before
that reset: it supplies the numeric workload comparison at the literal Palm
batch, while the target coverage identifies the finite comparator ledger. -/
theorem ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_globalMax_and_targetRemoteStart
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
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
                (∀ u : Real, u ≤ 0 →
                  stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
                      G.capacity * (-u) ≤
                    stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
                      G.capacity * (-resetTime)) ∧
                ∀ i,
                  (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
                    G.capacity G.weight (fun _ => 0) hstart_reset).workload i = 0 := by
  filter_upwards [M.ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_globalMax G target,
    M.ae_tendsto_neg_stationaryAdmittedTargetPalmPastStart_atTop target]
    with z hclosed hlimit
  rcases hclosed with ⟨htarget_good, hsource_work_nonneg, start, resetTime,
    hstart_reset, hstart_zero, hboundary, hreset_zero, hglobal, hclosed_workload⟩
  rcases exists_taggedAdmittedTargetPastWindowCoversRemoteStart_of_goodCarrier_and_tendsto
      resetTime target z htarget_good hlimit with ⟨remoteStart, hcoverage⟩
  exact ⟨htarget_good, hsource_work_nonneg, start, resetTime, remoteStart,
    hstart_reset, hstart_zero, hboundary, hreset_zero, hcoverage, hglobal,
    hclosed_workload⟩

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
