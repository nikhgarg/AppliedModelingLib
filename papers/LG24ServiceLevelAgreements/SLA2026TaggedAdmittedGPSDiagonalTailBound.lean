import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalDeadlineBridge
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalIndex
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSFiniteComparatorIntegration
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGlobalPastTargetRemoteStart
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCanonicalTail
import Mathlib.Tactic

/-!
# Eventual comparator bound for literal diagonal GPS replays

This module composes the source-side global-reset event with the literal
diagonal deadline bridge.  It proves an almost-sure eventual bound for the
actual finite diagonal responses, then transfers it through the explicit
bad-carrier totalization.  The only infinite-past comparison is the already
constructed target-only FCFS comparator; no GPS response is selected from a
reset witness.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Almost surely, every sufficiently remote literal diagonal GPS replay
completes the tagged source job no later than the coalesced direct
target-only comparator response.  The finite comparator deadline is first
used physically inside the same diagonal source-labelled trace; its later
comparison with the coalesced direct comparator is a separate scalar
inequality. -/
theorem ae_eventually_taggedAdmittedGPSDiagonalFiniteResponseTotal_le_comparatorResponse
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hstable : M.admittedRate target < G.capacity * G.weight target) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∀ᶠ N : Nat in atTop,
        taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z ≤
          stationaryAdmittedTargetPalmComparatorResponse target
            (G.capacity * G.weight target) z := by
  filter_upwards [
    M.ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_globalMax_and_targetRemoteStart
      G target,
    M.ae_stationaryAdmittedTargetPassivePalmWorkAtZero_positive target,
    M.ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_gpsParameters
      G target hstable]
    with z hreset htagged_work_pos hcoalesces
  rcases hreset with ⟨htarget_good, hsource_work_nonneg, start, resetTime,
    remoteStart, hstart_reset, hstart_zero, hboundary, hreset_zero, hcoverage,
    hglobal, hclosed_workload⟩
  filter_upwards [eventually_taggedAdmittedGPSDiagonal_contains resetTime
    (stationaryAdmittedTargetPalmFiniteComparatorResponse
      target (G.capacity * G.weight target) z remoteStart)] with N hdiagonal
  have hfinite : taggedAdmittedGPSDiagonalFiniteResponse
      target z htarget_good G.capacity G.weight N ≤
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart :=
    taggedAdmittedGPSDiagonalFiniteResponse_le_finiteComparatorResponse_of_pastGlobalMax
      M G target z htarget_good hsource_work_nonneg resetTime remoteStart hreset_zero
      hglobal hcoverage htagged_work_pos N hdiagonal.1 hdiagonal.2
  have hfinite_to_direct : stationaryAdmittedTargetPalmFiniteComparatorResponse
      target (G.capacity * G.weight target) z remoteStart ≤
      stationaryAdmittedTargetPalmComparatorResponse target
        (G.capacity * G.weight target) z :=
    stationaryAdmittedTargetPalmFiniteComparatorResponse_le_comparatorResponse_of_coalesces
      target (G.capacity * G.weight target) z remoteStart
      ((M.admittedRate_pos target).trans hstable) hcoalesces
  simpa only [taggedAdmittedGPSDiagonalFiniteResponseTotal, dif_pos htarget_good] using
    hfinite.trans hfinite_to_direct

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
