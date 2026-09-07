import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGlobalPastReset
import Mathlib.Tactic

/-!
# Source-semantic reset bridge for diagonal tagged GPS replays

This module records the part of the remote-past restart argument that follows
directly from the global source-net maximizer.  In particular, a fixed global
maximizing boundary closes *every* diagonal prefix whose left endpoint lies
before that boundary.  This is deliberately stronger than choosing one reset
for one finite window.

The remaining lemmas in this module will lift this aggregate closed-prefix
fact to the literal source-labelled FCFS trace.  That lift must preserve the
endpoint-before-service convention at a boundary batch; it cannot be inferred
from equality of aggregate GPS workload alone.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A retained global source-net maximizer closes every sufficiently remote
diagonal prefix at the same physical boundary.  This is the pathwise
closed-prefix fact needed before any FCFS trace restart can be considered. -/
theorem taggedAdmittedFiniteGPSDiagonalPrefix_all_work_eq_zero_of_pastGlobalMax
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (resetTime : ℝ)
    (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (N : ℕ) (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime) :
    ∀ i,
      (taggedAdmittedFiniteGPSRun (taggedAdmittedGPSDiagonalStart N) resetTime
        target z htarget_good G.capacity G.weight (fun _ => 0)
        hdiagonal_before_reset).workload i = 0 := by
  exact taggedAdmittedFiniteGPSRun_all_work_eq_zero_of_pastGlobalMax
    (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
    G.capacity G.weight hdiagonal_before_reset hreset_zero
    (G.capacity_pos target) G.weight_pos G.total_weight_le_one
    hsource_work_nonneg hglobal

/-- At every diagonal long enough to begin before the retained global
boundary, the aggregate executable GPS run has the exact closed-prefix
restart form at that boundary.  The displayed equality deliberately records
only the aggregate runner state and accumulated service; it is not yet an
equality of source-labelled FCFS completion histories. -/
theorem taggedAdmittedFiniteGPSDiagonalRun_eq_closed_prefix_then_closed_source_suffix_of_pastGlobalMax
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (resetTime : ℝ)
    (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (N : ℕ) (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime) :
    taggedAdmittedFiniteGPSRun
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight (fun _ => 0)
        (taggedAdmittedGPSDiagonalStart_le_horizon N) =
      { workload :=
          (taggedAdmittedFiniteGPSRun resetTime (taggedAdmittedGPSDiagonalHorizon N)
            target z htarget_good G.capacity G.weight (fun _ => 0)
            (hreset_zero.trans (taggedAdmittedGPSDiagonalHorizon_pos N).le)).workload
        currentTime :=
          (taggedAdmittedFiniteGPSRun resetTime (taggedAdmittedGPSDiagonalHorizon N)
            target z htarget_good G.capacity G.weight (fun _ => 0)
            (hreset_zero.trans (taggedAdmittedGPSDiagonalHorizon_pos N).le)).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSRun
            (taggedAdmittedGPSDiagonalStart N) resetTime
            target z htarget_good G.capacity G.weight (fun _ => 0)
            hdiagonal_before_reset).service i +
          (taggedAdmittedFiniteGPSRun resetTime (taggedAdmittedGPSDiagonalHorizon N)
            target z htarget_good G.capacity G.weight (fun _ => 0)
            (hreset_zero.trans (taggedAdmittedGPSDiagonalHorizon_pos N).le)).service i } := by
  apply taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_closed_prefix_workload_zero
    (taggedAdmittedGPSDiagonalStart N) resetTime (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good G.capacity G.weight (fun _ => 0)
    hdiagonal_before_reset
    (hreset_zero.trans (taggedAdmittedGPSDiagonalHorizon_pos N).le)
    (G.capacity_pos target) G.weight_pos G.total_weight_le_one
    (by intro _; norm_num) hsource_work_nonneg
  exact taggedAdmittedFiniteGPSDiagonalPrefix_all_work_eq_zero_of_pastGlobalMax
    M G target z htarget_good hsource_work_nonneg resetTime hreset_zero hglobal
    N hdiagonal_before_reset

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
