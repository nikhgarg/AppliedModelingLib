import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCanonicalTail
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSFiniteResponseBounds
import Mathlib.Tactic

/-!
# Nonnegative canonical finite GPS replay responses

This module lifts the literal finite-response lower bound through the
canonical diagonal windows and their explicit bad-carrier zero totalization.
It supplies the eventual nonnegativity fact used by the real-valued limsup
tail argument without introducing a separate response regularity premise.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Every literal diagonal finite response is nonnegative when its source
work paths are nonnegative. -/
theorem taggedAdmittedGPSDiagonalFiniteResponse_nonneg
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) (N : Nat)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    0 ≤ taggedAdmittedGPSDiagonalFiniteResponse
      target z htarget_good G.capacity G.weight N := by
  simpa [taggedAdmittedGPSDiagonalFiniteResponse] using
    (taggedAdmittedFiniteGPSHorizonFenceTotalResponse_nonneg
      (taggedAdmittedGPSDiagonalStart N)
      (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight
      (taggedAdmittedGPSDiagonalStart_le_zero N)
      (taggedAdmittedGPSDiagonalHorizon_pos N)
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg)

/-- The explicit zero totalization makes every diagonal finite response
nonnegative under the source-work condition, whether or not the source
good-carrier test holds. -/
theorem taggedAdmittedGPSDiagonalFiniteResponseTotal_nonneg_of_sourceWorkNonnegative
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (N : Nat)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    0 ≤ taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z := by
  classical
  unfold taggedAdmittedGPSDiagonalFiniteResponseTotal
  split
  · next htarget_good =>
      exact taggedAdmittedGPSDiagonalFiniteResponse_nonneg
        M G target z htarget_good N hsource_work_nonneg
  · norm_num

/-- Almost every Palm-tagged input has nonnegative canonical finite response
at every diagonal index.  The same source-good event supplies the actual
source work nonnegativity; no separately named response condition is used. -/
theorem ae_forall_taggedAdmittedGPSDiagonalFiniteResponseTotal_nonneg
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∀ N : Nat,
        0 ≤ taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z := by
  filter_upwards [M.ae_taggedAdmittedFiniteExecutionInputGood target] with
      z hinput
  intro N
  exact taggedAdmittedGPSDiagonalFiniteResponseTotal_nonneg_of_sourceWorkNonnegative
    M G target N z hinput.2

/-- The preceding pointwise-in-index fact supplies eventual nonnegativity for
the canonical limsup tail construction. -/
theorem ae_eventually_taggedAdmittedGPSDiagonalFiniteResponseTotal_nonneg
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∀ᶠ N : Nat in atTop,
        0 ≤ taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z := by
  filter_upwards [
    ae_forall_taggedAdmittedGPSDiagonalFiniteResponseTotal_nonneg M G target]
    with z hnonneg
  exact Filter.Eventually.of_forall hnonneg

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
