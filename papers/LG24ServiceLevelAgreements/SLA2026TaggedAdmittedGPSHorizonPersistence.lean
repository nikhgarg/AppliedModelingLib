import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSFCFSRestart
import Mathlib.Tactic

/-!
# Horizon persistence for literal tagged GPS/FCFS replays

This module is the trace-level horizon-extension layer used after a physical
reset has been connected to a diagonal replay.  A finite horizon contains an
explicit computational zero-work fence, so raw full-horizon step lists at two
different horizons are not automatically prefixes of one another.  The
theorems below therefore require the exact source-labelled common-prefix
factorization that a caller has established.  They make no claim that such a
factorization follows merely from aggregate workload equality.

Once the common prefix already contains the real Palm completion, both
horizon selectors and their response values are forced to agree.  This is
the persistence fact needed to turn a reset-start replay into an eventually
constant diagonal response.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- If two literal reset-start horizon traces have the same exact
source-labelled prefix and that prefix already selects the Palm tag, then
both full horizon selectors choose the same completion.  The tails are kept
as arbitrary concrete step lists because the shorter trace may end in a
computational fence while the longer trace continues through later external
source batches. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_eq_some_of_commonSourcePrefix
    (start smallHorizon largeHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (sourcePrefix smallTail largeTail : List
      (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hsmall_steps : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start smallHorizon target z htarget_good capacity weight = sourcePrefix ++ smallTail)
    (hlarge_steps : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start largeHorizon target z htarget_good capacity weight = sourcePrefix ++ largeTail)
    (hprefix_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target sourcePrefix) =
        some selected) :
    taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
        start smallHorizon target z htarget_good capacity weight = some selected /\
      taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
        start largeHorizon target z htarget_good capacity weight = some selected := by
  constructor
  · unfold taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
    unfold taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
    rw [hsmall_steps]
    exact taggedAdmittedFiniteGPSFirstTagCompletion?_persists_of_stepTrace_append
      target sourcePrefix smallTail selected hprefix_selected
  · unfold taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
    unfold taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
    rw [hlarge_steps]
    exact taggedAdmittedFiniteGPSFirstTagCompletion?_persists_of_stepTrace_append
      target sourcePrefix largeTail selected hprefix_selected

/-- The total literal response is horizon-persistent under the same exact
source-labelled common-prefix condition.  This theorem uses the selector's
actual completion record, rather than an aggregate deadline or a chosen
reset witness. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_commonSourcePrefix
    (start smallHorizon largeHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (sourcePrefix smallTail largeTail : List
      (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hsmall_steps : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start smallHorizon target z htarget_good capacity weight = sourcePrefix ++ smallTail)
    (hlarge_steps : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start largeHorizon target z htarget_good capacity weight = sourcePrefix ++ largeTail)
    (hprefix_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target sourcePrefix) =
        some selected) :
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        start smallHorizon target z htarget_good capacity weight =
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        start largeHorizon target z htarget_good capacity weight := by
  have hselected :=
    taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_eq_some_of_commonSourcePrefix
      start smallHorizon largeHorizon target z htarget_good capacity weight
      sourcePrefix smallTail largeTail selected hsmall_steps hlarge_steps hprefix_selected
  calc
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        start smallHorizon target z htarget_good capacity weight = selected.completionTime :=
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
        start smallHorizon target z htarget_good capacity weight selected hselected.1
    _ = taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        start largeHorizon target z htarget_good capacity weight :=
      (taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
        start largeHorizon target z htarget_good capacity weight selected hselected.2).symm

/-- After each diagonal replay has been connected by the FCFS crossing proof
to its reset-start replay, a common exact source-labelled prefix containing
the tagged completion makes the two diagonal finite responses equal.  The two
crossing equalities remain explicit because this theorem does not infer them
from a workload reset. -/
theorem taggedAdmittedGPSDiagonalFiniteResponse_eq_of_resetReplay_commonSourcePrefix
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (resetTime : Real) (smallIndex largeIndex : Nat)
    (sourcePrefix smallTail largeTail : List
      (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hsmall_steps : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      resetTime (taggedAdmittedGPSDiagonalHorizon smallIndex)
      target z htarget_good G.capacity G.weight = sourcePrefix ++ smallTail)
    (hlarge_steps : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      resetTime (taggedAdmittedGPSDiagonalHorizon largeIndex)
      target z htarget_good G.capacity G.weight = sourcePrefix ++ largeTail)
    (hprefix_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target sourcePrefix) =
        some selected)
    (hsmall_crossing : taggedAdmittedGPSDiagonalTagCompletion?
      target z htarget_good G.capacity G.weight smallIndex =
        taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
          resetTime (taggedAdmittedGPSDiagonalHorizon smallIndex)
          target z htarget_good G.capacity G.weight)
    (hlarge_crossing : taggedAdmittedGPSDiagonalTagCompletion?
      target z htarget_good G.capacity G.weight largeIndex =
        taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
          resetTime (taggedAdmittedGPSDiagonalHorizon largeIndex)
          target z htarget_good G.capacity G.weight) :
    taggedAdmittedGPSDiagonalFiniteResponse
        target z htarget_good G.capacity G.weight smallIndex =
      taggedAdmittedGPSDiagonalFiniteResponse
        target z htarget_good G.capacity G.weight largeIndex := by
  have hselected :=
    taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_eq_some_of_commonSourcePrefix
      resetTime (taggedAdmittedGPSDiagonalHorizon smallIndex)
      (taggedAdmittedGPSDiagonalHorizon largeIndex)
      target z htarget_good G.capacity G.weight sourcePrefix smallTail largeTail selected
      hsmall_steps hlarge_steps hprefix_selected
  have hsmall_diagonal : taggedAdmittedGPSDiagonalTagCompletion?
      target z htarget_good G.capacity G.weight smallIndex = some selected :=
    hsmall_crossing.trans hselected.1
  have hlarge_diagonal : taggedAdmittedGPSDiagonalTagCompletion?
      target z htarget_good G.capacity G.weight largeIndex = some selected :=
    hlarge_crossing.trans hselected.2
  calc
    taggedAdmittedGPSDiagonalFiniteResponse
        target z htarget_good G.capacity G.weight smallIndex = selected.completionTime := by
      unfold taggedAdmittedGPSDiagonalFiniteResponse
      exact taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
        (taggedAdmittedGPSDiagonalStart smallIndex)
        (taggedAdmittedGPSDiagonalHorizon smallIndex)
        target z htarget_good G.capacity G.weight selected (by
          simpa [taggedAdmittedGPSDiagonalTagCompletion?] using hsmall_diagonal)
    _ = taggedAdmittedGPSDiagonalFiniteResponse
        target z htarget_good G.capacity G.weight largeIndex := by
      unfold taggedAdmittedGPSDiagonalFiniteResponse
      exact (taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
        (taggedAdmittedGPSDiagonalStart largeIndex)
        (taggedAdmittedGPSDiagonalHorizon largeIndex)
        target z htarget_good G.capacity G.weight selected (by
          simpa [taggedAdmittedGPSDiagonalTagCompletion?] using hlarge_diagonal)).symm

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
