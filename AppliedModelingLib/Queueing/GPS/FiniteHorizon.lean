import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTraceProgress
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BlockDominance
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionEventRefinement
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTemporalSeparation
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSDeadline
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSEmptyFenceFixedScriptMeasurability
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSKeyAbsence
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSKeyAccounting
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSSemanticProjection
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSZeroDelayFence
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Multiclass
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.PreBatchReset
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentComposition
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SuffixCreditReset

/-!
# Finite-horizon generalized processor sharing

Curated queueing-domain entrypoint for executable finite GPS traces, segment
and FCFS projections, completion accounting, reset and fence arguments, and
the associated measurability results.

This module is intentionally separate from `AppliedModelingLib.Queueing.GPS`: importing
the basic deterministic and almost-everywhere comparison layer should not load
the much larger finite-horizon implementation. Its declaration-owning modules
live under this queueing-domain subtree while retaining the established
mathematical declaration names.
-/
