import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core

/-!
# Palm/PASTA queue-length interface

This module records the queue-length distributional conclusion supplied by a
Palm/PASTA construction.  It does not specialize that conclusion to an M/M/1
model or construct a tagged response-time certificate.
-/

namespace AppliedModelingLib
namespace Probability
namespace Palm

open MeasureTheory ProbabilityTheory

/--
The queue-state consequence of a stationary Palm/PASTA construction.

`base` is the shift-invariant untagged system law.  `tagged` is a different
probability law in which an arrival has been pinned at time zero.  The field
`pasta_queue_length` says precisely that the tagged pre-arrival queue-length
distribution agrees with the base stationary queue-length distribution.  It
is deliberately a conclusion-to-be-proved, not an automatic property of a
Poisson rate declaration.
-/
structure PalmPASTAQueueLengthCertificate
    (Ωbase Ωtag : Type*) [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    (base : ShiftInvariantProbabilityLaw Ωbase)
    (tagged : Queueing.TaggedArrivalAtZero Ωtag) where
  stationaryQueueLength : Ωbase → ℕ
  preArrivalQueueLength : Ωtag → ℕ
  stationaryQueueLength_measurable : Measurable stationaryQueueLength
  preArrivalQueueLength_measurable : Measurable preArrivalQueueLength
  pasta_queue_length : HasLaw preArrivalQueueLength
    (base.Pbase.map stationaryQueueLength) tagged.Ptag

namespace PalmPASTAQueueLengthCertificate

/-- PASTA transfers every queue-length upper tail from the base law to the tag. -/
theorem real_preArrivalQueueLength_tail_eq_stationary
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (k : ℕ) :
    tagged.Ptag.real {ω | k ≤ H.preArrivalQueueLength ω} =
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} := by
  change (tagged.Ptag {ω | k ≤ H.preArrivalQueueLength ω}).toReal =
    (base.Pbase {ω | k ≤ H.stationaryQueueLength ω}).toReal
  rw [show tagged.Ptag {ω | k ≤ H.preArrivalQueueLength ω} =
      (tagged.Ptag.map H.preArrivalQueueLength) (Set.Ici k) by
        simpa only [Set.preimage_setOf_eq] using
          (Measure.map_apply H.preArrivalQueueLength_measurable measurableSet_Ici).symm]
  rw [H.pasta_queue_length.map_eq]
  congr 1
  simpa only [Set.preimage_setOf_eq] using
    (Measure.map_apply H.stationaryQueueLength_measurable measurableSet_Ici)

end PalmPASTAQueueLengthCertificate

end Palm
end Probability
end AppliedModelingLib
