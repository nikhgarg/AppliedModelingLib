import AppliedModelingLib.Foundations.Probability.Processes.Palm.QueueLengthPASTA
import AppliedModelingLib.Queueing.MM1.AnalyticTail

/-!
# Stationary base laws and Palm/PASTA queue-state interfaces

This module does not construct a Palm measure.  It gives the explicit
mathematical interface a future construction must satisfy: a shift-invariant
untagged stationary probability law, a separately tagged-at-zero probability
law, and a PASTA distributional identity for the pre-arrival queue state.
-/

namespace AppliedModelingLib
namespace Probability
namespace Palm

open MeasureTheory ProbabilityTheory

namespace PalmPASTAQueueLengthCertificate

/--
Combine an explicit stationary-base/PASTA queue-state certificate with a
forward potential-service process to obtain the count certificate consumed by
the M/M/1 response-tail proof.  The base stationary geometric law, post-tag
independence, response event identity, and no-atom property remain explicit
inputs; unlike the lower-level constructor, the tagged queue tail is derived
from the PASTA identity rather than supplied directly.
-/
def toTaggedPASTAMM1CountCertificate
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw
      Ωtag tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (response : Ωtag → ℝ)
    (hresponse_measurable : Measurable response)
    (hstationary_queue_tail : ∀ k : ℕ,
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =
        {ω | service.count z.toNNReal ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  Queueing.TaggedPASTAMM1CountCertificate.ofForwardServiceProcess
    tagged arrivalRate harrivalRate service hstable H.preArrivalQueueLength response
    H.preArrivalQueueLength_measurable hresponse_measurable
    hpreArrivalQueueLength_indep_service
    (fun k => (H.real_preArrivalQueueLength_tail_eq_stationary k).trans
      (hstationary_queue_tail k))
    hstrict_response_event hresponse_atom_zero

/--
Forward-service version of the PASTA-to-count-certificate bridge with an
almost-everywhere response event identity.  The stationary base law, Palm
tagged law, PASTA identity, future-service independence, and no-atom condition
remain explicit inputs.
-/
def toTaggedPASTAMM1CountCertificateAE
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw
      Ωtag tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (response : Ωtag → ℝ)
    (hresponse_measurable : Measurable response)
    (hstationary_queue_tail : ∀ k : ℕ,
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
        {ω | service.count z.toNNReal ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  Queueing.TaggedPASTAMM1CountCertificate.ofForwardServiceProcessAE
    tagged arrivalRate harrivalRate service hstable H.preArrivalQueueLength response
    H.preArrivalQueueLength_measurable hresponse_measurable
    hpreArrivalQueueLength_indep_service
    (fun k => (H.real_preArrivalQueueLength_tail_eq_stationary k).trans
      (hstationary_queue_tail k))
    hstrict_response_event hresponse_atom_zero

/--
Combine an explicit stationary-base/PASTA queue-state certificate with just
the fixed-horizon post-tag completion-count facts consumed by the M/M/1 tail
mixture.  Unlike `toTaggedPASTAMM1CountCertificate`, this makes no assertion
about chronological sample paths or independent increments of the supplied
counts.
-/
noncomputable def toTaggedPASTAMM1CountCertificateOfPostTagPoissonCompletionCountMarginals
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : Queueing.PostTagPoissonCompletionCountMarginals Ωtag tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (response : Ωtag → ℝ)
    (hresponse_measurable : Measurable response)
    (hstationary_queue_tail : ∀ k : ℕ,
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.completionCount z) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
      {ω | service.completionCount z ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  Queueing.TaggedPASTAMM1CountCertificate.ofPostTagPoissonCompletionCountMarginals
    tagged arrivalRate harrivalRate service hstable H.preArrivalQueueLength response
    H.preArrivalQueueLength_measurable hresponse_measurable
    hpreArrivalQueueLength_indep_service
    (fun k => (H.real_preArrivalQueueLength_tail_eq_stationary k).trans
      (hstationary_queue_tail k))
    hstrict_response_event hresponse_atom_zero

end PalmPASTAQueueLengthCertificate

end Palm
end Probability
end AppliedModelingLib
