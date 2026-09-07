import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSTaggedCompletion
import Mathlib.Tactic

/-!
# FCFS front-work order at an endpoint batch

This small deterministic module records the service-before-batch fact needed
when a distinguished job is admitted at a real source endpoint.  It is
deliberately independent of a particular arrival model: callers must prove
that the preceding queue does not already contain the distinguished job and
that the endpoint batch has the desired literal order.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- If an ordered queue has no keyed job and a keyed job is appended as the
sole final endpoint job, its FCFS front work is exactly the residual work
already ahead of it plus that job's own work.  This is the semantic
service-before-batch interface: `left` may already be the result of an
actual segment's service, but no endpoint work is moved ahead of the key. -/
theorem finiteGPSFCFSFrontWork_append_singleton_eq_jobWork_add
    (key : JobId -> Bool) (left : List (FiniteGPSFCFSJob JobId))
    (job : FiniteGPSFCFSJob JobId)
    (hleft_no_key : ∀ earlier ∈ left, key earlier.identifier ≠ true)
    (hjob_key : key job.identifier = true) :
    finiteGPSFCFSFrontWork key (left ++ [job]) =
      some (finiteGPSFCFSJobWork left + job.residualWork) := by
  induction left with
  | nil =>
      simp [finiteGPSFCFSFrontWork, finiteGPSFCFSJobWork, hjob_key]
  | cons earlier left ih =>
      have hearlier_no_key : key earlier.identifier ≠ true :=
        hleft_no_key earlier (by simp)
      have hleft_tail_no_key : ∀ later ∈ left, key later.identifier ≠ true := by
        intro later hlater
        exact hleft_no_key later (by simp [hlater])
      have htail := ih hleft_tail_no_key
      rw [List.cons_append, finiteGPSFCFSFrontWork, if_neg hearlier_no_key, htail]
      simp only [Option.map_some, finiteGPSFCFSJobWork_cons]
      congr 1
      ring

/-- Applying a segment consumes service before appending its endpoint jobs.
Consequently, if the endpoint batch is the single keyed job, the keyed front
work is the post-service FCFS work already present plus the keyed job's own
work. -/
theorem finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq
    (key : JobId -> Bool) (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (i : Class) (job : FiniteGPSFCFSJob JobId)
    (hendpoint : endpointJobs.jobs i = [job])
    (hserved_no_key : ∀ earlier ∈
      finiteGPSFCFSConsume (segment.serviceIncrement i) (ledger.residualJobs i),
      key earlier.identifier ≠ true)
    (hjob_key : key job.identifier = true) :
    finiteGPSFCFSFrontWork key
        ((finiteGPSFCFSApplySegment ledger segment endpointJobs).residualJobs i) =
      some
        (finiteGPSFCFSJobWork
          (finiteGPSFCFSConsume (segment.serviceIncrement i) (ledger.residualJobs i)) +
          job.residualWork) := by
  change finiteGPSFCFSFrontWork key
      (finiteGPSFCFSConsume (segment.serviceIncrement i) (ledger.residualJobs i) ++
        endpointJobs.jobs i) = _
  rw [hendpoint]
  exact finiteGPSFCFSFrontWork_append_singleton_eq_jobWork_add
    key _ job hserved_no_key hjob_key

end

end AppliedModelingLib.Probability.Queueing
