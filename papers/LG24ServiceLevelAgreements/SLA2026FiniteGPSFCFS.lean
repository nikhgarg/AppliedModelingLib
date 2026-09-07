import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonSegments
import LG24ServiceLevelAgreements.SLA2026FiniteGPSExecution
import Mathlib.Tactic

/-!
# Source-identified finite FCFS jobs for the SLA GPS input

This adapter decomposes the active SLA paper's direct admitted-work source
ledger into individual finite FCFS jobs.  A class-wide ledger is sorted
lexicographically by `(arrivalTime, rawIndex)`; the raw index is therefore a
deterministic tie breaker without changing chronological order.  At one exact
external batch epoch all arrival times agree, so the endpoint-job list uses
the natural raw-index order.

The module proves only source accounting facts: each ledger request is emitted
once and every endpoint job batch has aggregate work equal to the existing
`admittedWorkBatchAt` vector.  It does not identify a source batch with a GPS
segment endpoint until such a segment-level equality is separately proved.
It makes no stationary, Palm, infinite-horizon, or response-tail claim.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A source job identifier keeps both its class and its lexicographic
arrival-time/raw-index key. -/
abbrev SLA2026FiniteGPSJobId (Category : Type*) :=
  Category × Lex (ℝ × ℕ)

/-- The deterministic within-class ordering key.  Its lexicographic order is
arrival time first, with raw natural index only breaking exact ties. -/
def admittedWorkJobKey
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    Lex (ℝ × ℕ) :=
  toLex (arrivalTime n
    (multiclassForwardQueueingPrimitiveRawInterarrivals k omega), n)

/-- Construct one FCFS job from an arbitrary source key.  The class-specific
source ledger below only supplies keys originating from actual admitted raw
indices. -/
def admittedWorkFCFSJobOfKey
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category)
    (key : Lex (ℝ × ℕ)) :
    FiniteGPSFCFSJob (SLA2026FiniteGPSJobId Category) :=
  { identifier := (k, key)
    arrivalTime := (ofLex key).1
    residualWork := M.admittedWorkRequirement k (ofLex key).2 omega }

/-- The FCFS record for one actual raw source index. -/
def admittedWorkFCFSJob
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    FiniteGPSFCFSJob (SLA2026FiniteGPSJobId Category) :=
  M.admittedWorkFCFSJobOfKey omega k (admittedWorkJobKey omega k n)

omit [DecidableEq Category] in
@[simp]
theorem admittedWorkFCFSJob_identifier
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    (M.admittedWorkFCFSJob omega k n).identifier =
      (k, admittedWorkJobKey omega k n) := rfl

omit [DecidableEq Category] in
@[simp]
theorem admittedWorkFCFSJob_arrivalTime
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    (M.admittedWorkFCFSJob omega k n).arrivalTime =
      arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) := rfl

omit [DecidableEq Category] in
@[simp]
theorem admittedWorkFCFSJob_residualWork
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    (M.admittedWorkFCFSJob omega k n).residualWork =
      M.admittedWorkRequirement k n omega := rfl

/-- Finite lexicographic keys for all source jobs of one class in
`(start, horizon]`. -/
def admittedWorkClassJobKeys
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    Finset (Lex (ℝ × ℕ)) :=
  (M.admittedWorkArrivalIndicesBetween start horizon omega k).image
    (admittedWorkJobKey omega k)

/-- Chronological deterministic key order for one class's finite source
ledger. -/
def admittedWorkClassJobKeyTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    List (Lex (ℝ × ℕ)) :=
  (M.admittedWorkClassJobKeys start horizon omega k).sort (fun left right => left ≤ right)

/-- Ordered actual source jobs of one class over `(start, horizon]`. -/
def admittedWorkClassJobs
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    List (FiniteGPSFCFSJob (SLA2026FiniteGPSJobId Category)) :=
  (M.admittedWorkClassJobKeyTrace start horizon omega k).map
    (M.admittedWorkFCFSJobOfKey omega k)

/-- The raw source indices of one class arriving at one exact external batch
time. -/
def admittedWorkJobIndicesAt
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (k : Category) : Finset ℕ :=
  (M.admittedWorkArrivalIndicesBetween start horizon omega k).filter fun n =>
    arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) = eventTime

/-- Explicit source-identified FCFS jobs arriving at one aggregated external
batch time.  Since all jobs in each class list have the same arrival time,
natural raw-index order is a deterministic within-batch tie break. -/
def admittedWorkFCFSJobsAt
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ) :
    FiniteGPSFCFSEndpointJobs Category (SLA2026FiniteGPSJobId Category) where
  jobs := fun k =>
    ((M.admittedWorkJobIndicesAt start horizon omega eventTime k).sort
      (fun left right : ℕ => left ≤ right)).map (M.admittedWorkFCFSJob omega k)

omit [DecidableEq Category] in
/-- The source-key-to-job conversion is injective because the source key is
stored verbatim in the public job identifier. -/
theorem admittedWorkFCFSJobOfKey_injective
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    Function.Injective (M.admittedWorkFCFSJobOfKey omega k) := by
  intro left right hjob
  have hidentifier := congrArg FiniteGPSFCFSJob.identifier hjob
  exact congrArg Prod.snd hidentifier

omit [DecidableEq Category] in
/-- A raw source index belongs to the finite key set exactly when it belongs
to the class's actual `(start, horizon]` source ledger. -/
theorem mem_admittedWorkClassJobKeys_iff
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    admittedWorkJobKey omega k n ∈ M.admittedWorkClassJobKeys start horizon omega k ↔
      n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k := by
  constructor
  · intro hkey
    rcases Finset.mem_image.mp hkey with ⟨m, hm, hmn⟩
    have hindex : m = n := by
      have hsecond := congrArg (fun key : Lex (ℝ × ℕ) => (ofLex key).2) hmn
      simpa [admittedWorkJobKey] using hsecond
    simpa [hindex] using hm
  · intro hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

omit [DecidableEq Category] in
/-- The sorted key trace contains each finite source key exactly once. -/
theorem admittedWorkClassJobKeyTrace_nodup
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    (M.admittedWorkClassJobKeyTrace start horizon omega k).Nodup := by
  exact Finset.sort_nodup (M.admittedWorkClassJobKeys start horizon omega k)
    (fun left right : Lex (ℝ × ℕ) => left ≤ right)

omit [DecidableEq Category] in
/-- The key trace is lexicographically ordered by arrival time and raw-index
tie breaker. -/
theorem admittedWorkClassJobKeyTrace_pairwise
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    List.Pairwise (fun left right : Lex (ℝ × ℕ) => left ≤ right)
      (M.admittedWorkClassJobKeyTrace start horizon omega k) := by
  exact Finset.pairwise_sort (M.admittedWorkClassJobKeys start horizon omega k)
    (fun left right : Lex (ℝ × ℕ) => left ≤ right)

omit [DecidableEq Category] in
/-- Every source-job key occurs in the sorted key trace exactly when its raw
index is in the actual source ledger. -/
theorem mem_admittedWorkClassJobKeyTrace_iff
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    admittedWorkJobKey omega k n ∈ M.admittedWorkClassJobKeyTrace start horizon omega k ↔
      n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k := by
  rw [admittedWorkClassJobKeyTrace, Finset.mem_sort]
  exact M.mem_admittedWorkClassJobKeys_iff start horizon omega k n

omit [DecidableEq Category] in
/-- The class job list contains no duplicate source jobs. -/
theorem admittedWorkClassJobs_nodup
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    (M.admittedWorkClassJobs start horizon omega k).Nodup := by
  unfold admittedWorkClassJobs
  exact List.Nodup.map (M.admittedWorkFCFSJobOfKey_injective omega k)
    (M.admittedWorkClassJobKeyTrace_nodup start horizon omega k)

omit [DecidableEq Category] in
/-- The source job list is chronologically nondecreasing.  Exact time ties
remain in the deterministic raw-index order carried by the key trace. -/
theorem admittedWorkClassJobs_arrivalTime_pairwise
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    List.Pairwise (fun left right : FiniteGPSFCFSJob (SLA2026FiniteGPSJobId Category) =>
      left.arrivalTime ≤ right.arrivalTime)
      (M.admittedWorkClassJobs start horizon omega k) := by
  unfold admittedWorkClassJobs
  apply (M.admittedWorkClassJobKeyTrace_pairwise start horizon omega k).map
    (M.admittedWorkFCFSJobOfKey omega k)
  intro left right horder
  change (ofLex left).1 ≤ (ofLex right).1
  exact Prod.Lex.monotone_fst left right horder

omit [DecidableEq Category] in
/-- An actual raw source job occurs in the class FCFS list if and only if its
index belongs to the actual finite source ledger. -/
theorem mem_admittedWorkFCFSJob_classJobs_iff
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    M.admittedWorkFCFSJob omega k n ∈ M.admittedWorkClassJobs start horizon omega k ↔
      n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k := by
  constructor
  · intro hjob
    rw [admittedWorkClassJobs] at hjob
    rcases List.mem_map.mp hjob with ⟨key, hkey, hkey_job⟩
    have hkey_eq : key = admittedWorkJobKey omega k n := by
      have hidentifier := congrArg FiniteGPSFCFSJob.identifier hkey_job
      exact congrArg Prod.snd hidentifier
    subst key
    exact (M.mem_admittedWorkClassJobKeyTrace_iff start horizon omega k n).mp hkey
  · intro hn
    rw [admittedWorkClassJobs]
    apply List.mem_map.mpr
    refine ⟨admittedWorkJobKey omega k n, ?_, rfl⟩
    exact (M.mem_admittedWorkClassJobKeyTrace_iff start horizon omega k n).mpr hn

omit [DecidableEq Category] in
/-- Each source request in the finite ledger is represented once: it is in the
FCFS list and that list is duplicate-free. -/
theorem admittedWorkFCFSJob_appears_once
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ)
    (hn : n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k) :
    M.admittedWorkFCFSJob omega k n ∈ M.admittedWorkClassJobs start horizon omega k ∧
      (M.admittedWorkClassJobs start horizon omega k).Nodup := by
  exact ⟨(M.mem_admittedWorkFCFSJob_classJobs_iff start horizon omega k n).mpr hn,
    M.admittedWorkClassJobs_nodup start horizon omega k⟩

omit [DecidableEq Category] in
/-- The job representation is injective in the raw index within a fixed
class, because that index is retained in the identifier key. -/
theorem admittedWorkFCFSJob_injective
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    Function.Injective (M.admittedWorkFCFSJob omega k) := by
  intro left right hjob
  have hidentifier := congrArg FiniteGPSFCFSJob.identifier hjob
  have hkey := congrArg Prod.snd hidentifier
  have hindex := congrArg (fun key : Lex (ℝ × ℕ) => (ofLex key).2) hkey
  simpa [admittedWorkJobKey] using hindex

omit [DecidableEq Category] in
/-- Membership in an endpoint raw-index batch is exactly membership in the
source ledger together with equality of the source arrival time to that batch
epoch. -/
theorem mem_admittedWorkJobIndicesAt_iff
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (k : Category) (n : ℕ) :
    n ∈ M.admittedWorkJobIndicesAt start horizon omega eventTime k ↔
      n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k ∧
        arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) =
          eventTime := by
  simp [admittedWorkJobIndicesAt]

omit [DecidableEq Category] in
/-- Every per-class endpoint batch list is duplicate-free. -/
theorem admittedWorkFCFSJobsAt_jobs_nodup
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (k : Category) :
    ((M.admittedWorkFCFSJobsAt start horizon omega eventTime).jobs k).Nodup := by
  unfold admittedWorkFCFSJobsAt
  exact List.Nodup.map (M.admittedWorkFCFSJob_injective omega k)
    (Finset.sort_nodup
      (M.admittedWorkJobIndicesAt start horizon omega eventTime k)
      (fun left right : ℕ => left ≤ right))

omit [DecidableEq Category] in
/-- A raw source job occurs in an endpoint job list exactly at its own source
arrival epoch. -/
theorem mem_admittedWorkFCFSJob_jobsAt_iff
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (k : Category) (n : ℕ) :
    M.admittedWorkFCFSJob omega k n ∈
        (M.admittedWorkFCFSJobsAt start horizon omega eventTime).jobs k ↔
      n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k ∧
        arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) =
          eventTime := by
  constructor
  · intro hjob
    unfold admittedWorkFCFSJobsAt at hjob
    rcases List.mem_map.mp hjob with ⟨m, hm, hm_job⟩
    have hindex : m = n := M.admittedWorkFCFSJob_injective omega k hm_job
    subst m
    apply (M.mem_admittedWorkJobIndicesAt_iff start horizon omega eventTime k n).mp
    exact (Finset.mem_sort (fun left right : ℕ => left ≤ right)).mp hm
  · rintro ⟨hn, htime⟩
    unfold admittedWorkFCFSJobsAt
    apply List.mem_map.mpr
    refine ⟨n, ?_, rfl⟩
    apply (Finset.mem_sort (fun left right : ℕ => left ≤ right)).mpr
    exact (M.mem_admittedWorkJobIndicesAt_iff start horizon omega eventTime k n).mpr
      ⟨hn, htime⟩

/-- Every raw request from the finite source ledger appears in precisely one
endpoint batch: the one indexed by its actual arrival time. -/
theorem admittedWorkFCFSJob_appears_in_exactly_one_batch
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ)
    (hn : n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k) :
    M.admittedWorkFCFSJob omega k n ∈
        (M.admittedWorkFCFSJobsAt start horizon omega
          (arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega))).jobs k ∧
      ∀ eventTime,
        M.admittedWorkFCFSJob omega k n ∈
          (M.admittedWorkFCFSJobsAt start horizon omega eventTime).jobs k →
          eventTime = arrivalTime n
            (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) := by
  constructor
  · exact (M.mem_admittedWorkFCFSJob_jobsAt_iff
      start horizon omega
      (arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega)) k n).mpr
      ⟨hn, rfl⟩
  · intro eventTime hjob
    exact (M.mem_admittedWorkFCFSJob_jobsAt_iff start horizon omega eventTime k n).mp hjob |>.2.symm

omit [DecidableEq Category] in
/-- Summing the explicit source jobs at one external epoch gives exactly the
existing aggregate admitted-work batch.  This is a source-ledger identity; it
does not yet assert compatibility with any separately constructed GPS segment. -/
theorem admittedWorkFCFSJobsAt_classWork_eq_admittedWorkBatchAt
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (k : Category) :
    (M.admittedWorkFCFSJobsAt start horizon omega eventTime).classWork k =
      M.admittedWorkBatchAt start horizon omega eventTime k := by
  let indices := M.admittedWorkJobIndicesAt start horizon omega eventTime k
  have hnodup : (indices.sort (fun left right : ℕ => left ≤ right)).Nodup :=
    Finset.sort_nodup indices (fun left right : ℕ => left ≤ right)
  have htoFinset : (indices.sort (fun left right : ℕ => left ≤ right)).toFinset =
      indices := by
    ext n
    simp
  simp [FiniteGPSFCFSEndpointJobs.classWork, finiteGPSFCFSJobWork,
    admittedWorkFCFSJobsAt]
  change ((indices.sort (fun left right : ℕ => left ≤ right)).map
      (fun n => M.admittedWorkRequirement k n omega)).sum =
    M.admittedWorkBatchAt start horizon omega eventTime k
  calc
    ((indices.sort (fun left right : ℕ => left ≤ right)).map
        (fun n => M.admittedWorkRequirement k n omega)).sum =
        (indices.sort (fun left right : ℕ => left ≤ right)).toFinset.sum
          (fun n => M.admittedWorkRequirement k n omega) :=
      (List.sum_toFinset (fun n => M.admittedWorkRequirement k n omega) hnodup).symm
    _ = ∑ n ∈ indices, M.admittedWorkRequirement k n omega := by
      rw [htoFinset]
    _ = M.admittedWorkBatchAt start horizon omega eventTime k := by
      rfl

omit [DecidableEq Category] in
/-- Nonnegative admitted work marks make every explicitly identified source
endpoint job nonnegative. -/
theorem admittedWorkFCFSJobsAt_nonnegative
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (eventTime : ℝ) :
    (M.admittedWorkFCFSJobsAt start horizon omega eventTime).Nonnegative := by
  intro k job hjob
  unfold admittedWorkFCFSJobsAt at hjob
  rcases List.mem_map.mp hjob with ⟨n, _hn, rfl⟩
  exact hwork_nonneg k n

/-- A source endpoint batch retains its exact external epoch together with the
identified FCFS jobs that arrive then.  This is intentionally separate from a
GPS execution segment: the latter may also end at an internal depletion. -/
structure SLA2026FiniteGPSTimedEndpointJobs (Category : Type*) where
  eventTime : ℝ
  endpointJobs :
    FiniteGPSFCFSEndpointJobs Category (SLA2026FiniteGPSJobId Category)

/-- The complete chronological ledger of actual source endpoint-job batches.
There is one entry for each distinct external batch time, including a single
entry for simultaneous arrivals from multiple categories. -/
def admittedWorkFCFSSourceEndpointBatchTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) :
    List (SLA2026FiniteGPSTimedEndpointJobs Category) :=
  (M.admittedWorkBatchTimeTrace start horizon omega).map fun eventTime =>
    { eventTime := eventTime
      endpointJobs := M.admittedWorkFCFSJobsAt start horizon omega eventTime }

omit [DecidableEq Category] in
/-- Every timed source endpoint batch has the aggregate work vector supplied
to the corresponding source batch trace epoch. -/
theorem admittedWorkFCFSSourceEndpointBatchTrace_classWork
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath)
    (batch : SLA2026FiniteGPSTimedEndpointJobs Category)
    (hbatch : batch ∈ M.admittedWorkFCFSSourceEndpointBatchTrace start horizon omega)
    (k : Category) :
    batch.endpointJobs.classWork k =
      M.admittedWorkBatchAt start horizon omega batch.eventTime k := by
  rcases List.mem_map.mp hbatch with ⟨eventTime, _heventTime, rfl⟩
  exact M.admittedWorkFCFSJobsAt_classWork_eq_admittedWorkBatchAt
    start horizon omega eventTime k

omit [DecidableEq Category] in
/-- A source request has one and only one external endpoint epoch in the
finite source batch trace.  The conclusion is about the concrete source
ledger, not about computational depletion or terminal-fence segments. -/
theorem admittedWorkFCFSJob_existsUnique_sourceEndpointTime
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ)
    (hn : n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k) :
    ∃! eventTime : ℝ,
      eventTime ∈ M.admittedWorkBatchTimeTrace start horizon omega ∧
        M.admittedWorkFCFSJob omega k n ∈
          (M.admittedWorkFCFSJobsAt start horizon omega eventTime).jobs k := by
  let sourceTime := arrivalTime n
    (multiclassForwardQueueingPrimitiveRawInterarrivals k omega)
  have hsourceTime_batch : sourceTime ∈ M.admittedWorkBatchTimes start horizon omega := by
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hsourceTime_trace : sourceTime ∈ M.admittedWorkBatchTimeTrace start horizon omega :=
    (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr hsourceTime_batch
  refine ⟨sourceTime, ?_, ?_⟩
  · constructor
    · exact hsourceTime_trace
    · exact (M.mem_admittedWorkFCFSJob_jobsAt_iff start horizon omega sourceTime k n).mpr
        ⟨hn, rfl⟩
  · intro eventTime heventTime
    exact (M.mem_admittedWorkFCFSJob_jobsAt_iff start horizon omega eventTime k n).mp
      heventTime.2 |>.2.symm

omit [DecidableEq Category] in
/-- Equivalently, each source request occurs once in the explicit timed source
endpoint-job ledger. -/
theorem admittedWorkFCFSJob_appears_once_in_sourceEndpointBatchTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ)
    (hn : n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k) :
    ∃! batch : SLA2026FiniteGPSTimedEndpointJobs Category,
      batch ∈ M.admittedWorkFCFSSourceEndpointBatchTrace start horizon omega ∧
        M.admittedWorkFCFSJob omega k n ∈ batch.endpointJobs.jobs k := by
  let sourceTime := arrivalTime n
    (multiclassForwardQueueingPrimitiveRawInterarrivals k omega)
  have hsourceTime_batch : sourceTime ∈ M.admittedWorkBatchTimes start horizon omega := by
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hsourceTime_trace : sourceTime ∈ M.admittedWorkBatchTimeTrace start horizon omega :=
    (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr hsourceTime_batch
  let sourceBatch : SLA2026FiniteGPSTimedEndpointJobs Category :=
    { eventTime := sourceTime
      endpointJobs := M.admittedWorkFCFSJobsAt start horizon omega sourceTime }
  refine ⟨sourceBatch, ?_, ?_⟩
  · constructor
    · exact List.mem_map.mpr ⟨sourceTime, hsourceTime_trace, rfl⟩
    · simpa [sourceBatch] using
        (M.mem_admittedWorkFCFSJob_jobsAt_iff start horizon omega sourceTime k n).mpr
          ⟨hn, rfl⟩
  · intro batch hbatch
    rcases List.mem_map.mp hbatch.1 with ⟨eventTime, heventTime, hbatch_eq⟩
    subst batch
    have heventTime_eq_sourceTime : eventTime = sourceTime :=
      (M.mem_admittedWorkFCFSJob_jobsAt_iff start horizon omega eventTime k n).mp
        hbatch.2 |>.2.symm
    subst eventTime
    rfl

/-- Empty endpoint-job data used for every computational endpoint: an internal
depletion or a terminal horizon fence introduces no source request. -/
def admittedWorkFCFSComputationalEndpointJobs :
    FiniteGPSFCFSEndpointJobs Category (SLA2026FiniteGPSJobId Category) where
  jobs := fun _ => []

omit [DecidableEq Category] in
@[simp]
theorem admittedWorkFCFSComputationalEndpointJobs_jobs
    (k : Category) :
    (admittedWorkFCFSComputationalEndpointJobs (Category := Category)).jobs k = [] := rfl

omit [DecidableEq Category] in
@[simp]
theorem admittedWorkFCFSComputationalEndpointJobs_classWork
    (k : Category) :
    (admittedWorkFCFSComputationalEndpointJobs (Category := Category)).classWork k = 0 := by
  simp [FiniteGPSFCFSEndpointJobs.classWork,
    admittedWorkFCFSComputationalEndpointJobs]

omit [DecidableEq Category] in
theorem admittedWorkFCFSComputationalEndpointJobs_nonnegative :
    (admittedWorkFCFSComputationalEndpointJobs (Category := Category)).Nonnegative := by
  intro k job hjob
  simp [admittedWorkFCFSComputationalEndpointJobs] at hjob

omit [DecidableEq Category] in
/-- A computational endpoint contains no source job, regardless of the raw
index. -/
theorem admittedWorkFCFSJob_not_mem_computationalEndpointJobs
    (M : SLA2026BoroughQueueingInput Category)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) (n : ℕ) :
    M.admittedWorkFCFSJob omega k n ∉
      (admittedWorkFCFSComputationalEndpointJobs (Category := Category)).jobs k := by
  simp [admittedWorkFCFSComputationalEndpointJobs]

/-- When the actual GPS kernel reaches a scheduled source batch, the explicit
jobs at that source epoch exactly decompose the segment's endpoint work. -/
theorem admittedWorkFCFSJobsAt_aggregateCompatible_buildExecutionSegment_of_external
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hExternal :
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay).endpointIsExternalBatch = true) :
    (M.admittedWorkFCFSJobsAt start horizon omega eventTime).AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay) := by
  intro k
  rw [M.admittedWorkFCFSJobsAt_classWork_eq_admittedWorkBatchAt]
  exact (finiteGPSBuildExecutionSegment_endpointBatch_eq_batchWork_of_external
    capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
    currentTime nextBatchDelay hExternal k).symm

/-- If a source-gap kernel segment ends at an internal depletion instead of
the scheduled external epoch, its endpoint is represented by the empty
computational job batch rather than by a source arrival. -/
theorem admittedWorkFCFSComputationalEndpointJobs_aggregateCompatible_buildExecutionSegment_of_not_external
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hnotExternal :
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay).endpointIsExternalBatch = false) :
    (admittedWorkFCFSComputationalEndpointJobs (Category := Category)).AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay) := by
  intro k
  rw [admittedWorkFCFSComputationalEndpointJobs_classWork]
  exact (finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_not_external
    capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
    currentTime nextBatchDelay hnotExternal k).symm

/-- Choose the endpoint-job decomposition from a segment's computed endpoint
tag.  This is used only for segments built toward the displayed scheduled
source epoch: an external endpoint receives that epoch's source jobs, while
an internal endpoint receives the empty computational batch. -/
def admittedWorkFiniteGPSEndpointJobsForSegment
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (segment : FiniteGPSExecutionSegment Category) :
    FiniteGPSFCFSEndpointJobs Category (SLA2026FiniteGPSJobId Category) :=
  if segment.endpointIsExternalBatch = true then
    M.admittedWorkFCFSJobsAt start horizon omega eventTime
  else
    admittedWorkFCFSComputationalEndpointJobs

/-- The selected endpoint-job decomposition is nonnegative whenever the
direct admitted work marks are nonnegative. -/
theorem admittedWorkFiniteGPSEndpointJobsForSegment_nonnegative
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (eventTime : ℝ) (segment : FiniteGPSExecutionSegment Category) :
    (M.admittedWorkFiniteGPSEndpointJobsForSegment
      start horizon omega eventTime segment).Nonnegative := by
  by_cases hExternal : segment.endpointIsExternalBatch = true
  · simpa [admittedWorkFiniteGPSEndpointJobsForSegment, hExternal] using
      (M.admittedWorkFCFSJobsAt_nonnegative start horizon omega
        hwork_nonneg eventTime)
  · simpa [admittedWorkFiniteGPSEndpointJobsForSegment, hExternal] using
      (admittedWorkFCFSComputationalEndpointJobs_nonnegative (Category := Category))

/-- One source-labelled concrete GPS segment together with the job batch
selected from its computed endpoint tag. -/
def admittedWorkFiniteGPSBuildSegmentJobStep
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category) :=
  { segment := finiteGPSBuildExecutionSegment capacity weight work
      (M.admittedWorkBatchAt start horizon omega eventTime)
      currentTime nextBatchDelay
    endpointJobs := M.admittedWorkFiniteGPSEndpointJobsForSegment
      start horizon omega eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay) }

/-- The identified endpoint jobs of a concrete source-labelled build step
have nonnegative work under the direct source-mark hypothesis. -/
theorem admittedWorkFiniteGPSBuildSegmentJobStep_endpointJobs_nonnegative
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (eventTime : ℝ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (M.admittedWorkFiniteGPSBuildSegmentJobStep
      start horizon omega eventTime capacity weight work
      currentTime nextBatchDelay).endpointJobs.Nonnegative := by
  simpa [admittedWorkFiniteGPSBuildSegmentJobStep] using
    (M.admittedWorkFiniteGPSEndpointJobsForSegment_nonnegative
      start horizon omega hwork_nonneg eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay))

/-- The endpoint-job choice is aggregate-compatible with the actual kernel
segment in both possible cases of the computed endpoint tag. -/
theorem admittedWorkFiniteGPSEndpointJobsForBuildSegment_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (M.admittedWorkFiniteGPSEndpointJobsForSegment start horizon omega eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay)).AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay) := by
  by_cases hExternal :
      (finiteGPSBuildExecutionSegment capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay).endpointIsExternalBatch = true
  · simpa [admittedWorkFiniteGPSEndpointJobsForSegment, hExternal] using
      (M.admittedWorkFCFSJobsAt_aggregateCompatible_buildExecutionSegment_of_external
        start horizon omega eventTime capacity weight work currentTime nextBatchDelay hExternal)
  · have hnotExternal :
        (finiteGPSBuildExecutionSegment capacity weight work
          (M.admittedWorkBatchAt start horizon omega eventTime)
          currentTime nextBatchDelay).endpointIsExternalBatch = false := by
      cases htag :
          (finiteGPSBuildExecutionSegment capacity weight work
            (M.admittedWorkBatchAt start horizon omega eventTime)
            currentTime nextBatchDelay).endpointIsExternalBatch <;> simp_all
    simpa [admittedWorkFiniteGPSEndpointJobsForSegment, hExternal] using
      (M.admittedWorkFCFSComputationalEndpointJobs_aggregateCompatible_buildExecutionSegment_of_not_external
        start horizon omega eventTime capacity weight work currentTime nextBatchDelay hnotExternal)

/-- The explicit source-labelled job step has aggregate endpoint work exactly
equal to its stored GPS segment endpoint batch. -/
theorem admittedWorkFiniteGPSBuildSegmentJobStep_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (M.admittedWorkFiniteGPSBuildSegmentJobStep
      start horizon omega eventTime capacity weight work currentTime nextBatchDelay).endpointJobs.AggregateCompatible
      (M.admittedWorkFiniteGPSBuildSegmentJobStep
        start horizon omega eventTime capacity weight work currentTime nextBatchDelay).segment := by
  simpa [admittedWorkFiniteGPSBuildSegmentJobStep] using
    (M.admittedWorkFiniteGPSEndpointJobsForBuildSegment_aggregateCompatible
      start horizon omega eventTime capacity weight work currentTime nextBatchDelay)

/-- Prepend one concrete source-labelled GPS step to a compatible FCFS tail.
All service and endpoint-job side conditions are discharged from the actual
kernel step and direct source work marks. -/
theorem admittedWorkFiniteGPSBuildSegmentJobStep_compatible_cons
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (tail : List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category)))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (htail : FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSApplySegment initial
        (M.admittedWorkFiniteGPSBuildSegmentJobStep
          start horizon omega eventTime capacity weight work
          currentTime nextBatchDelay).segment
        (M.admittedWorkFiniteGPSBuildSegmentJobStep
          start horizon omega eventTime capacity weight work
          currentTime nextBatchDelay).endpointJobs)
      (M.admittedWorkFiniteGPSBuildSegmentJobStep
        start horizon omega eventTime capacity weight work
        currentTime nextBatchDelay).segment.endpointWorkload tail) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (M.admittedWorkFiniteGPSBuildSegmentJobStep
        start horizon omega eventTime capacity weight work
        currentTime nextBatchDelay :: tail) := by
  let step := M.admittedWorkFiniteGPSBuildSegmentJobStep
    start horizon omega eventTime capacity weight work currentTime nextBatchDelay
  change
    (∀ i, initial.classWork i = work i) ∧
      (∀ i, work i = step.segment.startWorkload i) ∧
      step.endpointJobs.AggregateCompatible step.segment ∧
      step.endpointJobs.Nonnegative ∧
      (∀ i, 0 ≤ step.segment.serviceIncrement i) ∧
      (∀ i, step.segment.serviceIncrement i ≤ initial.classWork i) ∧
      (∀ i, step.segment.endpointWorkload i =
        step.segment.startWorkload i + step.segment.endpointBatch i -
          step.segment.serviceIncrement i) ∧
      FiniteGPSFCFSRunSegmentStepsCompatible
        (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        step.segment.endpointWorkload tail
  refine ⟨hinitial_matches_work, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · exact M.admittedWorkFiniteGPSBuildSegmentJobStep_aggregateCompatible
      start horizon omega eventTime capacity weight work currentTime nextBatchDelay
  · exact M.admittedWorkFiniteGPSBuildSegmentJobStep_endpointJobs_nonnegative
      start horizon omega hsource_work_nonneg eventTime capacity weight work
      currentTime nextBatchDelay
  · intro i
    simpa [step, admittedWorkFiniteGPSBuildSegmentJobStep] using
      (finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
        (batchWork := M.admittedWorkBatchAt start horizon omega eventTime)
        (startTime := currentTime)
        hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hnextBatchDelay_nonneg (i := i))
  · intro i
    rw [hinitial_matches_work i]
    simpa [step, admittedWorkFiniteGPSBuildSegmentJobStep] using
      (finiteGPSBuildExecutionSegment_serviceIncrement_le_startWorkload
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay i)
  · intro i
    simpa [step, admittedWorkFiniteGPSBuildSegmentJobStep] using
      (finiteGPSBuildExecutionSegment_balance capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay i)
  · simpa [step] using htail

/-- A single concrete source-labelled GPS step gives a compatible finite FCFS
transition from an initial ledger whose aggregate work is the step's input. -/
theorem admittedWorkFiniteGPSBuildSegmentJobStep_compatible_singleton
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      [M.admittedWorkFiniteGPSBuildSegmentJobStep
        start horizon omega eventTime capacity weight work
        currentTime nextBatchDelay] := by
  let step := M.admittedWorkFiniteGPSBuildSegmentJobStep
    start horizon omega eventTime capacity weight work currentTime nextBatchDelay
  have hnext_matches : ∀ i,
      (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).classWork i =
        step.segment.endpointWorkload i := by
    intro i
    simpa [step, admittedWorkFiniteGPSBuildSegmentJobStep] using
      (finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
        (JobId := SLA2026FiniteGPSJobId Category)
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay initial step.endpointJobs
        hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work
        (by
          simpa [step] using
            (M.admittedWorkFiniteGPSBuildSegmentJobStep_aggregateCompatible
              start horizon omega eventTime capacity weight work
              currentTime nextBatchDelay)) i)
  simpa [step] using
    (M.admittedWorkFiniteGPSBuildSegmentJobStep_compatible_cons
      start horizon omega eventTime capacity weight work currentTime nextBatchDelay
      initial [] hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hsource_work_nonneg hnextBatchDelay_nonneg hinitial_nonneg
      hinitial_matches_work hnext_matches)

/-- Mirror `finiteGPSRunGapSegments` while retaining explicit endpoint jobs.
The scheduled source epoch is fixed through the recursion; only a segment
whose computed tag says it actually reached that epoch receives its source
jobs. -/
def admittedWorkFiniteGPSGapSegmentJobSteps
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category)) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := M.admittedWorkFiniteGPSBuildSegmentJobStep
        start horizon omega eventTime capacity weight work currentTime nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay
      if duration = nextBatchDelay then
        [step]
      else
        step :: M.admittedWorkFiniteGPSGapSegmentJobSteps start horizon omega eventTime
          fuel capacity weight nextWork (currentTime + duration) (nextBatchDelay - duration)

/-- Forgetting endpoint-job metadata from the annotated gap returns exactly
the generic concrete segment list, not a separately supplied certificate. -/
theorem admittedWorkFiniteGPSGapSegmentJobSteps_segments
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (M.admittedWorkFiniteGPSGapSegmentJobSteps
      start horizon omega eventTime fuel capacity weight work currentTime nextBatchDelay).map
        (fun step => step.segment) =
      finiteGPSRunGapSegments fuel capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        currentTime nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [admittedWorkFiniteGPSGapSegmentJobSteps, finiteGPSRunGapSegments]
  | succ fuel ih =>
      simp only [admittedWorkFiniteGPSGapSegmentJobSteps,
        finiteGPSRunGapSegments]
      split <;>
        simp [admittedWorkFiniteGPSBuildSegmentJobStep, ih]

/-- The final endpoint workload read from the annotated gap steps is exactly
the final workload of the bounded GPS gap runner. -/
theorem admittedWorkFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    finiteGPSFCFSSegmentStepsEndpointWorkload work
      (M.admittedWorkFiniteGPSGapSegmentJobSteps
        start horizon omega eventTime fuel capacity weight work currentTime nextBatchDelay) =
      (finiteGPSRunGap fuel capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        nextBatchDelay).workload := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [admittedWorkFiniteGPSGapSegmentJobSteps, finiteGPSRunGap,
        finiteGPSFCFSSegmentStepsEndpointWorkload]
  | succ fuel ih =>
      simp only [admittedWorkFiniteGPSGapSegmentJobSteps, finiteGPSRunGap]
      split <;>
        simp [admittedWorkFiniteGPSBuildSegmentJobStep,
          finiteGPSFCFSSegmentStepsEndpointWorkload, ih]

/-- A compatible finite FCFS fold preserves nonnegative residual jobs.  This
local helper is used only to carry the direct-source ledger from one concrete
GPS gap to the next. -/
theorem admittedWorkFiniteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (initialWorkload : Category → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category)))
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible :
      FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    (finiteGPSFCFSRunSegmentSteps initial steps).Nonnegative := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial_nonneg
  | cons step steps ih =>
      rcases hcompatible with ⟨_hledger_initial, _hinitial_start,
        _hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        _hservice_le_ledger, _hsegment_balance, htail⟩
      have hnext_nonneg :
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
        finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
          hinitial_nonneg hservice_nonneg hendpoint_nonneg
      simpa [finiteGPSFCFSRunSegmentSteps] using
        ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          (initialWorkload := step.segment.endpointWorkload)
          hnext_nonneg htail

/-- Compatibility composes along concrete FCFS step lists when the right list
starts from the exact computed ledger and endpoint workload of the left list. -/
theorem admittedWorkFiniteGPSFCFSRunSegmentStepsCompatible_append
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (initialWorkload : Category → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (SLA2026FiniteGPSJobId Category)))
    (hleft : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload left)
    (hright : FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSRunSegmentSteps initial left)
      (finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload left) right) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload (left ++ right) := by
  induction left generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using hright
  | cons step left ih =>
      rcases hleft with ⟨hledger_initial, hinitial_start,
        hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        hservice_le_ledger, hsegment_balance, hleft_tail⟩
      refine ⟨hledger_initial, hinitial_start, hbatch_compatible,
        hendpoint_nonneg, hservice_nonneg, hservice_le_ledger,
        hsegment_balance, ?_⟩
      apply ih
      · exact hleft_tail
      · simpa [finiteGPSFCFSRunSegmentSteps,
          finiteGPSFCFSSegmentStepsEndpointWorkload] using hright

/-- Every segment in the annotated gap has an explicit endpoint-job list that
matches its actual aggregate endpoint work. -/
theorem admittedWorkFiniteGPSGapSegmentJobSteps_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ step ∈ M.admittedWorkFiniteGPSGapSegmentJobSteps
      start horizon omega eventTime fuel capacity weight work currentTime nextBatchDelay,
      step.endpointJobs.AggregateCompatible step.segment := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [admittedWorkFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      unfold admittedWorkFiniteGPSGapSegmentJobSteps
      dsimp only
      split
      · intro step hstep
        have hstep_eq : step = M.admittedWorkFiniteGPSBuildSegmentJobStep
            start horizon omega eventTime capacity weight work currentTime nextBatchDelay := by
          simpa using hstep
        subst step
        exact M.admittedWorkFiniteGPSBuildSegmentJobStep_aggregateCompatible
          start horizon omega eventTime capacity weight work currentTime nextBatchDelay
      · intro step hstep
        rcases List.mem_cons.mp hstep with hhead | htail
        · subst step
          exact M.admittedWorkFiniteGPSBuildSegmentJobStep_aggregateCompatible
            start horizon omega eventTime capacity weight work currentTime nextBatchDelay
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay)
            (currentTime := currentTime +
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            (nextBatchDelay := nextBatchDelay -
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            step htail

/-- The identified FCFS jobs realize every bounded concrete source gap, not
merely its endpoint-batch totals.  The proof follows the same internal-event
recursion as the GPS gap runner. -/
theorem admittedWorkFiniteGPSGapSegmentJobSteps_compatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (M.admittedWorkFiniteGPSGapSegmentJobSteps
        start horizon omega eventTime fuel capacity weight work currentTime nextBatchDelay) := by
  induction fuel generalizing work currentTime nextBatchDelay initial with
  | zero =>
      simpa [admittedWorkFiniteGPSGapSegmentJobSteps] using hinitial_matches_work
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := M.admittedWorkFiniteGPSBuildSegmentJobStep
        start horizon omega eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsingle := M.admittedWorkFiniteGPSBuildSegmentJobStep_compatible_singleton
          start horizon omega eventTime capacity weight work currentTime nextBatchDelay
          initial hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hsource_work_nonneg hnextBatchDelay_nonneg hinitial_nonneg
          hinitial_matches_work
        simpa [admittedWorkFiniteGPSGapSegmentJobSteps, duration, hduration, step] using hsingle
      · have hinternal :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay := by
            simpa [duration] using hduration
        have hnext_work_nonneg : ∀ j, 0 ≤
            finiteGPSNextEventState capacity weight work
              (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay j := by
            exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hresidual_delay_nonneg : 0 ≤ nextBatchDelay - duration := by
            rw [show duration = finiteGPSNextStepDuration capacity weight work nextBatchDelay by rfl]
            exact sub_nonneg.mpr
              (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
                nextBatchDelay)
        have hstep_service_nonneg : ∀ i, 0 ≤ step.segment.serviceIncrement i := by
            intro i
            simpa [step, admittedWorkFiniteGPSBuildSegmentJobStep] using
              (finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
                (batchWork := M.admittedWorkBatchAt start horizon omega eventTime)
                (startTime := currentTime)
                hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
                hnextBatchDelay_nonneg (i := i))
        have hstep_endpoint_nonneg : step.endpointJobs.Nonnegative := by
            simpa [step] using
              (M.admittedWorkFiniteGPSBuildSegmentJobStep_endpointJobs_nonnegative
                start horizon omega hsource_work_nonneg eventTime capacity weight work
                currentTime nextBatchDelay)
        have hnext_initial_nonneg :
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
          finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
            hinitial_nonneg hstep_service_nonneg hstep_endpoint_nonneg
        have hnext_initial_matches : ∀ i,
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).classWork i =
              finiteGPSNextEventState capacity weight work
                (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay i := by
            intro i
            simpa [step, admittedWorkFiniteGPSBuildSegmentJobStep] using
              (finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
                (JobId := SLA2026FiniteGPSJobId Category)
                capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
                currentTime nextBatchDelay initial step.endpointJobs
                hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
                hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work
                (by
                  simpa [step] using
                    (M.admittedWorkFiniteGPSBuildSegmentJobStep_aggregateCompatible
                      start horizon omega eventTime capacity weight work
                      currentTime nextBatchDelay)) i)
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work
            (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration)
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          hnext_work_nonneg hresidual_delay_nonneg hnext_initial_nonneg
          hnext_initial_matches
        have hcons := M.admittedWorkFiniteGPSBuildSegmentJobStep_compatible_cons
          start horizon omega eventTime capacity weight work currentTime nextBatchDelay
          initial
          (M.admittedWorkFiniteGPSGapSegmentJobSteps start horizon omega eventTime
            fuel capacity weight
            (finiteGPSNextEventState capacity weight work
              (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay)
            (currentTime + duration) (nextBatchDelay - duration))
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hsource_work_nonneg hnextBatchDelay_nonneg hinitial_nonneg
          hinitial_matches_work (by simpa [step] using htail)
        simpa [admittedWorkFiniteGPSGapSegmentJobSteps, duration, hduration, step] using hcons

/-- Extract only the external endpoint-job batches from an annotated segment
ledger.  Internal depletion segments and the terminal fence are deliberately
excluded by their computed endpoint tag. -/
def admittedWorkFiniteGPSExternalEndpointJobBatches
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (SLA2026FiniteGPSJobId Category))) :
    List (FiniteGPSFCFSEndpointJobs Category (SLA2026FiniteGPSJobId Category)) :=
  steps.filterMap fun step =>
    if step.segment.endpointIsExternalBatch = true then some step.endpointJobs else none

/-- If the bounded gap actually reaches its scheduled source batch, its
annotated external endpoint-job ledger is exactly that one source batch. -/
theorem admittedWorkFiniteGPSGapSegmentJobSteps_externalEndpointJobBatches_eq_singleton_of_batchApplied
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatchApplied :
      (finiteGPSRunGap fuel capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        nextBatchDelay).batchApplied = true) :
    admittedWorkFiniteGPSExternalEndpointJobBatches
      (M.admittedWorkFiniteGPSGapSegmentJobSteps
        start horizon omega eventTime fuel capacity weight work currentTime nextBatchDelay) =
      [M.admittedWorkFCFSJobsAt start horizon omega eventTime] := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGap] at hbatchApplied
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hduration' :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay =
              nextBatchDelay := by
            simpa [duration] using hduration
        have htag :
            (M.admittedWorkFiniteGPSBuildSegmentJobStep
              start horizon omega eventTime capacity weight work
              currentTime nextBatchDelay).segment.endpointIsExternalBatch = true := by
            change (finiteGPSBuildExecutionSegment capacity weight work
              (M.admittedWorkBatchAt start horizon omega eventTime)
              currentTime nextBatchDelay).endpointIsExternalBatch = true
            exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              currentTime nextBatchDelay |>.mpr hduration
        have hendpoint :
            (M.admittedWorkFiniteGPSBuildSegmentJobStep
              start horizon omega eventTime capacity weight work
              currentTime nextBatchDelay).endpointJobs =
              M.admittedWorkFCFSJobsAt start horizon omega eventTime := by
            have htag' :
                (finiteGPSBuildExecutionSegment capacity weight work
                  (M.admittedWorkBatchAt start horizon omega eventTime)
                  currentTime nextBatchDelay).endpointIsExternalBatch = true := by
                simpa [admittedWorkFiniteGPSBuildSegmentJobStep] using htag
            simp [admittedWorkFiniteGPSBuildSegmentJobStep,
              admittedWorkFiniteGPSEndpointJobsForSegment, htag']
        rw [show M.admittedWorkFiniteGPSGapSegmentJobSteps
            start horizon omega eventTime (fuel + 1) capacity weight work
            currentTime nextBatchDelay =
            [M.admittedWorkFiniteGPSBuildSegmentJobStep
              start horizon omega eventTime capacity weight work
              currentTime nextBatchDelay] by
          simp [admittedWorkFiniteGPSGapSegmentJobSteps, hduration']]
        simp [admittedWorkFiniteGPSExternalEndpointJobBatches, htag, hendpoint]
      · have htailApplied :
            (finiteGPSRunGap fuel capacity weight
              (finiteGPSNextEventState capacity weight work
                (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay)
              (M.admittedWorkBatchAt start horizon omega eventTime)
              (nextBatchDelay - duration)).batchApplied = true := by
            simpa [finiteGPSRunGap, duration, hduration] using hbatchApplied
        have hheadNotExternal :
            (M.admittedWorkFiniteGPSBuildSegmentJobStep
              start horizon omega eventTime capacity weight work
              currentTime nextBatchDelay).segment.endpointIsExternalBatch ≠ true := by
            intro htag
            apply hduration
            apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              currentTime nextBatchDelay |>.mp
            simpa [admittedWorkFiniteGPSBuildSegmentJobStep] using htag
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work
            (M.admittedWorkBatchAt start horizon omega eventTime) nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration) htailApplied
        simpa [admittedWorkFiniteGPSExternalEndpointJobBatches,
          admittedWorkFiniteGPSGapSegmentJobSteps, duration, hduration,
          hheadNotExternal] using htail

/-- Mirror the generic finite batch-trace recursion with the source-labelled
gap annotations.  The recursion stops at the same actual partial gap if a
bounded runner does not reach a later scheduled batch. -/
def admittedWorkFiniteGPSBatchTraceSegmentJobSteps
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight : Category → ℝ) (currentTime : ℝ) (work : Category → ℝ) :
    List ℝ → List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category))
  | [] => []
  | eventTime :: times =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gapSteps := M.admittedWorkFiniteGPSGapSegmentJobSteps
        start horizon omega eventTime gapFuel capacity weight work
        currentTime (eventTime - currentTime)
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (M.admittedWorkBatchAt start horizon omega eventTime)
        (eventTime - currentTime)
      if gap.batchApplied = true then
        gapSteps ++ M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
          start horizon omega capacity weight eventTime gap.workload times
      else
        gapSteps

/-- The annotated batch recursion continues exactly when the generic runner
reaches the scheduled source batch. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime eventTime : ℝ) (times : List ℝ)
    (hbatchApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        (eventTime - currentTime)).batchApplied = true) :
    M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
      start horizon omega capacity weight currentTime work (eventTime :: times) =
      M.admittedWorkFiniteGPSGapSegmentJobSteps start horizon omega eventTime
        ((finiteGPSActiveClasses work).card + 1) capacity weight work
        currentTime (eventTime - currentTime) ++
      M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps start horizon omega
        capacity weight eventTime
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
          (eventTime - currentTime)).workload times := by
  simp [admittedWorkFiniteGPSBatchTraceSegmentJobSteps, hbatchApplied]

/-- If the bounded gap does not reach its scheduled source epoch, the
annotated ledger records only that actual partial gap and fabricates neither
later segments nor later source jobs. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime eventTime : ℝ) (times : List ℝ)
    (hbatchNotApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        (eventTime - currentTime)).batchApplied ≠ true) :
    M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
      start horizon omega capacity weight currentTime work (eventTime :: times) =
      M.admittedWorkFiniteGPSGapSegmentJobSteps start horizon omega eventTime
        ((finiteGPSActiveClasses work).card + 1) capacity weight work
        currentTime (eventTime - currentTime) := by
  simp [admittedWorkFiniteGPSBatchTraceSegmentJobSteps, hbatchNotApplied]

/-- Forgetting endpoint-job metadata from the complete annotated source trace
returns exactly the generic pre-terminal segment ledger. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_segments
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ) :
    (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
      start horizon omega capacity weight currentTime work times).map
        (fun step => step.segment) =
      finiteGPSRunBatchTraceSegments capacity weight
        (M.admittedWorkBatchAt start horizon omega) currentTime work times := by
  induction times generalizing currentTime work with
  | nil =>
      simp [admittedWorkFiniteGPSBatchTraceSegmentJobSteps,
        finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatchApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon omega capacity weight work currentTime eventTime times hbatchApplied,
          finiteGPSRunBatchTraceSegments_cons_of_batchApplied
            capacity weight (M.admittedWorkBatchAt start horizon omega)
            currentTime work eventTime times hbatchApplied]
        simp only [List.map_append]
        rw [M.admittedWorkFiniteGPSGapSegmentJobSteps_segments]
        rw [ih
          (currentTime := eventTime)
          (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).workload)]
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon omega capacity weight work currentTime eventTime times hbatchNotApplied,
          finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
            capacity weight (M.admittedWorkBatchAt start horizon omega)
            currentTime work eventTime times hbatchNotApplied]
        exact M.admittedWorkFiniteGPSGapSegmentJobSteps_segments
          start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)

/-- Reading the final endpoint workload after concatenated FCFS steps is the
same as first reading the left endpoint and then continuing through the
right-hand steps. -/
theorem admittedWorkFiniteGPSFCFSSegmentStepsEndpointWorkload_append
    (initialWorkload : Category → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (SLA2026FiniteGPSJobId Category))) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload (left ++ right) =
      finiteGPSFCFSSegmentStepsEndpointWorkload
        (finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload left) right := by
  induction left generalizing initialWorkload with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload]
  | cons step left ih =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload, ih]

/-- The endpoint workload computed from the annotated source batch steps is
exactly the workload returned by the bounded GPS batch runner, even in the
explicit partial-gap branch. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_endpointWorkload_eq_runner
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ) :
    finiteGPSFCFSSegmentStepsEndpointWorkload work
      (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
        start horizon omega capacity weight currentTime work times) =
      (finiteGPSRunBatchTrace capacity weight
        (M.admittedWorkBatchAt start horizon omega) currentTime work times).workload := by
  induction times generalizing currentTime work with
  | nil =>
      simp [admittedWorkFiniteGPSBatchTraceSegmentJobSteps,
        finiteGPSRunBatchTrace, finiteGPSFCFSSegmentStepsEndpointWorkload]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatchApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon omega capacity weight work currentTime eventTime times hbatchApplied,
          finiteGPSRunBatchTrace_cons_of_batchApplied
            capacity weight (M.admittedWorkBatchAt start horizon omega)
            currentTime work eventTime times hbatchApplied,
          admittedWorkFiniteGPSFCFSSegmentStepsEndpointWorkload_append,
          M.admittedWorkFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner,
          ih]
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon omega capacity weight work currentTime eventTime times hbatchNotApplied,
          finiteGPSRunBatchTrace_cons_of_not_batchApplied
            capacity weight (M.admittedWorkBatchAt start horizon omega)
            currentTime work eventTime times hbatchNotApplied]
        exact M.admittedWorkFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner
          start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)

/-- Every source-labelled step in the annotated batch trace is aggregate
compatible with the exact concrete GPS segment that it retains. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ) :
    ∀ step ∈ M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
      start horizon omega capacity weight currentTime work times,
      step.endpointJobs.AggregateCompatible step.segment := by
  induction times generalizing currentTime work with
  | nil =>
      simp [admittedWorkFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatchApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon omega capacity weight work currentTime eventTime times hbatchApplied]
        intro step hstep
        rcases List.mem_append.mp hstep with hgap | htail
        · exact M.admittedWorkFiniteGPSGapSegmentJobSteps_aggregateCompatible
            start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
            capacity weight work currentTime (eventTime - currentTime) step hgap
        · exact ih
            (currentTime := eventTime)
            (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).workload)
            step htail
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon omega capacity weight work currentTime eventTime times hbatchNotApplied]
        exact M.admittedWorkFiniteGPSGapSegmentJobSteps_aggregateCompatible
          start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)

/-- The complete annotated finite source batch trace is a compatible FCFS
execution.  Its initial ledger is caller-supplied only as a representation of
the explicit input workload; all later queue transitions are computed from
the concrete GPS segments and identified source endpoint jobs. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_compatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j,
      0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
        start horizon omega capacity weight currentTime work times) := by
  induction times generalizing currentTime work initial with
  | nil =>
      simpa [admittedWorkFiniteGPSBatchTraceSegmentJobSteps] using
        hinitial_matches_work
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j,
          0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 ≤ M.admittedWorkBatchAt start horizon omega laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      have hgap_terminates :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).batchApplied = true := by
        exact (finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)).1
      let gapSteps := M.admittedWorkFiniteGPSGapSegmentJobSteps
        start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
        capacity weight work currentTime (eventTime - currentTime)
      have hgap_compatible :
          FiniteGPSFCFSRunSegmentStepsCompatible initial work gapSteps := by
        exact M.admittedWorkFiniteGPSGapSegmentJobSteps_compatible
          start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime) initial
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hsource_work_nonneg (sub_nonneg.mpr hdelay) hinitial_nonneg
          hinitial_matches_work
      have hgap_fold_nonneg :
          (finiteGPSFCFSRunSegmentSteps initial gapSteps).Nonnegative :=
        admittedWorkFiniteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
          initial work gapSteps hinitial_nonneg hgap_compatible
      have hgap_endpoint :
          finiteGPSFCFSSegmentStepsEndpointWorkload work gapSteps =
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).workload := by
        simpa [gapSteps] using
          (M.admittedWorkFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner
            start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
            capacity weight work currentTime (eventTime - currentTime))
      have hgap_fold_matches : ∀ i,
          (finiteGPSFCFSRunSegmentSteps initial gapSteps).classWork i =
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).workload i := by
        intro i
        calc
          (finiteGPSFCFSRunSegmentSteps initial gapSteps).classWork i =
              finiteGPSFCFSSegmentStepsEndpointWorkload work gapSteps i :=
            finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
              initial work gapSteps hinitial_nonneg hgap_compatible i
          _ = (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
              (eventTime - currentTime)).workload i := by
            rw [hgap_endpoint]
      have hgap_work_nonneg : ∀ j, 0 ≤
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (M.admittedWorkBatchAt start horizon omega eventTime)
          (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih
        (currentTime := eventTime)
        (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
          (eventTime - currentTime)).workload)
        (initial := finiteGPSFCFSRunSegmentSteps initial gapSteps)
        hgap_work_nonneg hchronological_tail hbatch_tail hgap_fold_nonneg
        hgap_fold_matches
      have htail_from_gap_endpoint :
          FiniteGPSFCFSRunSegmentStepsCompatible
            (finiteGPSFCFSRunSegmentSteps initial gapSteps)
            (finiteGPSFCFSSegmentStepsEndpointWorkload work gapSteps)
            (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
              start horizon omega capacity weight eventTime
              (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
                (eventTime - currentTime)).workload times) := by
        rw [hgap_endpoint]
        exact htail
      have happend := admittedWorkFiniteGPSFCFSRunSegmentStepsCompatible_append
        initial work gapSteps
        (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
          start horizon omega capacity weight eventTime
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).workload times)
        hgap_compatible htail_from_gap_endpoint
      rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon omega capacity weight work currentTime eventTime times hgap_terminates]
      simpa [gapSteps] using happend

/-- Under the ordinary finite GPS hypotheses, every scheduled source batch is
reached and the external endpoint-job batches in the actual annotated segment
sequence are exactly the chronological source-batch ledger. -/
theorem admittedWorkFiniteGPSBatchTraceSegmentJobSteps_externalEndpointJobBatches_eq_sourceBatchTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j,
      0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j) :
    admittedWorkFiniteGPSExternalEndpointJobBatches
      (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
        start horizon omega capacity weight currentTime work times) =
      times.map (fun eventTime => M.admittedWorkFCFSJobsAt start horizon omega eventTime) := by
  induction times generalizing currentTime work with
  | nil =>
      simp [admittedWorkFiniteGPSExternalEndpointJobBatches,
        admittedWorkFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j,
          0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 ≤ M.admittedWorkBatchAt start horizon omega laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      have hgap_terminates :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).batchApplied = true ∧
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).remainingDelay = 0 := by
        exact finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)
      have hgap_nonneg : ∀ j, 0 ≤
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
            (eventTime - currentTime)).workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (M.admittedWorkBatchAt start horizon omega eventTime)
          (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih
        (currentTime := eventTime)
        (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
          (eventTime - currentTime)).workload)
        hgap_nonneg hchronological_tail hbatch_tail
      rw [M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon omega capacity weight work currentTime eventTime times hgap_terminates.1]
      unfold admittedWorkFiniteGPSExternalEndpointJobBatches
      rw [List.filterMap_append]
      change admittedWorkFiniteGPSExternalEndpointJobBatches
          (M.admittedWorkFiniteGPSGapSegmentJobSteps start horizon omega eventTime
            ((finiteGPSActiveClasses work).card + 1) capacity weight work
            currentTime (eventTime - currentTime)) ++
          admittedWorkFiniteGPSExternalEndpointJobBatches
            (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps
              start horizon omega capacity weight eventTime
              (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (M.admittedWorkBatchAt start horizon omega eventTime)
                (eventTime - currentTime)).workload times) =
        (eventTime :: times).map
          (fun laterTime => M.admittedWorkFCFSJobsAt start horizon omega laterTime)
      rw [M.admittedWorkFiniteGPSGapSegmentJobSteps_externalEndpointJobBatches_eq_singleton_of_batchApplied
          start horizon omega eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)
          hgap_terminates.1,
        htail]
      rfl

/-- The concrete segment ledger of the finite source batch trace before the
zero-work horizon fence is appended. -/
def admittedWorkFiniteGPSPreTerminalHistory
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) : FiniteGPSBatchSegmentHistory Category :=
  finiteGPSRunExternalBatchTraceWithSegments capacity weight
    (M.admittedWorkBatchAt start horizon omega) start initialWork
    (M.admittedWorkExternalBatchTrace start horizon omega)

/-- The source segment history has exactly the same pre-terminal runner
result as the existing direct-source batch execution. -/
theorem admittedWorkFiniteGPSPreTerminalHistory_final
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    (M.admittedWorkFiniteGPSPreTerminalHistory start horizon omega capacity weight initialWork).final =
      M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork := rfl

/-- The pre-terminal source segment ledger records exactly the service field
of its concrete batch runner. -/
theorem admittedWorkFiniteGPSPreTerminalHistory_segments_service_eq_final
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) (k : Category) :
    finiteGPSExecutionSegmentsService
      (M.admittedWorkFiniteGPSPreTerminalHistory
        start horizon omega capacity weight initialWork).segments k =
      (M.admittedWorkFiniteGPSPreTerminalHistory
        start horizon omega capacity weight initialWork).final.service k := by
  exact finiteGPSRunBatchTraceWithSegments_service capacity weight initialWork
    (M.admittedWorkBatchAt start horizon omega) start
    (M.admittedWorkExternalBatchTrace start horizon omega).times k

/-- The full concrete segment history appends the generic zero-work horizon
fence to the source history.  It is the segment-level counterpart of
`admittedWorkFiniteGPSRun`; the fence is not a source batch. -/
def admittedWorkFiniteGPSRunWithSegments
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (_hstart_le_horizon : start ≤ horizon) : FiniteGPSBatchSegmentHistory Category :=
  finiteGPSCloseAtHorizonWithSegments capacity weight
    (M.admittedWorkFiniteGPSPreTerminalHistory
      start horizon omega capacity weight initialWork) horizon

/-- Closing the source segment history has precisely the existing full finite
GPS execution as its final runner result. -/
theorem admittedWorkFiniteGPSRunWithSegments_final
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    (M.admittedWorkFiniteGPSRunWithSegments
      start horizon omega capacity weight initialWork hstart_le_horizon).final =
      M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
        hstart_le_horizon := rfl

/-- The complete segment history's service increments telescope to its final
source-run service ledger, including the zero-work terminal fence. -/
theorem admittedWorkFiniteGPSRunWithSegments_segments_service_eq_final
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) (k : Category) :
    finiteGPSExecutionSegmentsService
      (M.admittedWorkFiniteGPSRunWithSegments
        start horizon omega capacity weight initialWork hstart_le_horizon).segments k =
      (M.admittedWorkFiniteGPSRunWithSegments
        start horizon omega capacity weight initialWork hstart_le_horizon).final.service k := by
  apply finiteGPSCloseAtHorizonWithSegments_segments_service_eq_final
  intro j
  exact M.admittedWorkFiniteGPSPreTerminalHistory_segments_service_eq_final
    start horizon omega capacity weight initialWork j

/-- Attach the empty computational endpoint-job batch to every segment in the
generic terminal zero-work fence history.  This list is deliberately a suffix
ledger only: source batches remain represented by
`admittedWorkFCFSSourceEndpointBatchTrace`. -/
def admittedWorkFiniteGPSHorizonFenceFCFSSteps
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category)) :=
  (finiteGPSHorizonFenceSegments capacity weight
    (M.admittedWorkFiniteGPSPreTerminalHistory
      start horizon omega capacity weight initialWork).final horizon).map fun segment =>
    { segment := segment
      endpointJobs := admittedWorkFCFSComputationalEndpointJobs }

/-- Every terminal-fence step carries the same explicitly empty endpoint-job
batch. -/
theorem admittedWorkFiniteGPSHorizonFenceFCFSSteps_endpointJobs
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category))
    (hstep : step ∈ M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
      start horizon omega capacity weight initialWork) :
    step.endpointJobs = admittedWorkFCFSComputationalEndpointJobs := by
  unfold admittedWorkFiniteGPSHorizonFenceFCFSSteps at hstep
  rcases List.mem_map.mp hstep with ⟨segment, _hsegment, rfl⟩
  rfl

/-- Every terminal-fence endpoint-job batch has zero work in every category. -/
theorem admittedWorkFiniteGPSHorizonFenceFCFSSteps_classWork_zero
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category))
    (hstep : step ∈ M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
      start horizon omega capacity weight initialWork) (k : Category) :
    step.endpointJobs.classWork k = 0 := by
  rw [M.admittedWorkFiniteGPSHorizonFenceFCFSSteps_endpointJobs
    start horizon omega capacity weight initialWork step hstep]
  exact admittedWorkFCFSComputationalEndpointJobs_classWork k

/-- The empty job batches attached to terminal-fence segments are exactly
compatible with the generic fence's proved-zero aggregate endpoint work. -/
theorem admittedWorkFiniteGPSHorizonFenceFCFSSteps_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category))
    (hstep : step ∈ M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
      start horizon omega capacity weight initialWork) :
    step.endpointJobs.AggregateCompatible step.segment := by
  unfold admittedWorkFiniteGPSHorizonFenceFCFSSteps at hstep
  rcases List.mem_map.mp hstep with ⟨segment, hsegment, rfl⟩
  intro k
  rw [admittedWorkFCFSComputationalEndpointJobs_classWork]
  exact (finiteGPSHorizonFenceSegments_forall_endpointBatch_eq_zero
    capacity weight
    (M.admittedWorkFiniteGPSPreTerminalHistory
      start horizon omega capacity weight initialWork).final horizon
    segment hsegment k).symm

/-- No source job is inserted by any terminal-fence endpoint. -/
theorem admittedWorkFCFSJob_not_mem_horizonFenceFCFSStep
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) (k : Category) (n : ℕ)
    (step : FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category))
    (hstep : step ∈ M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
      start horizon omega capacity weight initialWork) :
    M.admittedWorkFCFSJob omega k n ∉ step.endpointJobs.jobs k := by
  rw [M.admittedWorkFiniteGPSHorizonFenceFCFSSteps_endpointJobs
    start horizon omega capacity weight initialWork step hstep]
  exact M.admittedWorkFCFSJob_not_mem_computationalEndpointJobs omega k n

/-- The concrete pre-terminal FCFS step ledger follows the direct admitted
source trace in exactly the same recursion as the generic segment history. -/
def admittedWorkFiniteGPSPreTerminalFCFSSteps
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category)) :=
  M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps start horizon omega capacity weight
    start initialWork (M.admittedWorkExternalBatchTrace start horizon omega).times

/-- Erasing the endpoint-job data from the pre-terminal FCFS step ledger
recovers exactly the segments stored in the existing source history. -/
theorem admittedWorkFiniteGPSPreTerminalFCFSSteps_segments
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
      start horizon omega capacity weight initialWork).map (fun step => step.segment) =
      (M.admittedWorkFiniteGPSPreTerminalHistory
        start horizon omega capacity weight initialWork).segments := by
  simpa [admittedWorkFiniteGPSPreTerminalFCFSSteps,
    admittedWorkFiniteGPSPreTerminalHistory,
    finiteGPSRunExternalBatchTraceWithSegments] using
    (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_segments
      start horizon omega capacity weight initialWork start
      (M.admittedWorkExternalBatchTrace start horizon omega).times)

/-- Every pre-terminal FCFS step is aggregate-compatible with the concrete
segment it retains. -/
theorem admittedWorkFiniteGPSPreTerminalFCFSSteps_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    ∀ step ∈ M.admittedWorkFiniteGPSPreTerminalFCFSSteps
      start horizon omega capacity weight initialWork,
      step.endpointJobs.AggregateCompatible step.segment := by
  simpa [admittedWorkFiniteGPSPreTerminalFCFSSteps] using
    (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_aggregateCompatible
      start horizon omega capacity weight initialWork start
      (M.admittedWorkExternalBatchTrace start horizon omega).times)

/-- For the actual direct admitted-work source, the external job batches in
the pre-terminal FCFS segment sequence are exactly the chronological finite
source batch trace.  Thus no source batch is dropped or duplicated before the
computational horizon fence is appended. -/
theorem admittedWorkFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hwork_nonneg : ∀ j n, 0 ≤ M.admittedWorkRequirement j n omega) :
    admittedWorkFiniteGPSExternalEndpointJobBatches
      (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
        start horizon omega capacity weight initialWork) =
      (M.admittedWorkExternalBatchTrace start horizon omega).times.map
        (fun eventTime => M.admittedWorkFCFSJobsAt start horizon omega eventTime) := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (M.admittedWorkExternalBatchTrace start horizon omega).times,
        ∀ j, 0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j := by
    intro eventTime _ j
    exact M.admittedWorkBatchAt_nonneg start horizon omega hwork_nonneg eventTime j
  simpa [admittedWorkFiniteGPSPreTerminalFCFSSteps] using
    (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_externalEndpointJobBatches_eq_sourceBatchTrace
      start horizon omega capacity weight initialWork start
      (M.admittedWorkExternalBatchTrace start horizon omega).times
      hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
      (M.admittedWorkExternalBatchTrace start horizon omega).chronological
      hbatch_nonneg)

/-- The direct source's annotated pre-terminal segment steps satisfy the
generic FCFS fold compatibility invariant under the ordinary finite GPS and
nonnegative-mark hypotheses. -/
theorem admittedWorkFiniteGPSPreTerminalFCFSSteps_compatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_work_nonneg : ∀ i, 0 ≤ initialWork i)
    (hsource_work_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = initialWork i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial initialWork
      (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
        start horizon omega capacity weight initialWork) := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (M.admittedWorkExternalBatchTrace start horizon omega).times,
        ∀ j, 0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j := by
    intro eventTime _ j
    exact M.admittedWorkBatchAt_nonneg start horizon omega hsource_work_nonneg eventTime j
  simpa [admittedWorkFiniteGPSPreTerminalFCFSSteps] using
    (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_compatible
      start horizon omega capacity weight initialWork start
      (M.admittedWorkExternalBatchTrace start horizon omega).times initial
      hcapacity hweight_pos htotal_weight_le_one
      hinitial_work_nonneg hsource_work_nonneg
      (M.admittedWorkExternalBatchTrace start horizon omega).chronological
      hbatch_nonneg hinitial_nonneg hinitial_matches_work)

/-- The endpoint workload computed by the annotated pre-terminal FCFS step
ledger is exactly the final workload of the direct-source GPS history. -/
theorem admittedWorkFiniteGPSPreTerminalFCFSSteps_endpointWorkload_eq_history
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWork
      (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
        start horizon omega capacity weight initialWork) =
      (M.admittedWorkFiniteGPSPreTerminalHistory
        start horizon omega capacity weight initialWork).final.workload := by
  simpa [admittedWorkFiniteGPSPreTerminalFCFSSteps,
    admittedWorkFiniteGPSPreTerminalHistory,
    finiteGPSRunExternalBatchTraceWithSegments] using
    (M.admittedWorkFiniteGPSBatchTraceSegmentJobSteps_endpointWorkload_eq_runner
      start horizon omega capacity weight initialWork start
      (M.admittedWorkExternalBatchTrace start horizon omega).times)

/-- Folding the explicit FCFS source jobs over the concrete pre-terminal GPS
segments yields a residual-job ledger whose aggregate workload is exactly the
pre-terminal GPS endpoint workload. -/
theorem admittedWorkFiniteGPSPreTerminalFCFSSteps_fold_classWork_eq_history
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (SLA2026FiniteGPSJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_work_nonneg : ∀ i, 0 ≤ initialWork i)
    (hsource_work_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = initialWork i)
    (i : Category) :
    (finiteGPSFCFSRunSegmentSteps initial
      (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
        start horizon omega capacity weight initialWork)).classWork i =
      (M.admittedWorkFiniteGPSPreTerminalHistory
        start horizon omega capacity weight initialWork).final.workload i := by
  calc
    (finiteGPSFCFSRunSegmentSteps initial
      (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
        start horizon omega capacity weight initialWork)).classWork i =
        finiteGPSFCFSSegmentStepsEndpointWorkload initialWork
          (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
            start horizon omega capacity weight initialWork) i :=
      finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
        initial initialWork
        (M.admittedWorkFiniteGPSPreTerminalFCFSSteps
          start horizon omega capacity weight initialWork)
        hinitial_nonneg
        (M.admittedWorkFiniteGPSPreTerminalFCFSSteps_compatible
          start horizon omega capacity weight initialWork initial
          hcapacity hweight_pos htotal_weight_le_one hinitial_work_nonneg hsource_work_nonneg
          hinitial_nonneg hinitial_matches_work) i
    _ = (M.admittedWorkFiniteGPSPreTerminalHistory
        start horizon omega capacity weight initialWork).final.workload i := by
      rw [M.admittedWorkFiniteGPSPreTerminalFCFSSteps_endpointWorkload_eq_history
        start horizon omega capacity weight initialWork]

/-- Erasing job data from the terminal-fence FCFS suffix recovers exactly the
generic zero-work fence segment history. -/
theorem admittedWorkFiniteGPSHorizonFenceFCFSSteps_segments
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) :
    (M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
      start horizon omega capacity weight initialWork).map (fun step => step.segment) =
      finiteGPSHorizonFenceSegments capacity weight
        (M.admittedWorkFiniteGPSPreTerminalHistory
          start horizon omega capacity weight initialWork).final horizon := by
  simp [admittedWorkFiniteGPSHorizonFenceFCFSSteps, Function.comp_def]

/-- The full FCFS segment ledger is the source-labelled pre-terminal ledger
followed by the explicitly empty computational horizon-fence suffix. -/
def admittedWorkFiniteGPSRunFCFSSteps
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (_hstart_le_horizon : start ≤ horizon) :
    List (FiniteGPSFCFSSegmentJobStep Category (SLA2026FiniteGPSJobId Category)) :=
  M.admittedWorkFiniteGPSPreTerminalFCFSSteps
    start horizon omega capacity weight initialWork ++
    M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
      start horizon omega capacity weight initialWork

/-- Forgetting all FCFS job data from the full finite ledger returns exactly
the source runner's concrete closed segment history. -/
theorem admittedWorkFiniteGPSRunFCFSSteps_segments
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    (M.admittedWorkFiniteGPSRunFCFSSteps
      start horizon omega capacity weight initialWork hstart_le_horizon).map
        (fun step => step.segment) =
      (M.admittedWorkFiniteGPSRunWithSegments
        start horizon omega capacity weight initialWork hstart_le_horizon).segments := by
  unfold admittedWorkFiniteGPSRunFCFSSteps admittedWorkFiniteGPSRunWithSegments
    finiteGPSCloseAtHorizonWithSegments
  simp only [List.map_append]
  rw [M.admittedWorkFiniteGPSPreTerminalFCFSSteps_segments,
    M.admittedWorkFiniteGPSHorizonFenceFCFSSteps_segments]

/-- Every step of the complete finite FCFS ledger has endpoint jobs whose
aggregate is exactly the batch work stored by that concrete GPS segment. -/
theorem admittedWorkFiniteGPSRunFCFSSteps_aggregateCompatible
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    ∀ step ∈ M.admittedWorkFiniteGPSRunFCFSSteps
      start horizon omega capacity weight initialWork hstart_le_horizon,
      step.endpointJobs.AggregateCompatible step.segment := by
  unfold admittedWorkFiniteGPSRunFCFSSteps
  intro step hstep
  rcases List.mem_append.mp hstep with hpre | hfence
  · exact M.admittedWorkFiniteGPSPreTerminalFCFSSteps_aggregateCompatible
      start horizon omega capacity weight initialWork step hpre
  · exact M.admittedWorkFiniteGPSHorizonFenceFCFSSteps_aggregateCompatible
      start horizon omega capacity weight initialWork step hfence

/-- The finite composite boundary keeps the two kinds of events distinct:
each actual source request occurs exactly once in its timed source batch, and
it occurs in no endpoint batch of the computational horizon fence. -/
theorem admittedWorkFCFSJob_source_once_and_absent_from_horizonFence
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) (k : Category) (n : ℕ)
    (hn : n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k) :
    (∃! batch : SLA2026FiniteGPSTimedEndpointJobs Category,
      batch ∈ M.admittedWorkFCFSSourceEndpointBatchTrace start horizon omega ∧
        M.admittedWorkFCFSJob omega k n ∈ batch.endpointJobs.jobs k) ∧
      ∀ step ∈ M.admittedWorkFiniteGPSHorizonFenceFCFSSteps
        start horizon omega capacity weight initialWork,
        M.admittedWorkFCFSJob omega k n ∉ step.endpointJobs.jobs k := by
  constructor
  · exact M.admittedWorkFCFSJob_appears_once_in_sourceEndpointBatchTrace
      start horizon omega k n hn
  · intro step hstep
    exact M.admittedWorkFCFSJob_not_mem_horizonFenceFCFSStep
      start horizon omega capacity weight initialWork k n step hstep

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
