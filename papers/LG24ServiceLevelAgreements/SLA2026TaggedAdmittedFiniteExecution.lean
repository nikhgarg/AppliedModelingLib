import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import LG24ServiceLevelAgreements.SLA2026StationaryAdmittedPalmInputs
import Mathlib.Tactic

/-!
# Finite GPS execution from a tagged direct-admitted SLA input

This module turns one genuine target/passive direct-admitted Palm input into
a finite source ledger and runs its collapsed exact-time batches through the
existing finite GPS runner.  The target category is enumerated by its
Palm-tagged gap path; every passive category is enumerated by its literal
stationary suspension path after the target event's physical-time recentering.

It is a finite path construction only.  It does not construct a stationary
GPS workload, a regenerative process, a response-time random variable, or a
tail bound.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- An actual direct-admitted source identifier: a category together with its
integer arrival label.  In particular, the selected Palm request has the real
identifier `(target, 0)`, rather than a synthetic scheduler-generated ID. -/
abbrev TaggedAdmittedSourceJobId (Category : Type*) := Category × Int

/-- The physical epoch of one source identifier in the target/passive tagged
input.  The target uses the Palm candidate-arrival path; a passive class uses
its already recentered literal stationary suspension. -/
def taggedAdmittedSourceArrival
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (job : TaggedAdmittedSourceJobId Category) : ℝ :=
  if htarget : job.1 = target then
    candidatePalmArrival z.1.1 job.2
  else
    suspensionBaseArrival (z.2 ⟨job.1, htarget⟩).1 job.2

/-- The exact source work mark attached to one target/passive source
identifier.  Both branches retain the complete direct-admitted work paths
from the Palm input. -/
def taggedAdmittedSourceWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (job : TaggedAdmittedSourceJobId Category) : ℝ :=
  if htarget : job.1 = target then
    z.1.2 job.2
  else
    (z.2 ⟨job.1, htarget⟩).2 job.2

/-- The finite direct-admitted ledger for one category on `[start, horizon)`.
The target branch uses the Palm finite enumerator; passive branches use the
literal stationary base enumerator. -/
def taggedAdmittedArrivalIndicesBetween
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (k : Category) :
    Finset ℤ :=
  if htarget : k = target then
    palmTaggedArrivalIndices start horizon z.1.1
  else
    suspensionBaseArrivalIndices start horizon (z.2 ⟨k, htarget⟩).1

omit [Fintype Category] in
/-- Exact interval semantics for every target/passive source ledger.  The
target good-carrier hypothesis is needed only for the raw Palm gap-path
enumerator; passive states are already literal good suspension states. -/
theorem mem_taggedAdmittedArrivalIndicesBetween_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (k : Category) (n : ℤ) :
    n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k ↔
      start ≤ taggedAdmittedSourceArrival target z (k, n) ∧
        taggedAdmittedSourceArrival target z (k, n) < horizon := by
  by_cases htarget : k = target
  · subst k
    simpa [taggedAdmittedArrivalIndicesBetween, taggedAdmittedSourceArrival] using
      (mem_palmTaggedArrivalIndices_iff start horizon z.1.1 htarget_good.1 n)
  · simpa [taggedAdmittedArrivalIndicesBetween, taggedAdmittedSourceArrival,
      htarget] using
      (mem_suspensionBaseArrivalIndices_iff start horizon
        (z.2 ⟨k, htarget⟩).1 n)

/-- All actual target/passive source identifiers in the finite interval. -/
def taggedAdmittedSourceJobLedger
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    Finset (TaggedAdmittedSourceJobId Category) :=
  (Finset.univ : Finset Category).biUnion fun k =>
    (taggedAdmittedArrivalIndicesBetween start horizon target z k).image fun n => (k, n)

/-- A source identifier belongs to the combined ledger exactly when its raw
integer label belongs to its own target or passive category ledger. -/
theorem mem_taggedAdmittedSourceJobLedger_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (k : Category) (n : ℤ) :
    (k, n) ∈ taggedAdmittedSourceJobLedger start horizon target z ↔
      n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k := by
  constructor
  · intro hmem
    rcases Finset.mem_biUnion.mp hmem with ⟨j, _hj, himage⟩
    rcases Finset.mem_image.mp himage with ⟨m, hm, hpair⟩
    cases hpair
    exact hm
  · intro hmem
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hmem, rfl⟩

/-- Exact `[start, horizon)` semantics for every combined source identifier. -/
theorem mem_taggedAdmittedSourceJobLedger_interval_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (job : TaggedAdmittedSourceJobId Category) :
    job ∈ taggedAdmittedSourceJobLedger start horizon target z ↔
      start ≤ taggedAdmittedSourceArrival target z job ∧
        taggedAdmittedSourceArrival target z job < horizon := by
  rw [mem_taggedAdmittedSourceJobLedger_iff]
  simpa using
    (mem_taggedAdmittedArrivalIndicesBetween_iff start horizon target z
      htarget_good job.1 job.2)

omit [Fintype Category] in
/-- The selected Palm request's real source ID has epoch zero. -/
@[simp]
theorem taggedAdmittedSourceArrival_target_zero
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    taggedAdmittedSourceArrival target z (target, 0) = 0 := by
  simp [taggedAdmittedSourceArrival, candidatePalmArrival_zero]

omit [Fintype Category] in
/-- The selected Palm request's source work is exactly the tagged index-zero
work mark retained by the direct admitted target path. -/
@[simp]
theorem taggedAdmittedSourceWork_target_zero
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    taggedAdmittedSourceWork target z (target, 0) = z.1.2 0 := by
  simp [taggedAdmittedSourceWork]

/-- The real target source ID occurs in the finite source ledger exactly when
the chosen interval contains the Palm epoch zero. -/
theorem mem_taggedAdmittedTargetSourceId_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) :
    (target, 0) ∈ taggedAdmittedSourceJobLedger start horizon target z ↔
      start ≤ 0 ∧ 0 < horizon := by
  simpa using
    (mem_taggedAdmittedSourceJobLedger_interval_iff start horizon target z
      htarget_good (target, 0))

/-- If `[start, horizon)` contains zero, the tagged job is present as the
actual `(target, 0)` source record. -/
theorem mem_taggedAdmittedTargetSourceId
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    (target, 0) ∈ taggedAdmittedSourceJobLedger start horizon target z :=
  (mem_taggedAdmittedTargetSourceId_iff start horizon target z htarget_good).mpr
    ⟨hstart, hhorizon⟩

/-- All distinct physical source epochs in the finite target/passive ledger.
`Finset.image` collapses deterministic simultaneous arrivals into one exact
GPS batch time. -/
def taggedAdmittedBatchTimes
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : Finset ℝ :=
  (taggedAdmittedSourceJobLedger start horizon target z).image
    (taggedAdmittedSourceArrival target z)

/-- The exact source work vector arriving at one physical batch epoch. -/
def taggedAdmittedBatchAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) : Category → ℝ :=
  fun k => ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k with
    taggedAdmittedSourceArrival target z (k, n) = eventTime,
    taggedAdmittedSourceWork target z (k, n)

/-- The chronological duplicate-free trace of actual external source batches. -/
def taggedAdmittedBatchTimeTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : List ℝ :=
  (taggedAdmittedBatchTimes start horizon target z).sort (fun s t : ℝ => s ≤ t)

/-- A finite batch time comes from an actual category/index source record. -/
theorem mem_taggedAdmittedBatchTimes_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ) :
    eventTime ∈ taggedAdmittedBatchTimes start horizon target z ↔
      ∃ job : TaggedAdmittedSourceJobId Category,
        job ∈ taggedAdmittedSourceJobLedger start horizon target z ∧
          taggedAdmittedSourceArrival target z job = eventTime := by
  constructor
  · rintro htime
    rcases Finset.mem_image.mp htime with ⟨job, hjob, harrival⟩
    exact ⟨job, hjob, harrival⟩
  · rintro ⟨job, hjob, harrival⟩
    exact Finset.mem_image.mpr ⟨job, hjob, harrival⟩

/-- The source-derived tagged trace is a valid finite GPS external batch
trace.  Its construction needs only the target Palm good carrier, which gives
the target interval enumeration its exact finite semantics. -/
def taggedAdmittedExternalBatchTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) :
    FiniteGPSExternalBatchTrace start where
  times := taggedAdmittedBatchTimeTrace start horizon target z
  chronological :=
    finiteGPSChronologicalFrom_of_pairwise_le start
      (taggedAdmittedBatchTimeTrace start horizon target z)
      (by
        intro t ht
        have htime : t ∈ taggedAdmittedBatchTimes start horizon target z :=
          (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp ht
        rcases (mem_taggedAdmittedBatchTimes_iff start horizon target z t).mp htime with
          ⟨job, hjob, harrival⟩
        rw [← harrival]
        exact (mem_taggedAdmittedSourceJobLedger_interval_iff start horizon target z
          htarget_good job).mp hjob |>.1)
      (Finset.pairwise_sort (taggedAdmittedBatchTimes start horizon target z)
        (fun s t : ℝ => s ≤ t))
  nodup := Finset.sort_nodup (taggedAdmittedBatchTimes start horizon target z)
    (fun s t : ℝ => s ≤ t)

/-- Every actual tagged source batch lies strictly before the chosen horizon. -/
theorem taggedAdmittedExternalBatchTrace_time_lt_horizon
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (eventTime : ℝ)
    (heventTime : eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times) :
    eventTime < horizon := by
  have htime : eventTime ∈ taggedAdmittedBatchTimes start horizon target z :=
    (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp heventTime
  rcases (mem_taggedAdmittedBatchTimes_iff start horizon target z eventTime).mp htime with
    ⟨job, hjob, harrival⟩
  rw [← harrival]
  exact (mem_taggedAdmittedSourceJobLedger_interval_iff start horizon target z
    htarget_good job).mp hjob |>.2

/-- A pathwise nonnegativity condition for all retained target and passive
source work paths.  The finite executor keeps this explicit rather than
silently treating a probabilistic a.e. fact as a deterministic scheduler
precondition. -/
def TaggedAdmittedSourceWorkNonnegative
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target) : Prop :=
  (∀ n : ℤ, 0 ≤ z.1.2 n) ∧
    ∀ k : PassiveCategory target, ∀ n : ℤ, 0 ≤ (z.2 k).2 n

/-- The strict source-work event needed to turn a zero aggregate workload
into an empty source-labelled FCFS ledger.  It is kept separate from the
weaker executor nonnegativity condition because a zero-work mark would make
that later implication false. -/
def TaggedAdmittedSourceWorkPositive
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target) : Prop :=
  (∀ n : ℤ, 0 < z.1.2 n) ∧
    ∀ k : PassiveCategory target, ∀ n : ℤ, 0 < (z.2 k).2 n

/-- The genuine tagged direct-admitted product law supplies both deterministic
preconditions of the finite tagged executor almost surely: the target Palm
gap path has exact finite-ledger semantics, and every target/passive source
work mark is nonnegative. -/
theorem ae_taggedAdmittedFiniteExecutionInputGood
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      palmTaggedArrivalGoodCarrier z.1.1 ∧
        TaggedAdmittedSourceWorkNonnegative target z := by
  filter_upwards [M.ae_stationaryAdmittedTargetPassivePalmGoodCarrier target,
    M.ae_all_stationaryAdmittedTargetPassivePalmWork_positive target] with
      z hgood hpositive
  exact ⟨hgood, ⟨fun n => (hpositive.1 n).le,
    fun k n => (hpositive.2 k n).le⟩⟩

/-- The same genuine tagged product law supplies strict positivity of every
literal source work mark.  This is a source-input fact, not a condition added
to the finite GPS executor. -/
theorem ae_taggedAdmittedFiniteExecutionInputStrictlyPositive
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      palmTaggedArrivalGoodCarrier z.1.1 ∧
        TaggedAdmittedSourceWorkPositive target z := by
  filter_upwards [M.ae_stationaryAdmittedTargetPassivePalmGoodCarrier target,
    M.ae_all_stationaryAdmittedTargetPassivePalmWork_positive target] with
      z hgood hpositive
  exact ⟨hgood, hpositive⟩

omit [Fintype Category] in
/-- Every actual source-work lookup is nonnegative under the explicit
target/passive source-work condition. -/
theorem taggedAdmittedSourceWork_nonneg
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (job : TaggedAdmittedSourceJobId Category) :
    0 ≤ taggedAdmittedSourceWork target z job := by
  unfold taggedAdmittedSourceWork
  split
  · exact hwork_nonneg.1 _
  · exact hwork_nonneg.2 _ _

omit [Fintype Category] in
/-- Every literal source-work lookup is strictly positive on the explicit
target/passive source-work event. -/
theorem taggedAdmittedSourceWork_pos
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hwork_pos : TaggedAdmittedSourceWorkPositive target z)
    (job : TaggedAdmittedSourceJobId Category) :
    0 < taggedAdmittedSourceWork target z job := by
  unfold taggedAdmittedSourceWork
  split
  · exact hwork_pos.1 _
  · exact hwork_pos.2 _ _

omit [Fintype Category] in
/-- Nonnegative literal source work yields nonnegative aggregate work at
every collapsed exact-time batch. -/
theorem taggedAdmittedBatchAt_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (eventTime : ℝ) (k : Category) :
    0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
  unfold taggedAdmittedBatchAt
  exact Finset.sum_nonneg fun n _ =>
    taggedAdmittedSourceWork_nonneg target z hwork_nonneg (k, n)

/-- Every category/index source record in the local ledger is present in the
combined finite source ledger. -/
theorem taggedAdmittedSourceJob_mem_ledger
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (k : Category) (n : ℤ)
    (hn : n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k) :
    (k, n) ∈ taggedAdmittedSourceJobLedger start horizon target z :=
  (mem_taggedAdmittedSourceJobLedger_iff start horizon target z k n).mpr hn

/-- Summing all collapsed batch fibers preserves the exact total source work
for one category.  Each literal category/index record maps to one physical
batch time, even when other categories share that time. -/
theorem sum_taggedAdmittedBatchAt_eq_totalLedgerWork
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (k : Category) :
    ∑ t ∈ taggedAdmittedBatchTimes start horizon target z,
      taggedAdmittedBatchAt start horizon target z t k =
      ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
        taggedAdmittedSourceWork target z (k, n) := by
  apply Finset.sum_fiberwise_of_maps_to
  · intro n hn
    exact Finset.mem_image.mpr ⟨(k, n),
      taggedAdmittedSourceJob_mem_ledger start horizon target z k n hn, rfl⟩

/-- Sorting the finite set of collapsed batch times preserves finite sums. -/
theorem sum_taggedAdmittedBatchTimeTrace_eq_sum_batchTimes
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (f : ℝ → ℝ) :
    ((taggedAdmittedBatchTimeTrace start horizon target z).map f).sum =
      ∑ t ∈ taggedAdmittedBatchTimes start horizon target z, f t := by
  have hnodup : (taggedAdmittedBatchTimeTrace start horizon target z).Nodup :=
    Finset.sort_nodup (taggedAdmittedBatchTimes start horizon target z)
      (fun s t : ℝ => s ≤ t)
  have htoFinset : (taggedAdmittedBatchTimeTrace start horizon target z).toFinset =
      taggedAdmittedBatchTimes start horizon target z := by
    ext t
    simp [taggedAdmittedBatchTimeTrace]
  calc
    ((taggedAdmittedBatchTimeTrace start horizon target z).map f).sum =
        (taggedAdmittedBatchTimeTrace start horizon target z).toFinset.sum f :=
      (List.sum_toFinset f hnodup).symm
    _ = ∑ t ∈ taggedAdmittedBatchTimes start horizon target z, f t := by
      rw [htoFinset]

/-- The chronological batch trace preserves each category's exact finite
source-work total. -/
theorem sum_taggedAdmittedBatchTimeTrace_batchAt_eq_totalLedgerWork
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (k : Category) :
    ((taggedAdmittedBatchTimeTrace start horizon target z).map
        (fun t => taggedAdmittedBatchAt start horizon target z t k)).sum =
      ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
        taggedAdmittedSourceWork target z (k, n) := by
  calc
    ((taggedAdmittedBatchTimeTrace start horizon target z).map
        (fun t => taggedAdmittedBatchAt start horizon target z t k)).sum =
        ∑ t ∈ taggedAdmittedBatchTimes start horizon target z,
          taggedAdmittedBatchAt start horizon target z t k :=
      sum_taggedAdmittedBatchTimeTrace_eq_sum_batchTimes start horizon target z
        (fun t => taggedAdmittedBatchAt start horizon target z t k)
    _ = ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
        taggedAdmittedSourceWork target z (k, n) :=
      sum_taggedAdmittedBatchAt_eq_totalLedgerWork start horizon target z k

/-- Execute the genuine target/passive direct-admitted source batches through
the finite GPS runner.  This pre-terminal result stops after the last actual
source batch; it makes no claim to have reached `horizon`. -/
def taggedAdmittedFiniteGPSPreTerminalRun
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    FiniteGPSBatchTraceResult Category :=
  finiteGPSRunExternalBatchTrace capacity weight
    (taggedAdmittedBatchAt start horizon target z) start initialWork
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good)

/-- The tagged finite pre-terminal run preserves nonnegative workload from an
arbitrary nonnegative initial workload and explicit nonnegative source work. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (k : Category) :
    0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
      capacity weight initialWork).workload k := by
  unfold taggedAdmittedFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  apply finiteGPSRunBatchTrace_workload_nonneg capacity weight initialWork
    (taggedAdmittedBatchAt start horizon target z) start
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times hinit_nonneg
  intro eventTime heventTime j
  exact taggedAdmittedBatchAt_nonneg start horizon target z hwork_nonneg eventTime j

/-- The finite tagged pre-terminal execution has the exact balance of
arbitrary initial work, actual finite target/passive source work, and stored
GPS service. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_balance
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (k : Category) :
    (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
      capacity weight initialWork).workload k =
      initialWork k +
        ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
          taggedAdmittedSourceWork target z (k, n) -
        (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
          capacity weight initialWork).service k := by
  have hbatch_nonneg :
      ∀ eventTime ∈
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times,
        ∀ j, 0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg start horizon target z hwork_nonneg eventTime j
  have hbalance := finiteGPSRunExternalBatchTrace_balance capacity weight initialWork
    (taggedAdmittedBatchAt start horizon target z) start
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good)
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hbatch_nonneg k
  have hledger :
      ((taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times.map
        fun eventTime => taggedAdmittedBatchAt start horizon target z eventTime k).sum =
        ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
          taggedAdmittedSourceWork target z (k, n) := by
    exact sum_taggedAdmittedBatchTimeTrace_batchAt_eq_totalLedgerWork
      start horizon target z k
  rw [hledger] at hbalance
  simpa [taggedAdmittedFiniteGPSPreTerminalRun] using hbalance

/-- The tagged pre-terminal finite runner never advances beyond `horizon`
when `start ≤ horizon`, because every actual source batch lies in
`[start, horizon)`. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
      capacity weight initialWork).currentTime ≤ horizon := by
  unfold taggedAdmittedFiniteGPSPreTerminalRun
  apply finiteGPSRunExternalBatchTrace_currentTime_le
  · exact hstart_le_horizon
  · intro eventTime heventTime
    exact (taggedAdmittedExternalBatchTrace_time_lt_horizon
      start horizon target z htarget_good eventTime heventTime).le

/-- Close the tagged finite execution through the requested horizon with the
existing computational zero-work fence.  The fence is not a source arrival. -/
def taggedAdmittedFiniteGPSRun
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (_hstart_le_horizon : start ≤ horizon) : FiniteGPSBatchTraceResult Category :=
  finiteGPSCloseAtHorizon capacity weight
    (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
      capacity weight initialWork)
    horizon

/-- Under the explicit finite GPS hypotheses, the computational terminal
fence reaches the requested horizon. -/
theorem taggedAdmittedFiniteGPSRun_currentTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
      hstart_le_horizon).currentTime = horizon := by
  exact finiteGPSCloseAtHorizon_currentTime capacity weight
    (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
      capacity weight initialWork)
    horizon hcapacity hweight_pos htotal_weight_le_one
    (fun j => taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight initialWork
      hinit_nonneg hwork_nonneg j)
    (taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight initialWork hstart_le_horizon)

/-- Closing the tagged finite execution preserves nonnegative workload. -/
theorem taggedAdmittedFiniteGPSRun_workload_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (k : Category) :
    0 ≤ (taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
      hstart_le_horizon).workload k := by
  simpa [taggedAdmittedFiniteGPSRun] using
    (finiteGPSCloseAtHorizon_workload_nonneg capacity weight
      (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork)
      horizon
      (fun j => taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
        start horizon target z htarget_good capacity weight initialWork
        hinit_nonneg hwork_nonneg j) k)

/-- The closed tagged finite run has the exact workload balance.  The terminal
zero-work fence contributes no source work and only adds stored service. -/
theorem taggedAdmittedFiniteGPSRun_balance
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (k : Category) :
    (taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
      hstart_le_horizon).workload k =
      initialWork k +
        ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
          taggedAdmittedSourceWork target z (k, n) -
        (taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
          hstart_le_horizon).service k := by
  have hpre_nonneg : ∀ j,
      0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork).workload j := by
    intro j
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight initialWork
      hinit_nonneg hwork_nonneg j
  have hpre_time :
      (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork).currentTime ≤ horizon :=
    taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight initialWork hstart_le_horizon
  have hpre_balance := taggedAdmittedFiniteGPSPreTerminalRun_balance
    start horizon target z htarget_good capacity weight initialWork hcapacity hweight_pos
    htotal_weight_le_one hinit_nonneg hwork_nonneg k
  have hfinal := finiteGPSCloseAtHorizon_balance capacity weight
    (taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
      capacity weight initialWork)
    horizon hcapacity hweight_pos htotal_weight_le_one hpre_nonneg hpre_time
    (initialWork k)
    (∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k,
      taggedAdmittedSourceWork target z (k, n))
    k hpre_balance
  simpa [taggedAdmittedFiniteGPSRun] using hfinal

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
