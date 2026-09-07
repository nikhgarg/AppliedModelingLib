import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Measurability
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedSourceLedgerMeasurability
import Mathlib.Tactic

/-!
# Tie-aware Borel finite replay scripts for the literal tagged SLA source

The finite tagged GPS input has a random finite source ledger and may contain
simultaneous source arrivals.  This module gives a countable, Borel
stratification by the finite ledger together with all pairwise source-arrival
comparisons on that ledger.  Equality pairs are retained explicitly, so no
no-ties event is assumed.

On every fixed comparison pattern, each fixed equality block has Borel source
work, and a fixed list of source-labelled block representatives gives a Borel
aggregate GPS batch script through the generic finite-runner theorem.  The
remaining work is to derive the actual chronological representative script
and the source-labelled FCFS completion selector from this pattern layer.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A finite tie-aware arrival pattern for one literal source ledger.
`equalPairs` records exact simultaneous arrivals and `earlierPairs` records
strictly earlier arrivals.  Both are finite because the pattern is restricted
to its fixed finite `labels` field. -/
structure TaggedAdmittedSourceArrivalPattern (Category : Type*) where
  labels : Finset (TaggedAdmittedSourceJobId Category)
  equalPairs : Finset (TaggedAdmittedSourceJobId Category ×
    TaggedAdmittedSourceJobId Category)
  earlierPairs : Finset (TaggedAdmittedSourceJobId Category ×
    TaggedAdmittedSourceJobId Category)

/-- A fixed arrival pattern matches an input when it gives the literal source
ledger exactly and records every equality and strict comparison between its
retained source epochs.  This is deliberately a total comparison record:
ties are equality pairs, not excluded cases. -/
def TaggedAdmittedSourceArrivalPattern.Matches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category) : Prop :=
  taggedAdmittedSourceJobLedger start horizon target z = pattern.labels ∧
    ∀ left ∈ pattern.labels, ∀ right ∈ pattern.labels,
      ((left, right) ∈ pattern.equalPairs ↔
        taggedAdmittedSourceArrival target z left =
          taggedAdmittedSourceArrival target z right) ∧
      ((left, right) ∈ pattern.earlierPairs ↔
        taggedAdmittedSourceArrival target z left <
          taggedAdmittedSourceArrival target z right)

/-- The Borel good-carrier fiber of one fixed finite tie-aware pattern. -/
def taggedAdmittedSourceArrivalPatternFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category) :
    Set (TaggedAdmittedSourceGoodCarrier target) :=
  {z | pattern.Matches start horizon target z.1}

private theorem measurableSet_taggedAdmittedSourceArrival_eq_goodCarrier
    (target : Category) (left right : TaggedAdmittedSourceJobId Category) :
    MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      taggedAdmittedSourceArrival target z.1 left =
        taggedAdmittedSourceArrival target z.1 right} := by
  exact measurableSet_eq_fun
    (measurable_taggedAdmittedSourceArrival_goodCarrier target left)
    (measurable_taggedAdmittedSourceArrival_goodCarrier target right)

private theorem measurableSet_taggedAdmittedSourceArrival_lt_goodCarrier
    (target : Category) (left right : TaggedAdmittedSourceJobId Category) :
    MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      taggedAdmittedSourceArrival target z.1 left <
        taggedAdmittedSourceArrival target z.1 right} := by
  exact measurableSet_lt
    (measurable_taggedAdmittedSourceArrival_goodCarrier target left)
    (measurable_taggedAdmittedSourceArrival_goodCarrier target right)

private theorem measurableSet_forall_mem_finset
    {Omega Alpha : Type*} [MeasurableSpace Omega] [DecidableEq Alpha]
    (labels : Finset Alpha) (predicate : Alpha → Set Omega)
    (hpredicate : ∀ label ∈ labels, MeasurableSet (predicate label)) :
    MeasurableSet {omega | ∀ label ∈ labels, omega ∈ predicate label} := by
  classical
  induction labels using Finset.induction_on with
  | empty =>
      simp
  | insert label labels hnot_mem ih =>
      have hhead : MeasurableSet (predicate label) :=
        hpredicate label (by simp)
      have htail : MeasurableSet {omega | ∀ later ∈ labels,
          omega ∈ predicate later} := by
        apply ih
        intro later hlater
        exact hpredicate later (by simp [hlater])
      have hset :
          {omega | ∀ later ∈ insert label labels, omega ∈ predicate later} =
            predicate label ∩ {omega | ∀ later ∈ labels,
              omega ∈ predicate later} := by
        ext omega
        simp
      rw [hset]
      exact hhead.inter htail

private theorem measurableSet_taggedAdmittedSourceArrivalPattern_pairMatch
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (left right : TaggedAdmittedSourceJobId Category) :
    MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      ((left, right) ∈ pattern.equalPairs ↔
        taggedAdmittedSourceArrival target z.1 left =
          taggedAdmittedSourceArrival target z.1 right) ∧
      ((left, right) ∈ pattern.earlierPairs ↔
        taggedAdmittedSourceArrival target z.1 left <
          taggedAdmittedSourceArrival target z.1 right)} := by
  by_cases hequal : (left, right) ∈ pattern.equalPairs
  · by_cases hearlier : (left, right) ∈ pattern.earlierPairs
    · have hset :
          {z : TaggedAdmittedSourceGoodCarrier target |
            ((left, right) ∈ pattern.equalPairs ↔
              taggedAdmittedSourceArrival target z.1 left =
                taggedAdmittedSourceArrival target z.1 right) ∧
            ((left, right) ∈ pattern.earlierPairs ↔
              taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right)} =
            {z | taggedAdmittedSourceArrival target z.1 left =
              taggedAdmittedSourceArrival target z.1 right} ∩
              {z | taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right} := by
          ext z
          simp [hequal, hearlier]
      rw [hset]
      exact (measurableSet_taggedAdmittedSourceArrival_eq_goodCarrier
        target left right).inter
        (measurableSet_taggedAdmittedSourceArrival_lt_goodCarrier
          target left right)
    · have hset :
          {z : TaggedAdmittedSourceGoodCarrier target |
            ((left, right) ∈ pattern.equalPairs ↔
              taggedAdmittedSourceArrival target z.1 left =
                taggedAdmittedSourceArrival target z.1 right) ∧
            ((left, right) ∈ pattern.earlierPairs ↔
              taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right)} =
            {z | taggedAdmittedSourceArrival target z.1 left =
              taggedAdmittedSourceArrival target z.1 right} ∩
              {z | taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right}ᶜ := by
          ext z
          simp [hequal, hearlier]
      rw [hset]
      exact (measurableSet_taggedAdmittedSourceArrival_eq_goodCarrier
        target left right).inter
        (measurableSet_taggedAdmittedSourceArrival_lt_goodCarrier
          target left right).compl
  · by_cases hearlier : (left, right) ∈ pattern.earlierPairs
    · have hset :
          {z : TaggedAdmittedSourceGoodCarrier target |
            ((left, right) ∈ pattern.equalPairs ↔
              taggedAdmittedSourceArrival target z.1 left =
                taggedAdmittedSourceArrival target z.1 right) ∧
            ((left, right) ∈ pattern.earlierPairs ↔
              taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right)} =
            {z | taggedAdmittedSourceArrival target z.1 left =
              taggedAdmittedSourceArrival target z.1 right}ᶜ ∩
              {z | taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right} := by
          ext z
          simp [hequal, hearlier]
      rw [hset]
      exact (measurableSet_taggedAdmittedSourceArrival_eq_goodCarrier
        target left right).compl.inter
        (measurableSet_taggedAdmittedSourceArrival_lt_goodCarrier
          target left right)
    · have hset :
          {z : TaggedAdmittedSourceGoodCarrier target |
            ((left, right) ∈ pattern.equalPairs ↔
              taggedAdmittedSourceArrival target z.1 left =
                taggedAdmittedSourceArrival target z.1 right) ∧
            ((left, right) ∈ pattern.earlierPairs ↔
              taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right)} =
            {z | taggedAdmittedSourceArrival target z.1 left =
              taggedAdmittedSourceArrival target z.1 right}ᶜ ∩
              {z | taggedAdmittedSourceArrival target z.1 left <
                taggedAdmittedSourceArrival target z.1 right}ᶜ := by
          ext z
          simp [hequal, hearlier]
      rw [hset]
      exact (measurableSet_taggedAdmittedSourceArrival_eq_goodCarrier
        target left right).compl.inter
        (measurableSet_taggedAdmittedSourceArrival_lt_goodCarrier
          target left right).compl

/-- Every fixed finite source-ledger and tie-comparison pattern has a Borel
fiber on the Palm good carrier.  The proof checks finitely many source epoch
equalities and strict inequalities; it does not use an almost-sure no-ties
assumption. -/
theorem measurableSet_taggedAdmittedSourceArrivalPatternFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category) :
    MeasurableSet (taggedAdmittedSourceArrivalPatternFiber
      start horizon target pattern) := by
  have hledger : MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      taggedAdmittedSourceJobLedger start horizon target z.1 = pattern.labels} := by
    exact measurableSet_taggedAdmittedSourceJobLedger_eq_goodCarrier
      start horizon target pattern.labels
  have hpairs : MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      ∀ left ∈ pattern.labels, ∀ right ∈ pattern.labels,
        ((left, right) ∈ pattern.equalPairs ↔
          taggedAdmittedSourceArrival target z.1 left =
            taggedAdmittedSourceArrival target z.1 right) ∧
        ((left, right) ∈ pattern.earlierPairs ↔
          taggedAdmittedSourceArrival target z.1 left <
            taggedAdmittedSourceArrival target z.1 right)} := by
    let pairMatches : TaggedAdmittedSourceJobId Category →
        TaggedAdmittedSourceJobId Category →
        Set (TaggedAdmittedSourceGoodCarrier target) := fun left right =>
      {z | ((left, right) ∈ pattern.equalPairs ↔
        taggedAdmittedSourceArrival target z.1 left =
          taggedAdmittedSourceArrival target z.1 right) ∧
        ((left, right) ∈ pattern.earlierPairs ↔
          taggedAdmittedSourceArrival target z.1 left <
            taggedAdmittedSourceArrival target z.1 right)}
    change MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      ∀ left ∈ pattern.labels, ∀ right ∈ pattern.labels,
        z ∈ pairMatches left right}
    apply measurableSet_forall_mem_finset pattern.labels
      (fun left => {z : TaggedAdmittedSourceGoodCarrier target | ∀ right ∈ pattern.labels,
        z ∈ pairMatches left right})
    intro left hleft
    apply measurableSet_forall_mem_finset pattern.labels
      (fun right => pairMatches left right)
    intro right hright
    exact measurableSet_taggedAdmittedSourceArrivalPattern_pairMatch
      target pattern left right
  change MeasurableSet ({z : TaggedAdmittedSourceGoodCarrier target |
    taggedAdmittedSourceJobLedger start horizon target z.1 = pattern.labels} ∩
    {z | ∀ left ∈ pattern.labels, ∀ right ∈ pattern.labels,
      ((left, right) ∈ pattern.equalPairs ↔
        taggedAdmittedSourceArrival target z.1 left =
          taggedAdmittedSourceArrival target z.1 right) ∧
      ((left, right) ∈ pattern.earlierPairs ↔
        taggedAdmittedSourceArrival target z.1 left <
          taggedAdmittedSourceArrival target z.1 right)})
  exact hledger.inter hpairs

/-- The canonical finite comparison pattern extracted from one literal source
input.  It retains all exact equality pairs and strict earlier pairs on the
finite ledger, including deterministic simultaneous source arrivals. -/
noncomputable def taggedAdmittedSourceArrivalPatternOf
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    TaggedAdmittedSourceArrivalPattern Category :=
  let labels := taggedAdmittedSourceJobLedger start horizon target z
  { labels
    equalPairs := (labels.product labels).filter fun pair =>
      taggedAdmittedSourceArrival target z pair.1 =
        taggedAdmittedSourceArrival target z pair.2
    earlierPairs := (labels.product labels).filter fun pair =>
      taggedAdmittedSourceArrival target z pair.1 <
        taggedAdmittedSourceArrival target z pair.2 }

/-- The canonical finite comparison pattern records exactly the literal source
ledger's arrival equality and strict-order facts. -/
theorem taggedAdmittedSourceArrivalPatternOf_matches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    (taggedAdmittedSourceArrivalPatternOf start horizon target z).Matches
      start horizon target z := by
  change taggedAdmittedSourceJobLedger start horizon target z =
      taggedAdmittedSourceJobLedger start horizon target z ∧
    ∀ left ∈ taggedAdmittedSourceJobLedger start horizon target z,
      ∀ right ∈ taggedAdmittedSourceJobLedger start horizon target z,
        ((left, right) ∈
          ((taggedAdmittedSourceJobLedger start horizon target z).product
            (taggedAdmittedSourceJobLedger start horizon target z)).filter
            (fun pair => taggedAdmittedSourceArrival target z pair.1 =
              taggedAdmittedSourceArrival target z pair.2) ↔
          taggedAdmittedSourceArrival target z left =
            taggedAdmittedSourceArrival target z right) ∧
        ((left, right) ∈
          ((taggedAdmittedSourceJobLedger start horizon target z).product
            (taggedAdmittedSourceJobLedger start horizon target z)).filter
            (fun pair => taggedAdmittedSourceArrival target z pair.1 <
              taggedAdmittedSourceArrival target z pair.2) ↔
          taggedAdmittedSourceArrival target z left <
            taggedAdmittedSourceArrival target z right)
  constructor
  · rfl
  · intro left hleft right hright
    constructor <;>
      simp [Finset.mem_filter, Finset.mem_product, hleft, hright]

/-- The fixed Borel pattern fibers cover the whole Palm good carrier.  The
index type is countable because it consists only of finite subsets of the
countable source-label type. -/
theorem iUnion_taggedAdmittedSourceArrivalPatternFiber_eq_univ
    (start horizon : ℝ) (target : Category) :
    (⋃ pattern : TaggedAdmittedSourceArrivalPattern Category,
      taggedAdmittedSourceArrivalPatternFiber start horizon target pattern) = Set.univ := by
  ext z
  constructor
  · intro _
    simp
  · intro _
    apply Set.mem_iUnion.mpr
    refine ⟨taggedAdmittedSourceArrivalPatternOf start horizon target z.1, ?_⟩
    exact taggedAdmittedSourceArrivalPatternOf_matches start horizon target z.1

/-- The source labels tied with one fixed pivot according to a fixed
comparison pattern. -/
def TaggedAdmittedSourceArrivalPattern.tieBlock
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) :
    Finset (TaggedAdmittedSourceJobId Category) :=
  pattern.labels.filter fun job => (job, pivot) ∈ pattern.equalPairs

/-- The fixed class-specific work of one pattern equality block. -/
def taggedAdmittedSourceArrivalPatternBlockWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (k : Category) : ℝ :=
  ∑ job ∈ (pattern.tieBlock pivot).filter (fun job => job.1 = k),
    taggedAdmittedSourceWork target z job

/-- A fixed finite sum of literal source-work coordinates is Borel on the
Palm good carrier. -/
theorem measurable_taggedAdmittedSourceWork_sum_goodCarrier
    (target : Category) (labels : Finset (TaggedAdmittedSourceJobId Category)) :
    Measurable (fun z : TaggedAdmittedSourceGoodCarrier target =>
      ∑ job ∈ labels, taggedAdmittedSourceWork target z.1 job) := by
  apply Finset.measurable_sum
  intro job _
  exact (measurable_taggedAdmittedSourceWork target job).comp measurable_subtype_coe

/-- The source work of every fixed tie block and class is Borel on the Palm
good carrier. -/
theorem measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (k : Category) :
    Measurable (fun z : TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k) := by
  simpa [taggedAdmittedSourceArrivalPatternBlockWork] using
    (measurable_taggedAdmittedSourceWork_sum_goodCarrier target
      ((pattern.tieBlock pivot).filter fun job => job.1 = k))

/-- On a matching pattern, the fixed equality block of a retained pivot is
exactly the literal source-ledger fiber at the pivot's physical arrival epoch.
This is the tie-preserving bridge from pattern data to the actual source
batch; the pivot need not be an isolated arrival. -/
theorem TaggedAdmittedSourceArrivalPattern.tieBlock_eq_sourceLedger_arrivalFiber
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels) :
    pattern.tieBlock pivot =
      (taggedAdmittedSourceJobLedger start horizon target z).filter fun job =>
        taggedAdmittedSourceArrival target z job =
          taggedAdmittedSourceArrival target z pivot := by
  rcases hmatches with ⟨hledger, hcomparison⟩
  rw [hledger]
  ext job
  simp only [tieBlock, Finset.mem_filter]
  constructor
  · rintro ⟨hjob, hequal_pair⟩
    exact ⟨hjob, (hcomparison job hjob pivot hpivot).1.mp hequal_pair⟩
  · rintro ⟨hjob, hequal⟩
    exact ⟨hjob, (hcomparison job hjob pivot hpivot).1.mpr hequal⟩

/-- The finite source-ledger representation of the literal batch at one
physical epoch and class. -/
def taggedAdmittedSourceLedgerJobsAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) (k : Category) :
    Finset (TaggedAdmittedSourceJobId Category) :=
  (taggedAdmittedSourceJobLedger start horizon target z).filter fun job =>
    job.1 = k ∧ taggedAdmittedSourceArrival target z job = eventTime

/-- Summing the literal source-ledger jobs at one epoch recovers the original
class-specific collapsed batch work. -/
theorem sum_taggedAdmittedSourceLedgerJobsAt_eq_taggedAdmittedBatchAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) (k : Category) :
    ∑ job ∈ taggedAdmittedSourceLedgerJobsAt start horizon target z eventTime k,
      taggedAdmittedSourceWork target z job =
      taggedAdmittedBatchAt start horizon target z eventTime k := by
  unfold taggedAdmittedSourceLedgerJobsAt taggedAdmittedBatchAt
  apply Finset.sum_bij (fun job _ => job.2)
  · intro job hjob
    rcases job with ⟨j, n⟩
    simp only [Finset.mem_filter] at hjob
    have hj : j = k := hjob.2.1
    subst j
    exact Finset.mem_filter.mpr ⟨
      (mem_taggedAdmittedSourceJobLedger_iff start horizon target z k n).mp hjob.1,
      hjob.2.2⟩
  · intro left hleft right hright heq
    rcases left with ⟨leftCategory, leftIndex⟩
    rcases right with ⟨rightCategory, rightIndex⟩
    simp only [Finset.mem_filter] at hleft hright
    exact Prod.ext (hleft.2.1.trans hright.2.1.symm) heq
  · intro n hn
    simp only [Finset.mem_filter] at hn
    refine ⟨(k, n), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨
      taggedAdmittedSourceJob_mem_ledger start horizon target z k n hn.1,
      ⟨rfl, hn.2⟩⟩
  · intro job hjob
    rcases job with ⟨j, n⟩
    simp only [Finset.mem_filter] at hjob
    have hj : j = k := hjob.2.1
    subst j
    rfl

/-- On a matching finite comparison pattern, the Borel fixed-block work is
the actual collapsed source batch work at its pivot epoch. -/
theorem taggedAdmittedSourceArrivalPatternBlockWork_eq_taggedAdmittedBatchAt_of_matches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels)
    (k : Category) :
    taggedAdmittedSourceArrivalPatternBlockWork target z pattern pivot k =
      taggedAdmittedBatchAt start horizon target z
        (taggedAdmittedSourceArrival target z pivot) k := by
  rw [taggedAdmittedSourceArrivalPatternBlockWork,
    pattern.tieBlock_eq_sourceLedger_arrivalFiber
      start horizon target z hmatches pivot hpivot]
  have hfilter :
      ((taggedAdmittedSourceJobLedger start horizon target z).filter fun job =>
        taggedAdmittedSourceArrival target z job =
          taggedAdmittedSourceArrival target z pivot).filter fun job => job.1 = k =
      taggedAdmittedSourceLedgerJobsAt start horizon target z
        (taggedAdmittedSourceArrival target z pivot) k := by
    ext job
    simp [taggedAdmittedSourceLedgerJobsAt, and_assoc, and_comm]
  rw [hfilter]
  exact sum_taggedAdmittedSourceLedgerJobsAt_eq_taggedAdmittedBatchAt
    start horizon target z (taggedAdmittedSourceArrival target z pivot) k

/-- A total batch-work kernel for a fixed list of source-labelled pattern
representatives.  At any requested time it sums the fixed equality blocks
whose representative has that epoch.  Thus the definition is Borel even
before a later proof establishes that the representatives are one per batch. -/
def taggedAdmittedSourceArrivalPatternBatchKernel
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (z : TaggedAdmittedSourceGoodCarrier target) (eventTime : ℝ)
    (k : Category) : ℝ :=
  (pivots.map fun pivot =>
    if eventTime = taggedAdmittedSourceArrival target z.1 pivot then
      taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
    else 0).sum

/-- The fixed representative-list batch kernel is jointly Borel in physical
time and the Palm good-carrier input. -/
theorem measurable_taggedAdmittedSourceArrivalPatternBatchKernel
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivots : List (TaggedAdmittedSourceJobId Category)) (k : Category) :
    Measurable (fun pair : ℝ × TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedSourceArrivalPatternBatchKernel target pattern pivots
        pair.2 pair.1 k) := by
  induction pivots with
  | nil =>
      simp [taggedAdmittedSourceArrivalPatternBatchKernel]
  | cons pivot pivots ih =>
      have harrival : Measurable (fun pair : ℝ × TaggedAdmittedSourceGoodCarrier target =>
          taggedAdmittedSourceArrival target pair.2.1 pivot) :=
        (measurable_taggedAdmittedSourceArrival_goodCarrier target pivot).comp
          measurable_snd
      have hblock : Measurable (fun pair : ℝ × TaggedAdmittedSourceGoodCarrier target =>
          taggedAdmittedSourceArrivalPatternBlockWork target pair.2.1
            pattern pivot k) :=
        (measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
          target pattern pivot k).comp measurable_snd
      have hcondition : MeasurableSet {pair : ℝ × TaggedAdmittedSourceGoodCarrier target |
          pair.1 = taggedAdmittedSourceArrival target pair.2.1 pivot} := by
        exact measurableSet_eq_fun measurable_fst harrival
      simpa [taggedAdmittedSourceArrivalPatternBatchKernel] using
        (Measurable.ite hcondition hblock
          (measurable_const : Measurable (fun _ : ℝ × TaggedAdmittedSourceGoodCarrier target =>
            (0 : ℝ)))).add ih

/-- The generic finite GPS runner is Borel for every fixed source-labelled
tie-aware representative script.  This is a real executor result, not merely
a measurable ledger coordinate; it preserves equal-time source blocks in the
kernel and does not make a no-ties assumption. -/
theorem finiteGPSBatchTraceResultMeasurable_taggedAdmittedSourceArrivalPatternScript
    (start : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    FiniteGPSBatchTraceResultMeasurable (fun z : TaggedAdmittedSourceGoodCarrier target =>
      finiteGPSRunBatchTrace capacity weight
        (fun eventTime k => taggedAdmittedSourceArrivalPatternBatchKernel
          target pattern pivots z eventTime k)
        start initialWork
        (pivots.map fun pivot =>
          taggedAdmittedSourceArrival target z.1 pivot)) := by
  let times : List (TaggedAdmittedSourceGoodCarrier target → ℝ) :=
    pivots.map fun pivot z => taggedAdmittedSourceArrival target z.1 pivot
  have htimes : ∀ time ∈ times, Measurable time := by
    intro time htime
    rcases List.mem_map.mp htime with ⟨pivot, _hpivot, rfl⟩
    exact measurable_taggedAdmittedSourceArrival_goodCarrier target pivot
  have hresult := finiteGPSBatchTraceResultMeasurable_apply
    capacity weight
    (fun z eventTime k => taggedAdmittedSourceArrivalPatternBatchKernel
      target pattern pivots z eventTime k)
    (by
      intro k
      exact measurable_taggedAdmittedSourceArrivalPatternBatchKernel
        target pattern pivots k)
    (fun _ => start) measurable_const
    (fun _ => initialWork) (by
      intro k
      exact measurable_const)
    times htimes
  simpa [times] using hresult

/-- A deterministic representative script for a fixed finite tie-aware
pattern.  Its list contains exactly one source label from every equality
block, and every earlier pair of list entries is recorded as a strict source
epoch comparison.  The script is fixed pattern data, not a random selector;
the source input appears only when its Borel arrival-coordinate functions are
evaluated. -/
structure TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript
    (pattern : TaggedAdmittedSourceArrivalPattern Category) where
  pivots : List (TaggedAdmittedSourceJobId Category)
  nodup : pivots.Nodup
  pivot_mem : ∀ pivot ∈ pivots, pivot ∈ pattern.labels
  /-- Every retained source label belongs to the equality block of exactly
  one listed pivot. -/
  exactly_one_pivot_per_block : ∀ job ∈ pattern.labels,
    ∃! pivot, pivot ∈ pivots ∧ (job, pivot) ∈ pattern.equalPairs
  /-- The script places distinct equality blocks in strict source-epoch
  order.  Equal-time jobs share one pivot rather than being ordered here. -/
  chronological : pivots.Pairwise fun left right =>
    left ∈ pattern.labels ∧ right ∈ pattern.labels ∧
      (left, right) ∈ pattern.earlierPairs

/-- The fixed list of Borel arrival-coordinate functions carried by a sorted
representative script.  This is the appropriate finite-dimensional Borel
representation of a fixed-length list; no measurable-space instance for
variable-length source lists is postulated. -/
def TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.arrivalCoordinates
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (target : Category) :
    List (TaggedAdmittedSourceGoodCarrier target → ℝ) :=
  script.pivots.map fun pivot z => taggedAdmittedSourceArrival target z.1 pivot

/-- Evaluate a fixed representative script at one source input. -/
def TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.arrivalTimes
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : List ℝ :=
  script.pivots.map fun pivot => taggedAdmittedSourceArrival target z pivot

/-- Every coordinate in the deterministic representative list is Borel on
the Palm good carrier. -/
theorem TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.measurable_arrivalCoordinates
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (target : Category) :
    ∀ coordinate ∈ script.arrivalCoordinates target, Measurable coordinate := by
  intro coordinate hcoordinate
  rcases List.mem_map.mp hcoordinate with ⟨pivot, _hpivot, rfl⟩
  exact measurable_taggedAdmittedSourceArrival_goodCarrier target pivot

/-- On a source input matching the fixed pattern, the representative arrival
times are pairwise strictly increasing.  This uses the pattern's explicit
strict-comparison relation, so simultaneous source arrivals remain grouped in
one equality block rather than being discarded. -/
theorem TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.arrivalTimes_pairwise_lt_of_matches
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hmatches : pattern.Matches start horizon target z) :
    (script.arrivalTimes target z).Pairwise (· < ·) := by
  rw [arrivalTimes, List.pairwise_map]
  apply script.chronological.imp
  intro left right hordered
  exact (hmatches.2 left hordered.1 right hordered.2.1).2.mp hordered.2.2

/-- The strict representative ordering makes the evaluated batch-time list
duplicate-free on every matching source input. -/
theorem TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.arrivalTimes_nodup_of_matches
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hmatches : pattern.Matches start horizon target z) :
    (script.arrivalTimes target z).Nodup := by
  exact (script.arrivalTimes_pairwise_lt_of_matches
    start horizon target z hmatches).nodup

/-- A matching representative script has exactly the actual finite set of
literal batch epochs.  Coverage is proved from source labels and equality
pairs, not from the names of the script or executor. -/
theorem TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.arrivalTimes_toFinset_eq_taggedAdmittedBatchTimes_of_matches
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hmatches : pattern.Matches start horizon target z) :
    (script.arrivalTimes target z).toFinset =
      taggedAdmittedBatchTimes start horizon target z := by
  ext eventTime
  constructor
  · intro htime
    have hlist : eventTime ∈ script.arrivalTimes target z := by
      simpa [arrivalTimes] using htime
    rcases List.mem_map.mp hlist with ⟨pivot, hpivot, hpivot_time⟩
    apply Finset.mem_image.mpr
    refine ⟨pivot, ?_, hpivot_time⟩
    rw [hmatches.1]
    exact script.pivot_mem pivot hpivot
  · intro htime
    rcases (mem_taggedAdmittedBatchTimes_iff start horizon target z eventTime).mp htime with
      ⟨job, hjob, hjob_time⟩
    have hlabel : job ∈ pattern.labels := by
      rw [← hmatches.1]
      exact hjob
    rcases script.exactly_one_pivot_per_block job hlabel with
      ⟨pivot, ⟨hpivot, hequal_pair⟩, _hunique⟩
    have hpivot_label : pivot ∈ pattern.labels := script.pivot_mem pivot hpivot
    have hequal_time : taggedAdmittedSourceArrival target z job =
        taggedAdmittedSourceArrival target z pivot :=
      (hmatches.2 job hlabel pivot hpivot_label).1.mp hequal_pair
    have hpivot_time : taggedAdmittedSourceArrival target z pivot = eventTime :=
      hequal_time.symm.trans hjob_time
    have hlist : eventTime ∈ script.arrivalTimes target z := by
      apply List.mem_map.mpr
      exact ⟨pivot, hpivot, hpivot_time⟩
    simpa [arrivalTimes] using hlist

/-- A sorted representative script evaluates to the literal chronological
batch-time trace on every matching pattern fiber.  This supplies the exact
tie-preserving sorted-script bridge needed to specialize the Borel fixed
batch-runner result; it does not yet address source-labelled FCFS completion
selection. -/
theorem TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript.arrivalTimes_eq_taggedAdmittedBatchTimeTrace_of_matches
    {pattern : TaggedAdmittedSourceArrivalPattern Category}
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hmatches : pattern.Matches start horizon target z) :
    script.arrivalTimes target z = taggedAdmittedBatchTimeTrace start horizon target z := by
  have hpairwise_lt := script.arrivalTimes_pairwise_lt_of_matches
    start horizon target z hmatches
  have hpairwise_le : (script.arrivalTimes target z).Pairwise (· ≤ ·) :=
    hpairwise_lt.imp fun hlt => hlt.le
  have hnodup := script.arrivalTimes_nodup_of_matches
    start horizon target z hmatches
  have htimes := script.arrivalTimes_toFinset_eq_taggedAdmittedBatchTimes_of_matches
    start horizon target z hmatches
  have hsort :
      (script.arrivalTimes target z).toFinset.sort (fun left right : ℝ => left ≤ right) =
        script.arrivalTimes target z :=
    (List.toFinset_sort (r := fun left right : ℝ => left ≤ right) hnodup).mpr
      hpairwise_le
  calc
    script.arrivalTimes target z =
        (script.arrivalTimes target z).toFinset.sort (fun left right : ℝ => left ≤ right) :=
      hsort.symm
    _ = (taggedAdmittedBatchTimes start horizon target z).sort
        (fun left right : ℝ => left ≤ right) := by rw [htimes]
    _ = taggedAdmittedBatchTimeTrace start horizon target z := rfl

/-- Every realized finite comparison pattern admits a tie-aware sorted
representative script.  The construction enumerates the literal finite batch
epochs, chooses one source label at each epoch, and then proves that this
finite witness depends only on the fixed pattern through its criterion.  A
later Borel gluing argument may range over all such fixed scripts, so no
measurable or canonical representative selector is needed here. -/
theorem TaggedAdmittedSourceArrivalPattern.nonempty_sortedRepresentativeScript_of_matches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z) :
    Nonempty (TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern) := by
  classical
  let times : Finset ℝ := taggedAdmittedBatchTimes start horizon target z
  let sortedTimes : List ℝ := times.sort (fun left right : ℝ => left ≤ right)
  have hsortedTimes_mem : ∀ time ∈ sortedTimes, time ∈ times := by
    intro time htime
    simpa [sortedTimes] using
      (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp htime
  have htime_source : ∀ (time : ℝ), time ∈ times →
      ∃ job : TaggedAdmittedSourceJobId Category,
        job ∈ taggedAdmittedSourceJobLedger start horizon target z ∧
          taggedAdmittedSourceArrival target z job = time := by
    intro time htime
    simpa [times] using
      (mem_taggedAdmittedBatchTimes_iff start horizon target z time).mp htime
  let pivotFor : ∀ (time : ℝ), time ∈ times → TaggedAdmittedSourceJobId Category :=
    fun time htime => Classical.choose (htime_source time htime)
  have hpivotFor_spec : ∀ (time : ℝ) (htime : time ∈ times),
      pivotFor time htime ∈ taggedAdmittedSourceJobLedger start horizon target z ∧
        taggedAdmittedSourceArrival target z (pivotFor time htime) = time := by
    intro time htime
    exact Classical.choose_spec (htime_source time htime)
  let pivots : List (TaggedAdmittedSourceJobId Category) :=
    sortedTimes.pmap pivotFor hsortedTimes_mem
  have hsortedTimes_nodup : sortedTimes.Nodup := by
    simpa [sortedTimes] using
      (Finset.sort_nodup times (fun left right : ℝ => left ≤ right))
  have hpivots_nodup : pivots.Nodup := by
    dsimp [pivots]
    apply hsortedTimes_nodup.pmap
    intro left hleft right hright hpivots_eq
    have hleft_spec := hpivotFor_spec left hleft
    have hright_spec := hpivotFor_spec right hright
    calc
      left = taggedAdmittedSourceArrival target z
          (pivotFor left hleft) := hleft_spec.2.symm
      _ = taggedAdmittedSourceArrival target z
          (pivotFor right hright) :=
        congrArg (taggedAdmittedSourceArrival target z) hpivots_eq
      _ = right := hright_spec.2
  have hpivots_mem : ∀ pivot ∈ pivots, pivot ∈ pattern.labels := by
    intro pivot hpivot
    dsimp [pivots] at hpivot
    rcases List.mem_pmap.mp hpivot with ⟨time, htime, hpivot_eq⟩
    rw [← hpivot_eq, ← hmatches.1]
    exact (hpivotFor_spec time (hsortedTimes_mem time htime)).1
  have pairwise_lt_of_pairwise_le_nodup :
      ∀ {trace : List ℝ}, trace.Pairwise (· ≤ ·) → trace.Nodup →
        trace.Pairwise (· < ·) := by
    intro trace hle hnodup
    induction trace with
    | nil => simp
    | cons time trace ih =>
        simp only [List.pairwise_cons] at hle ⊢
        rw [List.nodup_cons] at hnodup
        refine ⟨?_, ih hle.2 hnodup.2⟩
        intro later hlater
        exact lt_of_le_of_ne (hle.1 later hlater) (by
          intro heq
          subst later
          exact hnodup.1 hlater)
  have hsortedTimes_pairwise_le : sortedTimes.Pairwise (· ≤ ·) := by
    simpa [sortedTimes] using
      (Finset.pairwise_sort times (fun left right : ℝ => left ≤ right))
  have hsortedTimes_pairwise_lt : sortedTimes.Pairwise (· < ·) :=
    pairwise_lt_of_pairwise_le_nodup hsortedTimes_pairwise_le hsortedTimes_nodup
  have hpivots_chronological : pivots.Pairwise fun left right =>
      left ∈ pattern.labels ∧ right ∈ pattern.labels ∧
        (left, right) ∈ pattern.earlierPairs := by
    dsimp [pivots]
    refine hsortedTimes_pairwise_lt.pmap hsortedTimes_mem ?_
    intro left hleft right hright hlt
    have hleft_spec := hpivotFor_spec left hleft
    have hright_spec := hpivotFor_spec right hright
    have hleft_label : pivotFor left hleft ∈ pattern.labels := by
      rw [← hmatches.1]
      exact hleft_spec.1
    have hright_label : pivotFor right hright ∈ pattern.labels := by
      rw [← hmatches.1]
      exact hright_spec.1
    refine ⟨hleft_label, hright_label, ?_⟩
    apply (hmatches.2 (pivotFor left hleft) hleft_label
      (pivotFor right hright) hright_label).2.mpr
    simpa [hleft_spec.2, hright_spec.2] using hlt
  refine ⟨{
    pivots := pivots
    nodup := hpivots_nodup
    pivot_mem := hpivots_mem
    exactly_one_pivot_per_block := ?_
    chronological := hpivots_chronological
  }⟩
  intro job hjob
  have hledger_job : job ∈ taggedAdmittedSourceJobLedger start horizon target z := by
    rw [hmatches.1]
    exact hjob
  have htime : taggedAdmittedSourceArrival target z job ∈ times := by
    simpa [times] using
      (mem_taggedAdmittedBatchTimes_iff start horizon target z
        (taggedAdmittedSourceArrival target z job)).mpr ⟨job, hledger_job, rfl⟩
  have htime_sorted : taggedAdmittedSourceArrival target z job ∈ sortedTimes := by
    simpa [sortedTimes] using
      (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr htime
  refine ⟨pivotFor (taggedAdmittedSourceArrival target z job)
      (hsortedTimes_mem _ htime_sorted), ?_, ?_⟩
  · constructor
    · change pivotFor (taggedAdmittedSourceArrival target z job)
          (hsortedTimes_mem _ htime_sorted) ∈ pivots
      dsimp [pivots]
      exact List.mem_pmap_of_mem htime_sorted
    · have hpivot_label : pivotFor (taggedAdmittedSourceArrival target z job)
        (hsortedTimes_mem _ htime_sorted) ∈ pattern.labels := by
        apply hpivots_mem
        change pivotFor (taggedAdmittedSourceArrival target z job)
          (hsortedTimes_mem _ htime_sorted) ∈ pivots
        dsimp [pivots]
        exact List.mem_pmap_of_mem htime_sorted
      apply (hmatches.2 job hjob
        (pivotFor (taggedAdmittedSourceArrival target z job)
          (hsortedTimes_mem _ htime_sorted)) hpivot_label).1.mpr
      exact (hpivotFor_spec _ (hsortedTimes_mem _ htime_sorted)).2.symm
  · intro other hother
    rcases hother with ⟨hother_mem, hother_equal⟩
    have hother_label : other ∈ pattern.labels := hpivots_mem other hother_mem
    have hjob_other_arrival : taggedAdmittedSourceArrival target z job =
        taggedAdmittedSourceArrival target z other :=
      (hmatches.2 job hjob other hother_label).1.mp hother_equal
    dsimp [pivots] at hother_mem
    rcases List.mem_pmap.mp hother_mem with ⟨otherTime, hotherTime, hother_eq⟩
    have hother_arrival : taggedAdmittedSourceArrival target z other = otherTime := by
      rw [← hother_eq]
      exact (hpivotFor_spec otherTime
        (hsortedTimes_mem otherTime hotherTime)).2
    have htime_eq : otherTime = taggedAdmittedSourceArrival target z job :=
      hother_arrival.symm.trans hjob_other_arrival.symm
    rw [← hother_eq]
    cases htime_eq
    rfl

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
