import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedSourceMeasurability
import Mathlib.Tactic

/-!
# Borel fixed-ledger strata for the literal tagged SLA source

The literal finite source ledger is a finite `Finset` assembled from random
arrival paths.  This module deliberately does not give that `Finset` a
measurable-space instance.  Instead, on the Borel Palm good-carrier subtype,
it proves Borel membership for each fixed source identifier and Borel fibers
for each fixed finite source ledger.  Those fibers cover the carrier and are
the source-only stratification needed before a later finite-executor Borel
argument.

No claim here concerns batch sorting, GPS execution, FCFS completion, or
arrival ties.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open MeasureTheory

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal target/passive tagged input restricted to the Borel Palm
good carrier required by the target interval enumerator. -/
abbrev TaggedAdmittedSourceGoodCarrier (target : Category) :=
  {z : StationaryAdmittedTargetPassiveTaggedInput target //
    palmTaggedArrivalGoodCarrier z.1.1}

/-- A fixed literal source-arrival coordinate remains Borel after restricting
the tagged input to the Palm good carrier. -/
theorem measurable_taggedAdmittedSourceArrival_goodCarrier
    (target : Category) (job : TaggedAdmittedSourceJobId Category) :
    Measurable (fun z : TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedSourceArrival target z.1 job) := by
  exact (measurable_taggedAdmittedSourceArrival target job).comp
    measurable_subtype_coe

/-- For fixed physical endpoints and a fixed literal source identifier,
membership in the finite source ledger is a Borel event on the good carrier.
The proof uses the actual half-open source interval semantics; it does not
treat the ledger as a random measurable finite set. -/
theorem measurableSet_mem_taggedAdmittedSourceJobLedger_goodCarrier
    (start horizon : ℝ) (target : Category)
    (job : TaggedAdmittedSourceJobId Category) :
    MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      job ∈ taggedAdmittedSourceJobLedger start horizon target z.1} := by
  let arrival : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
    taggedAdmittedSourceArrival target z.1 job
  have harrival : Measurable arrival := by
    exact measurable_taggedAdmittedSourceArrival_goodCarrier target job
  have hmembership :
      {z : TaggedAdmittedSourceGoodCarrier target |
        job ∈ taggedAdmittedSourceJobLedger start horizon target z.1} =
      {z | start ≤ arrival z ∧ arrival z < horizon} := by
    ext z
    simpa [arrival] using
      (mem_taggedAdmittedSourceJobLedger_interval_iff start horizon target z.1
        z.2 job)
  rw [hmembership]
  exact (measurableSet_le measurable_const harrival).inter
    (measurableSet_lt harrival measurable_const)

/-- Every fixed finite literal source ledger is a Borel fiber on the good
carrier.  The proof is a countable intersection of fixed-identifier decisions,
not a measurability assertion for the random `Finset` itself. -/
theorem measurableSet_taggedAdmittedSourceJobLedger_eq_goodCarrier
    (start horizon : ℝ) (target : Category)
    (labels : Finset (TaggedAdmittedSourceJobId Category)) :
    MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
      taggedAdmittedSourceJobLedger start horizon target z.1 = labels} := by
  classical
  have hmem : ∀ job : TaggedAdmittedSourceJobId Category,
      MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
        job ∈ taggedAdmittedSourceJobLedger start horizon target z.1} := by
    intro job
    exact measurableSet_mem_taggedAdmittedSourceJobLedger_goodCarrier
      start horizon target job
  have hfiber : ∀ job : TaggedAdmittedSourceJobId Category,
      MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
        job ∈ taggedAdmittedSourceJobLedger start horizon target z.1 ↔
          job ∈ labels} := by
    intro job
    by_cases hlabel : job ∈ labels
    · simpa [hlabel] using hmem job
    · have hnot : MeasurableSet {z : TaggedAdmittedSourceGoodCarrier target |
          job ∉ taggedAdmittedSourceJobLedger start horizon target z.1} := by
        convert (hmem job).compl using 1
      simpa [hlabel] using hnot
  have heq :
      {z : TaggedAdmittedSourceGoodCarrier target |
        taggedAdmittedSourceJobLedger start horizon target z.1 = labels} =
      ⋂ job : TaggedAdmittedSourceJobId Category,
        {z | job ∈ taggedAdmittedSourceJobLedger start horizon target z.1 ↔
          job ∈ labels} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hz job
      simpa [hz]
    · intro hz
      ext job
      exact hz job
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- Distinct fixed-ledger fibers cannot share a good-carrier input. -/
theorem pairwiseDisjoint_taggedAdmittedSourceJobLedger_eq_goodCarrier
    (start horizon : ℝ) (target : Category) :
    Pairwise (fun left right : Finset (TaggedAdmittedSourceJobId Category) =>
      Disjoint
        {z : TaggedAdmittedSourceGoodCarrier target |
          taggedAdmittedSourceJobLedger start horizon target z.1 = left}
        {z : TaggedAdmittedSourceGoodCarrier target |
          taggedAdmittedSourceJobLedger start horizon target z.1 = right}) := by
  intro left right hne
  rw [Set.disjoint_left]
  intro z hleft hright
  exact hne (hleft.symm.trans hright)

/-- The Borel fixed-ledger fibers cover the entire Palm good carrier. -/
theorem iUnion_taggedAdmittedSourceJobLedger_eq_univ_goodCarrier
    (start horizon : ℝ) (target : Category) :
    (⋃ labels : Finset (TaggedAdmittedSourceJobId Category),
      {z : TaggedAdmittedSourceGoodCarrier target |
        taggedAdmittedSourceJobLedger start horizon target z.1 = labels}) = Set.univ := by
  ext z
  constructor
  · intro _
    simp
  · intro _
    exact Set.mem_iUnion.mpr
      ⟨taggedAdmittedSourceJobLedger start horizon target z.1, rfl⟩

/-- The finite source ledger is a Borel, countable-valued coordinate on the
Palm good carrier.  This packages the fixed-ledger fibers above without
treating a random `Finset` as a primitive measurable object. -/
theorem measurable_taggedAdmittedSourceJobLedger_goodCarrier
    (start horizon : ℝ) (target : Category) :
    Measurable[_, ⊤] (fun z : TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedSourceJobLedger start horizon target z.1) := by
  letI : MeasurableSpace (Finset (TaggedAdmittedSourceJobId Category)) := ⊤
  apply measurable_to_countable'
  intro labels
  exact measurableSet_taggedAdmittedSourceJobLedger_eq_goodCarrier
    start horizon target labels

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
