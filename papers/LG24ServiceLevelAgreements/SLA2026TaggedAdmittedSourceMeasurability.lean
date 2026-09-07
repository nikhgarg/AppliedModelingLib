import AppliedModelingLib.Foundations.Probability.MeasurableCountableEvaluation
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteExecution
import Mathlib.Tactic

/-!
# Measurable coordinates of the literal tagged SLA source

The finite GPS executor is driven by literal source identifiers.  This module
supplies the coordinate-level Borel facts needed to replace a random finite
ledger by a fixed finite label window.  It does not assert measurability of a
GPS run itself: that requires a separate finite-executor Borel proof.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open MeasureTheory

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The target Palm carrier used to totalize literal finite executions is a
Borel event.  The index-zero epoch equality is definitionally true for every
Palm gap path, so this is exactly the measurable two-sided gap-path carrier,
not an unproved selector condition. -/
theorem measurableSet_taggedAdmittedTargetPalmGoodCarrier
    (target : Category) :
    MeasurableSet {z : StationaryAdmittedTargetPassiveTaggedInput target |
      palmTaggedArrivalGoodCarrier z.1.1} := by
  simpa [palmTaggedArrivalGoodCarrier, candidatePalmArrival_zero] using
    (measurableSet_suspensionGoodGapPath.preimage
      (measurable_fst.comp measurable_fst))

/-- A fixed literal source arrival coordinate is measurable on the complete
target/passive Palm input. -/
theorem measurable_taggedAdmittedSourceArrival
    (target : Category) (job : TaggedAdmittedSourceJobId Category) :
    Measurable (fun z : StationaryAdmittedTargetPassiveTaggedInput target =>
      taggedAdmittedSourceArrival target z job) := by
  rcases job with ⟨k, n⟩
  by_cases htarget : k = target
  · subst k
    simpa [taggedAdmittedSourceArrival] using
      ((measurable_candidatePalmArrival n).comp
        (measurable_fst.comp measurable_fst))
  · simpa [taggedAdmittedSourceArrival, htarget] using
      ((measurable_suspensionBaseArrival n).comp
        (measurable_fst.comp
          ((measurable_pi_apply (⟨k, htarget⟩ : PassiveCategory target)).comp
            measurable_snd)))

/-- A fixed literal source work coordinate is measurable on the complete
target/passive Palm input. -/
theorem measurable_taggedAdmittedSourceWork
    (target : Category) (job : TaggedAdmittedSourceJobId Category) :
    Measurable (fun z : StationaryAdmittedTargetPassiveTaggedInput target =>
      taggedAdmittedSourceWork target z job) := by
  rcases job with ⟨k, n⟩
  by_cases htarget : k = target
  · subst k
    simpa [taggedAdmittedSourceWork] using
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst))
  · simpa [taggedAdmittedSourceWork, htarget] using
      ((measurable_pi_apply n).comp
        (measurable_snd.comp
          ((measurable_pi_apply (⟨k, htarget⟩ : PassiveCategory target)).comp
            measurable_snd)))

/-- A passive source's label immediately before a fixed physical time is a
measurable integer-valued coordinate of the full tagged input. -/
theorem measurable_taggedAdmittedPassiveCrossingIndexPastClosed
    (target : Category) (k : PassiveCategory target) (t : ℝ) :
    Measurable (fun z : StationaryAdmittedTargetPassiveTaggedInput target =>
      suspensionCrossingIndexPastClosed t ((z.2 k).1).1) := by
  exact (measurable_suspensionCrossingIndexPastClosed t).comp
    (measurable_subtype_coe.comp
      (measurable_fst.comp
        ((measurable_pi_apply k).comp measurable_snd)))

/-- Reindexing a fixed-category source arrival at a measurable integer label
preserves measurability.  This is the primitive used by deterministic-width
windows centered at a random suspension crossing index. -/
theorem measurable_taggedAdmittedSourceArrival_at_measurable_index
    (target k : Category)
    (index : StationaryAdmittedTargetPassiveTaggedInput target → ℤ)
    (hindex : Measurable index) :
    Measurable (fun z => taggedAdmittedSourceArrival target z (k, index z)) := by
  exact measurable_apply_of_measurable_countable_index
    (fun z n => taggedAdmittedSourceArrival target z (k, n))
    (fun n => measurable_taggedAdmittedSourceArrival target (k, n)) index hindex

/-- Reindexing a fixed-category source work mark at a measurable integer
label preserves measurability. -/
theorem measurable_taggedAdmittedSourceWork_at_measurable_index
    (target k : Category)
    (index : StationaryAdmittedTargetPassiveTaggedInput target → ℤ)
    (hindex : Measurable index) :
    Measurable (fun z => taggedAdmittedSourceWork target z (k, index z)) := by
  exact measurable_apply_of_measurable_countable_index
    (fun z n => taggedAdmittedSourceWork target z (k, n))
    (fun n => measurable_taggedAdmittedSourceWork target (k, n)) index hindex

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
