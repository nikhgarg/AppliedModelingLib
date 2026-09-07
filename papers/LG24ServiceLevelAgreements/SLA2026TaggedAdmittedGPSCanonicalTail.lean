import AppliedModelingLib.Foundations.Probability.EventuallyStableFiniteReplay
import AppliedModelingLib.Queueing.Core
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedSourceMeasurability
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorResponseLaw
import Mathlib.Tactic

/-!
# Canonical tail composition for the literal tagged GPS construction

This file defines the candidate GPS response directly from the total literal
diagonal executions.  It contains no reset selector: on the full-measure
source good carrier each finite replay is the executable source/fence
response, and the infinite-past response is their `limsup`.  Outside that
carrier the finite replay is explicitly totalized to zero.

The two remaining source obligations are intentionally visible at the final
tail theorem: Borel measurability of the finite executions, and their
eventual numerical domination by the direct target comparator.  Neither is
encoded in a model structure or inferred from a function name.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A total version of the literal `N`th diagonal GPS response.  The zero
branch is used only for inputs outside the already-proved source good carrier;
it is not a reset, an artificial queue state, or a replacement for the
literal source execution on the carrier where the construction is used. -/
noncomputable def taggedAdmittedGPSDiagonalFiniteResponseTotal
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (N : Nat) :
    StationaryAdmittedTargetPassiveTaggedInput target → ℝ :=
  by
    classical
    intro z
    exact if htarget_good : palmTaggedArrivalGoodCarrier z.1.1 then
      taggedAdmittedGPSDiagonalFiniteResponse target z htarget_good G.capacity G.weight N
    else 0

/-- A Borel proof for the total diagonal executor reduces exactly to a Borel
proof for its literal finite executor on the measurable Palm good carrier.
The theorem does not treat the carrier check as a free side condition: the
bad branch is the explicit zero totalization branch in the definition. -/
theorem measurable_taggedAdmittedGPSDiagonalFiniteResponseTotal_of_good_measurable
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (N : Nat)
    (hgood : Measurable (fun z : {z : StationaryAdmittedTargetPassiveTaggedInput target //
      palmTaggedArrivalGoodCarrier z.1.1} =>
        taggedAdmittedGPSDiagonalFiniteResponse target z.1 z.2
          G.capacity G.weight N)) :
    Measurable (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N) := by
  classical
  unfold taggedAdmittedGPSDiagonalFiniteResponseTotal
  exact Measurable.dite hgood measurable_const
    (measurableSet_taggedAdmittedTargetPalmGoodCarrier target)

/-- The source-defined tagged GPS response candidate: the canonical limsup of
the total literal finite diagonal executions. -/
noncomputable def stationaryAdmittedTargetGPSDiagonalResponse
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) :
    StationaryAdmittedTargetPassiveTaggedInput target → ℝ :=
  stabilizedFiniteReplayResponse
    (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target)

/-- Once the finite source/fence replays are Borel, their canonical diagonal
response is Borel as well.  This theorem deliberately asks for the actual
finite-executor Borel proof rather than treating finiteness as measurability. -/
theorem measurable_stationaryAdmittedTargetGPSDiagonalResponse_of_finite_measurable
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hfinite_measurable : ∀ N,
      Measurable (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N)) :
    Measurable (stationaryAdmittedTargetGPSDiagonalResponse M G target) := by
  exact measurable_stabilizedFiniteReplayResponse
    (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target) hfinite_measurable

/-- The strict tail of the canonical literal diagonal response follows from
eventual pathwise finite-replay domination by the direct target comparator.
The eventual nonnegativity premise is explicit because it is required by the
real-valued limsup order argument.  No reset time, completion witness, or
stationary GPS certificate is selected in this statement. -/
theorem stationaryAdmittedTargetGPSDiagonalResponse_strictTail_le_exp_of_ae_eventually_bounds
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay : ℝ)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 ≤ delay)
    (hnonneg : ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∀ᶠ N : Nat in atTop,
        0 ≤ taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z)
    (hbound : ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∀ᶠ N : Nat in atTop,
        taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z ≤
          stationaryAdmittedTargetPalmComparatorResponse target
            (G.capacity * G.weight target) z) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < stationaryAdmittedTargetGPSDiagonalResponse M G target z} ≤
      Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)) := by
  let tagged := M.stationaryAdmittedTargetPassiveTaggedInput target
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  have hresponse_le : stationaryAdmittedTargetGPSDiagonalResponse M G target ≤ᵐ[tagged.Ptag]
      stationaryAdmittedTargetPalmComparatorResponse target
        (G.capacity * G.weight target) := by
    simpa [tagged, stationaryAdmittedTargetGPSDiagonalResponse] using
      (ae_stabilizedFiniteReplayResponse_le_of_ae_eventually_nonneg_and_le
        tagged.Ptag (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target)
        (stationaryAdmittedTargetPalmComparatorResponse target
          (G.capacity * G.weight target)) hnonneg hbound)
  have hcomparator_tail :=
    M.stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_exp_of_gpsParameters
      G target delay hstable hdelay
  exact responseStrictTailReal_le_of_ae_response_le tagged.Ptag
    (stationaryAdmittedTargetGPSDiagonalResponse M G target)
    (stationaryAdmittedTargetPalmComparatorResponse target
      (G.capacity * G.weight target))
    delay
    (Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)))
    hresponse_le (le_of_eq (by simpa [tagged] using hcomparator_tail))

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
