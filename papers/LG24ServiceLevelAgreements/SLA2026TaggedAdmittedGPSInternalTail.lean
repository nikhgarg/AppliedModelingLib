import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponseBounds
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalTailBound
import Mathlib.Tactic

/-!
# Internal tail inequality for the canonical literal GPS construction

The finite source construction now supplies both eventual facts required by
the canonical real-valued limsup argument: nonnegativity and domination by
the direct target comparator.  This proves the exponential tail inequality
for the internally defined canonical response.  Borel measurability of that
response remains a separate, deliberately visible obligation in
`SLA2026TaggedAdmittedGPSCanonicalTail`.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The internally constructed canonical GPS diagonal response has the
paper's exponential strict-tail upper bound.  This is an outer-measure tail
statement and intentionally does not claim Borel measurability or identify
the canonical limsup with a separately constructed stationary GPS process. -/
theorem stationaryAdmittedTargetGPSDiagonalResponse_strictTail_le_exp_of_gpsParameters
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay : ℝ)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 ≤ delay) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < stationaryAdmittedTargetGPSDiagonalResponse M G target z} ≤
      Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)) := by
  exact stationaryAdmittedTargetGPSDiagonalResponse_strictTail_le_exp_of_ae_eventually_bounds
    M G target delay hstable hdelay
    (ae_eventually_taggedAdmittedGPSDiagonalFiniteResponseTotal_nonneg M G target)
    (ae_eventually_taggedAdmittedGPSDiagonalFiniteResponseTotal_le_comparatorResponse
      M G target hstable)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
