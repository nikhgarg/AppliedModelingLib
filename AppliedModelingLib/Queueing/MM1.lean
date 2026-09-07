import AppliedModelingLib.Queueing.MM1.AnalyticTail
import AppliedModelingLib.Queueing.MM1.Palm.CountCertificateBridge
import AppliedModelingLib.Queueing.MM1.Palm.IndependentProductTrajectory
import AppliedModelingLib.Queueing.MM1.Palm.SelectedMarkRate
import AppliedModelingLib.Queueing.MM1.PalmPASTA
import AppliedModelingLib.Queueing.MM1.PalmRenewalService
import AppliedModelingLib.Queueing.StationaryPerformance

/-!
# Stationary M/M/1 performance

This top-level queueing module exposes the mean tagged-response consequence of
the stationary M/M/1 Palm interface.  The underlying construction and
count-level argument remain in the probability foundations; queueing clients
can import this module for the resulting performance statement.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open MeasureTheory

namespace TaggedPASTAMM1CountCertificate

/-- A nonnegative tagged response in a certified stationary M/M/1 Palm model
has mean response time equal to the reciprocal spare capacity. -/
theorem integral_response_eq_inv_spareCapacity
    {Ω : Type*} [MeasurableSpace Ω] (H : TaggedPASTAMM1CountCertificate Ω)
    (hnonnegative : 0 ≤ᵐ[H.Ptag] H.response) :
    ∫ omega, H.response omega ∂H.Ptag = (H.serviceRate - H.arrivalRate)⁻¹ := by
  letI : IsProbabilityMeasure H.Ptag := H.isProbability
  exact AppliedModelingLib.Queueing.integral_eq_inv_of_exponential_responseTail_of_finite
    H.Ptag H.response (H.serviceRate - H.arrivalRate)
    H.response_measurable.aestronglyMeasurable hnonnegative
    (sub_pos.mpr H.stable)
    (fun t ht => H.strict_responseTail_eq t ht)

end TaggedPASTAMM1CountCertificate

end Queueing
end Probability
end AppliedModelingLib
