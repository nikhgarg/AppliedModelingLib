import AppliedModelingLib.Queueing.MM1.Palm.CountCertificateBridge
import AppliedModelingLib.Queueing.MM1.GeometricStationary
import AppliedModelingLib.Queueing.MM1.Stationary

/-!
# Geometric stationary state laws in the Palm/PASTA M/M/1 bridge

This module converts an actual geometric stationary queue-state distribution
under a shift-invariant base law into the tail premise used by the tagged
M/M/1 response calculation.  It does not construct the invariant CTMC or
derive the Palm/PASTA identity.
-/

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory

namespace PalmPASTAQueueLengthCertificate

/-- A geometric stationary state law supplies the corresponding base queue tail. -/
theorem real_stationaryQueueLength_tail_of_geometric_hasLaw
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (rho : ℝ) (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1)
    (hstationary : HasLaw H.stationaryQueueLength
      (geometricMeasure (p := 1 - rho) (sub_pos.mpr hrho_lt_one)
        (sub_le_self 1 hrho_nonneg)) base.Pbase)
    (k : ℕ) :
    base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} = rho ^ k := by
  change (base.Pbase {ω | k ≤ H.stationaryQueueLength ω}).toReal = _
  rw [show base.Pbase {ω | k ≤ H.stationaryQueueLength ω} =
      (base.Pbase.map H.stationaryQueueLength) (Set.Ici k) by
        simpa only [Set.preimage_setOf_eq] using
          (Measure.map_apply H.stationaryQueueLength_measurable measurableSet_Ici).symm]
  rw [hstationary.map_eq]
  exact Queueing.measureReal_geometricMeasure_tail rho hrho_nonneg hrho_lt_one k

/--
Build the M/M/1 count certificate from a PASTA state law stated as an actual
geometric distribution, rather than as one tail equality for every index.
-/
def toTaggedPASTAMM1CountCertificateOfGeometricStateLaw
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
    (hstationary : HasLaw H.stationaryQueueLength
      (geometricMeasure (p := 1 - arrivalRate / service.rate)
        (sub_pos.mpr (Queueing.mm1TrafficIntensity_lt_one hstable service.rate_pos))
        (sub_le_self 1 (Queueing.mm1TrafficIntensity_nonneg
          (le_of_lt harrivalRate) service.rate_pos))) base.Pbase)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =
        {ω | service.count z.toNNReal ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  H.toTaggedPASTAMM1CountCertificate arrivalRate harrivalRate service hstable response
    hresponse_measurable
    (fun k => H.real_stationaryQueueLength_tail_of_geometric_hasLaw
      (arrivalRate / service.rate)
      (Queueing.mm1TrafficIntensity_nonneg (le_of_lt harrivalRate) service.rate_pos)
      (Queueing.mm1TrafficIntensity_lt_one hstable service.rate_pos) hstationary k)
    hpreArrivalQueueLength_indep_service hstrict_response_event hresponse_atom_zero

/--
Geometric-state-law constructor with an almost-everywhere response event
identity.  This matches chronological queue paths whose response/count
identity is proved up to tagged-law null sets.
-/
def toTaggedPASTAMM1CountCertificateOfGeometricStateLawAE
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
    (hstationary : HasLaw H.stationaryQueueLength
      (geometricMeasure (p := 1 - arrivalRate / service.rate)
        (sub_pos.mpr (Queueing.mm1TrafficIntensity_lt_one hstable service.rate_pos))
        (sub_le_self 1 (Queueing.mm1TrafficIntensity_nonneg
          (le_of_lt harrivalRate) service.rate_pos))) base.Pbase)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
        {ω | service.count z.toNNReal ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  H.toTaggedPASTAMM1CountCertificateAE arrivalRate harrivalRate service hstable response
    hresponse_measurable
    (fun k => H.real_stationaryQueueLength_tail_of_geometric_hasLaw
      (arrivalRate / service.rate)
      (Queueing.mm1TrafficIntensity_nonneg (le_of_lt harrivalRate) service.rate_pos)
      (Queueing.mm1TrafficIntensity_lt_one hstable service.rate_pos) hstationary k)
    hpreArrivalQueueLength_indep_service hstrict_response_event hresponse_atom_zero

end PalmPASTAQueueLengthCertificate

end AppliedModelingLib.Probability.Palm
