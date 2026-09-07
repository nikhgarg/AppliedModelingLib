import LG24ServiceLevelAgreements.SLA2026Queueing
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalMeasurability
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSStationaryPalmSemantics
import Mathlib.Tactic

/-!
# Source-facing SLA consequences of the constructed stationary GPS response

The source's response-time display concerns a typical admitted request.  This
module packages that display around the literal selected-Palm GPS/FCFS
response, then proves the printed admitted- and all-request SLA arithmetic.
It deliberately does not turn the tail inequality into a caller-supplied
``cited'' proposition: the only conditional theorem here is a reusable
algebraic consequence of an explicitly supplied response-tail fact.  The
construction theorem that discharges that fact belongs with the stationary
GPS replay construction.
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

/-- The exact source-facing response-tail assertion for a typical admitted
target-class request.  Its response is the concrete selected-Palm remote-past
GPS/FCFS functional, and measurability is part of the assertion rather than a
property inferred from a scheduler name. -/
def SLA2026StationaryGPSResponseTail
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay : Real) : Prop :=
  Measurable (selectedPalmTaggedGPSFCFSRemotePastResponse M G target) /\
    IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target
      (selectedPalmTaggedGPSFCFSRemotePastResponse M G target) /\
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < selectedPalmTaggedGPSFCFSRemotePastResponse M G target z} <=
      Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay))

/-- The two genuine construction obligations compose directly into the
source-facing stationary tail: finite literal replays must be Borel and the
same literal replays must stabilize to the selected-Palm remote-past response.
Neither fact is hidden in the tail predicate or inferred from a function
name. -/
theorem stationaryGPSResponseTail_of_finiteMeasurable_and_semantics
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hfinite_measurable : forall N,
      Measurable (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N))
    (hsemantics : IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target
      (selectedPalmTaggedGPSFCFSRemotePastResponse M G target))
    (delay : Real)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 <= delay) :
    SLA2026StationaryGPSResponseTail M G target delay := by
  refine ⟨?_, hsemantics, ?_⟩
  · simpa [selectedPalmTaggedGPSFCFSRemotePastResponse] using
      (measurable_stationaryAdmittedTargetGPSDiagonalResponse_of_finite_measurable
        M G target hfinite_measurable)
  · exact selectedPalmTaggedGPSFCFSResponse_strictTail_le_exp_of_semantics
      M G target (selectedPalmTaggedGPSFCFSRemotePastResponse M G target)
      hsemantics delay hstable hdelay

/-- The literal selected-Palm GPS/FCFS construction supplies the complete
source-facing stationary response tail: every finite diagonal replay is
Borel, and physical global-reset stabilization identifies its canonical
remote-past response.  No cited tail certificate, stationary-output
selector, or caller-supplied replay semantics remains. -/
theorem stationaryGPSResponseTail_of_physicalSourceStabilization
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay : Real)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 <= delay) :
    SLA2026StationaryGPSResponseTail M G target delay := by
  exact stationaryGPSResponseTail_of_finiteMeasurable_and_semantics
    M G target
    (fun N => measurable_taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N)
    (isSelectedPalmTaggedGPSFCFSRemotePastResponse_canonical_of_physicalSourceStabilization
      M G target)
    delay hstable hdelay

/-- The source logarithmic SLA constraint turns the constructed typical
admitted-request tail into the advertised admitted tail probability target. -/
theorem sla2026_stationary_gps_tail_implies_admitted_sla
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay alpha : Real)
    (htail : SLA2026StationaryGPSResponseTail M G target delay)
    (halpha : 0 < alpha)
    (hsla : sla2026SufficientSLAConstraint
      (G.capacity * G.weight target - M.admittedRate target) delay alpha) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < selectedPalmTaggedGPSFCFSRemotePastResponse M G target z} <= alpha := by
  exact sla2026_cited_gps_tail_implies_admitted_sla htail.2.2 halpha hsla

/-- The source's independent-admission rate fraction transfers the
admitted-request SLA conclusion to its displayed all-request rate-fraction
expression.  This is the deterministic intensity calculation after the actual
Palm tail has been supplied.  It does not purport to prove a separate raw-path
or empirical-frequency coupling, which the source does not state as a named
theorem. -/
theorem sla2026_stationary_gps_tail_implies_all_request_sla
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay alpha : Real)
    (htail : SLA2026StationaryGPSResponseTail M G target delay)
    (halpha : 0 < alpha)
    (hsla : sla2026SufficientSLAConstraint
      (G.capacity * G.weight target - M.admittedRate target) delay alpha) :
    M.admittedRate target / M.arrivalRate target * (1 - alpha) <=
      sla2026AllRequestResponseFraction
        (M.arrivalRate target) (M.admittedRate target)
        ((M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
          {z | delay < selectedPalmTaggedGPSFCFSRemotePastResponse M G target z}) := by
  exact sla2026_admitted_tail_implies_all_request_sla
    (M.arrivalRate_pos target)
    (M.admittedRate_pos target).le
    (sla2026_stationary_gps_tail_implies_admitted_sla
      M G target delay alpha htail halpha hsla)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
