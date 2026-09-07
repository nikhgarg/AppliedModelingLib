import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalTailBound
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSFutureSourceCompletion
import Mathlib.Tactic

/-!
# Selected-Palm remote-past semantics for the literal tagged GPS/FCFS response

The SLA source model first constructs a stationary direct-admitted input and
then views it from a selected target-class Palm arrival at physical time zero.
For that selected-Palm input, the literal finite executions on
`[-N, N + 1)` are already defined in
`SLA2026TaggedAdmittedGPSDiagonalResponse`: each replay starts empty, reads
the actual source-labelled target/passive batches, uses the executable GPS
segments and FCFS ledger, and scans the real source tag `(target, 0)`.

This file gives that construction a precise remote-past response semantics.
It deliberately separates two facts which must not be conflated:

* the response functional is the canonical `limsup` of those literal finite
  replays; and
* a proof that the replays eventually agree with a causal stationary output
  is a separate, explicit obligation.

The latter is exactly the point at which a physical global reset, the
source-labelled crossing refinement, and horizon-extension persistence must
be connected.  No existential reset selector, stationary-output certificate,
or name-based convention is used here.
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

/-- The selected-Palm response obtained from the literal GPS/FCFS remote-past
construction.  This is a definition by the concrete diagonal finite replays,
not a certificate that a separately postulated stationary queue has this
response.  Its domain is the actual target-Palm input whose passive streams
were recentered at the target's physical arrival epoch. -/
noncomputable def selectedPalmTaggedGPSFCFSRemotePastResponse
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) :
    StationaryAdmittedTargetPassiveTaggedInput target -> Real :=
  stationaryAdmittedTargetGPSDiagonalResponse M G target

/-- A candidate response has the literal selected-Palm remote-past semantics
when, almost surely, every sufficiently remote zero-start diagonal source
replay returns that candidate's value.  This is the semantic stabilization
obligation for the actual GPS/FCFS output.  It is intentionally stated in
terms of the concrete finite response, rather than an implementation name or
a hidden scheduler certificate. -/
def IsSelectedPalmTaggedGPSFCFSRemotePastResponse
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (response : StationaryAdmittedTargetPassiveTaggedInput target -> Real) : Prop :=
  ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
    ∀ᶠ N : Nat in atTop,
      taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z = response z

/-- The canonical remote-past response is exactly the previously constructed
canonical diagonal response.  The theorem is retained so downstream proofs
can cite the semantic name without unfolding an unrelated implementation
detail. -/
theorem selectedPalmTaggedGPSFCFSRemotePastResponse_eq_diagonalResponse
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) :
    selectedPalmTaggedGPSFCFSRemotePastResponse M G target =
      stationaryAdmittedTargetGPSDiagonalResponse M G target := rfl

/-- Any candidate satisfying the literal eventual-replay semantics agrees
almost surely with the canonical remote-past response.  This is the direct
bridge to the `limsup` definition; it does not choose a reset time. -/
theorem ae_selectedPalmTaggedGPSFCFSRemotePastResponse_eq_of_semantics
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (response : StationaryAdmittedTargetPassiveTaggedInput target -> Real)
    (hresponse : IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target response) :
    selectedPalmTaggedGPSFCFSRemotePastResponse M G target =ᵐ[
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag] response := by
  simpa [selectedPalmTaggedGPSFCFSRemotePastResponse,
    stationaryAdmittedTargetGPSDiagonalResponse] using
    (ae_stabilizedFiniteReplayResponse_eq_of_ae_eventually_eq
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag
      (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target) response hresponse)

/-- Once a literal causal response has been proved to stabilize the finite
replays, the canonical version itself satisfies the same semantic criterion.
This does not manufacture stabilization: `hresponse` remains an explicit
input, normally discharged from the physical-reset and trace-persistence
proofs. -/
theorem isSelectedPalmTaggedGPSFCFSRemotePastResponse_canonical_of_semantics
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (response : StationaryAdmittedTargetPassiveTaggedInput target -> Real)
    (hresponse : IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target response) :
    IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target
      (selectedPalmTaggedGPSFCFSRemotePastResponse M G target) := by
  filter_upwards [hresponse] with z hz
  have hcanonical :
      selectedPalmTaggedGPSFCFSRemotePastResponse M G target z = response z := by
    simpa [selectedPalmTaggedGPSFCFSRemotePastResponse,
      stationaryAdmittedTargetGPSDiagonalResponse] using
      (stabilizedFiniteReplayResponse_eq_of_eventually_eq
        (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target) response z hz)
  filter_upwards [hz] with N hN
  exact hN.trans hcanonical.symm

/-- The literal selected-Palm GPS/FCFS remote-past response satisfies its
own eventual-replay semantics.  Almost surely, a physical global reset and a
genuine future target source epoch produce a finite reset-start value; the
executable diagonal replays are eventually exactly that value.  The final
identification uses the canonical `limsup` definition only after this
pathwise scalar stabilization has been proved. -/
theorem isSelectedPalmTaggedGPSFCFSRemotePastResponse_canonical_of_physicalSourceStabilization
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) :
    IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target
      (selectedPalmTaggedGPSFCFSRemotePastResponse M G target) := by
  filter_upwards [
    M.ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_globalMax_and_targetRemoteStart
      G target,
    M.ae_taggedAdmittedFiniteExecutionInputStrictlyPositive target,
    M.ae_stationaryAdmittedTargetPassivePalmWorkAtZero_positive target] with
      z hreset hstrict_input htagged_work_pos
  rcases hreset with ⟨htarget_good, _hsource_work_nonneg, start, resetTime,
    remoteStart, hstart_reset, hstart_zero, hboundary, hreset_zero, hcoverage,
    hglobal, hclosed_workload⟩
  rcases hstrict_input with ⟨_hstrict_good, hsource_work_pos⟩
  rcases exists_eventually_taggedAdmittedGPSDiagonalFiniteResponse_eq_resetHorizonResponse_of_pastGlobalMax_futureSource
      M G target z htarget_good hsource_work_pos resetTime remoteStart hreset_zero
      hglobal hcoverage htagged_work_pos with
      ⟨completionHorizon, hdiagonal_stable⟩
  let stabilizedValue := taggedAdmittedFiniteGPSHorizonFenceTotalResponse
    resetTime completionHorizon target z htarget_good G.capacity G.weight
  have htotal_stable : ∀ᶠ N : Nat in atTop,
      taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N z = stabilizedValue := by
    filter_upwards [hdiagonal_stable] with N hN
    simpa only [taggedAdmittedGPSDiagonalFiniteResponseTotal, dif_pos htarget_good,
      stabilizedValue] using hN
  have hcanonical :
      selectedPalmTaggedGPSFCFSRemotePastResponse M G target z = stabilizedValue := by
    simpa [selectedPalmTaggedGPSFCFSRemotePastResponse,
      stationaryAdmittedTargetGPSDiagonalResponse] using
      (stabilizedFiniteReplayResponse_eq_of_eventually_eq
        (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target)
        (fun _ : StationaryAdmittedTargetPassiveTaggedInput target => stabilizedValue)
        z htotal_stable)
  filter_upwards [htotal_stable] with N hN
  exact hN.trans hcanonical.symm

/-- Measurability of an intended selected-Palm response follows from actual
finite replay measurability plus the explicit semantic stabilization proof.
No measurable reset or completion selector is required. -/
theorem aemeasurable_selectedPalmTaggedGPSFCFSResponse_of_semantics
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (response : StationaryAdmittedTargetPassiveTaggedInput target -> Real)
    (hfinite_measurable : forall N,
      Measurable (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N))
    (hresponse : IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target response) :
    AEMeasurable response (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  exact aemeasurable_response_of_ae_eventually_eq
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag
    (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target) response
    hfinite_measurable hresponse

/-- The actual source-labelled finite comparator bound transfers to any
selected-Palm response satisfying the explicit remote-past semantics.  In
particular, this uses the existing finite replay theorem rather than treating
the `limsup` name as a response comparison proof. -/
theorem ae_selectedPalmTaggedGPSFCFSResponse_le_comparator_of_semantics
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (response : StationaryAdmittedTargetPassiveTaggedInput target -> Real)
    (hresponse : IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target response)
    (hstable : M.admittedRate target < G.capacity * G.weight target) :
    response ≤ᵐ[(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag]
      stationaryAdmittedTargetPalmComparatorResponse target
        (G.capacity * G.weight target) := by
  filter_upwards [hresponse,
    ae_eventually_taggedAdmittedGPSDiagonalFiniteResponseTotal_le_comparatorResponse
      M G target hstable] with z hresponse_stable hbound
  exact response_le_of_eventually_eq_and_eventually_le
    (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target) response
    (stationaryAdmittedTargetPalmComparatorResponse target
      (G.capacity * G.weight target)) z hresponse_stable hbound

/-- The paper's strict exponential tail transfers to any literal selected-Palm
GPS/FCFS response once the physical replay-stabilization obligation has been
proved.  The hypothesis is semantic and source-labelled; it is not an opaque
stationary-output assumption. -/
theorem selectedPalmTaggedGPSFCFSResponse_strictTail_le_exp_of_semantics
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (response : StationaryAdmittedTargetPassiveTaggedInput target -> Real)
    (hresponse : IsSelectedPalmTaggedGPSFCFSRemotePastResponse M G target response)
    (delay : Real)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 <= delay) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < response z} <=
      Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)) := by
  let tagged := M.stationaryAdmittedTargetPassiveTaggedInput target
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  have hresponse_le :=
    ae_selectedPalmTaggedGPSFCFSResponse_le_comparator_of_semantics
      M G target response hresponse hstable
  have hcomparator_tail :=
    M.stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_exp_of_gpsParameters
      G target delay hstable hdelay
  exact responseStrictTailReal_le_of_ae_response_le tagged.Ptag response
    (stationaryAdmittedTargetPalmComparatorResponse target
      (G.capacity * G.weight target)) delay
    (Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)))
    (by simpa [tagged] using hresponse_le)
    (le_of_eq (by simpa [tagged] using hcomparator_tail))

/-- The constructed selected-Palm GPS/FCFS response has the paper's strict
exponential response-time tail.  This is the closed source-side consequence
of physical replay stabilization, rather than an externally supplied
stationary-response certificate. -/
theorem selectedPalmTaggedGPSFCFSRemotePastResponse_strictTail_le_exp_of_physicalSourceStabilization
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (delay : Real)
    (hstable : M.admittedRate target < G.capacity * G.weight target)
    (hdelay : 0 <= delay) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < selectedPalmTaggedGPSFCFSRemotePastResponse M G target z} <=
      Real.exp (-((G.capacity * G.weight target - M.admittedRate target) * delay)) := by
  exact selectedPalmTaggedGPSFCFSResponse_strictTail_le_exp_of_semantics
    M G target (selectedPalmTaggedGPSFCFSRemotePastResponse M G target)
    (isSelectedPalmTaggedGPSFCFSRemotePastResponse_canonical_of_physicalSourceStabilization
      M G target)
    delay hstable hdelay

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
