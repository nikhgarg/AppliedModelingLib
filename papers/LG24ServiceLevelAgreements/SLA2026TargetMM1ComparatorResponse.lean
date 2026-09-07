import LG24ServiceLevelAgreements.SLA2026TargetMM1RemotePast
import LG24ServiceLevelAgreements.SLA2026GPSParameters
import Mathlib.Tactic

/-!
# Literal target-Palm constant-rate FCFS comparator response

This module turns the source-defined remote-past scalar construction into the
tagged completion functional for the isolated target-class FCFS comparator.
The comparator uses exactly the direct admitted target arrivals and their iid
unit-mean exponential work marks.  Its state at the Palm epoch is defined by
the coalesced finite service-before-arrival recursions from the literal past;
the tag then receives its own literal work at the declared constant rate.

This is a source-facing path functional, not a tail calculation.  In
particular, it does not identify the functional's law with an exponential
law, does not invoke a uniformized carrier, and does not make a GPS
comparison.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

/-! ## Canonical direct marked-renewal comparator -/

/-! The source-free constant-rate FCFS comparator on one literal two-sided
marked renewal input.  It is kept separate from the SLA carrier so a later
tail proof has one exact direct-Poisson/Exponential functional to analyze. -/
namespace DirectMarkedRenewalComparator

/-- Literal work of the `n`th job before the tag, in outward past order. -/
def remotePastBatch (z : TwoSidedMarkedRenewalSample) (n : Nat) : Real :=
  markedRenewalPastWork z n

/-- Constant service accrued after that past job and before its newer
neighbour. -/
def remotePastService (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) (n : Nat) : Real :=
  serviceRate * markedRenewalPastGap z n

/-- The finite chronological replay of the literal past, evaluated just
before the tag at time zero.  The tagged job is deliberately not a batch of
this recursion. -/
def finitePreTagWorkload (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) (remoteStart : Nat) : Real :=
  lateBatchPreWorkload
    (reverseRemotePastIncrement (remotePastBatch z) remoteStart)
    (reverseRemotePastIncrement (remotePastService serviceRate z) remoteStart)
    remoteStart

/-- A finite late-batch replay is measurable whenever each supplied batch and
service coordinate is measurable.  This is the finite-horizon measurability
bridge used to transport literal source approximants to the canonical direct
marked-renewal law. -/
private theorem measurable_lateBatchPreWorkload_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (batch service : Nat → Ω → Real)
    (hbatch : ∀ n, Measurable (batch n))
    (hservice : ∀ n, Measurable (service n)) (n : Nat) :
    Measurable (fun ω =>
      lateBatchPreWorkload (fun i => batch i ω) (fun i => service i ω) n) := by
  have hpost : ∀ n : Nat, Measurable (fun ω =>
      lateBatchPostWorkload (fun i => batch i ω) (fun i => service i ω) n) := by
    intro m
    induction m with
    | zero =>
        simpa [lateBatchPostWorkload] using hbatch 0
    | succ m hm =>
        simpa [lateBatchPostWorkload, lateBatchUpdate] using
          ((hm.sub (hservice m)).max measurable_const).add (hbatch (m + 1))
  cases n with
  | zero => simpa [lateBatchPreWorkload] using (measurable_const : Measurable (fun _ : Ω => (0 : Real)))
  | succ n =>
      simpa [lateBatchPreWorkload] using
        ((hpost n).sub (hservice n)).max measurable_const

/-- Every literal past work coordinate of a marked-renewal sample is
measurable. -/
theorem measurable_remotePastBatch (n : Nat) :
    Measurable (fun z : TwoSidedMarkedRenewalSample => remotePastBatch z n) := by
  simpa [remotePastBatch, markedRenewalPastWork] using
    (measurable_twoSidedGap (Int.negSucc n)).comp measurable_snd

/-- Every literal past service amount at a fixed constant rate is measurable. -/
theorem measurable_remotePastService (serviceRate : Real) (n : Nat) :
    Measurable (fun z : TwoSidedMarkedRenewalSample =>
      remotePastService serviceRate z n) := by
  simpa [remotePastService, markedRenewalPastGap] using
    measurable_const.mul
      ((measurable_twoSidedGap (Int.negSucc n)).comp measurable_fst)

/-- Each finite direct marked-renewal pre-tag replay is measurable. -/
theorem measurable_finitePreTagWorkload (serviceRate : Real) (remoteStart : Nat) :
    Measurable (fun z : TwoSidedMarkedRenewalSample =>
      finitePreTagWorkload serviceRate z remoteStart) := by
  let batch : Nat → TwoSidedMarkedRenewalSample → Real :=
    fun i z => reverseRemotePastIncrement (remotePastBatch z) remoteStart i
  let service : Nat → TwoSidedMarkedRenewalSample → Real :=
    fun i z => reverseRemotePastIncrement (remotePastService serviceRate z) remoteStart i
  have hbatch : ∀ i, Measurable (batch i) := by
    intro i
    simpa [batch, reverseRemotePastIncrement] using
      (measurable_remotePastBatch (remoteStart - (i + 1)))
  have hservice : ∀ i, Measurable (service i) := by
    intro i
    simpa [service, reverseRemotePastIncrement] using
      (measurable_remotePastService serviceRate (remoteStart - (i + 1)))
  simpa [finitePreTagWorkload, batch, service] using
    (measurable_lateBatchPreWorkload_apply batch service hbatch hservice remoteStart)

/-- Coalescence of remote finite replays at the literal pre-tag state. -/
def PreTagCoalesces (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) : Prop :=
  ∃ K, ∀ N ≥ K,
    finitePreTagWorkload serviceRate z N = finitePreTagWorkload serviceRate z K

/-- The totalized coalesced pre-tag workload.  The fallback applies only off
the coalescence event; strict input stability proves that event almost surely. -/
noncomputable def preTagWorkload (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) : Real := by
  classical
  exact if h : PreTagCoalesces serviceRate z then
    finitePreTagWorkload serviceRate z (Nat.find h)
  else 0

/-- The source tag's own work mark. -/
def tagWork (z : TwoSidedMarkedRenewalSample) : Real :=
  twoSidedGap 0 z.2

/-- The direct source tag's work coordinate is measurable. -/
theorem measurable_tagWork : Measurable tagWork := by
  simpa [tagWork] using (measurable_twoSidedGap 0).comp measurable_snd

/-- The tagged constant-rate FCFS completion lag from the direct marked
renewal source. -/
noncomputable def response (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) : Real :=
  (preTagWorkload serviceRate z + tagWork z) / serviceRate

/-- A globally measurable version of the direct pre-tag workload, defined as
the limsup of the measurable finite remote-past replays.  On the proved
coalescence event it agrees with the selected finite value used by
`preTagWorkload`. -/
noncomputable def measurablePreTagWorkload (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) : Real :=
  limsup (fun n => finitePreTagWorkload serviceRate z n) atTop

/-- The limsup version of the direct tagged response. -/
noncomputable def measurableResponse (serviceRate : Real)
    (z : TwoSidedMarkedRenewalSample) : Real :=
  (measurablePreTagWorkload serviceRate z + tagWork z) / serviceRate

/-- Every finite direct tagged response approximation is measurable. -/
theorem measurable_finiteResponse (serviceRate : Real) (remoteStart : Nat) :
    Measurable (fun z : TwoSidedMarkedRenewalSample =>
      (finitePreTagWorkload serviceRate z remoteStart + tagWork z) / serviceRate) := by
  exact (measurable_finitePreTagWorkload serviceRate remoteStart).add measurable_tagWork |>.div
    measurable_const

/-- The limsup workload version is measurable because every finite replay is
measurable. -/
theorem measurable_measurablePreTagWorkload (serviceRate : Real) :
    Measurable (measurablePreTagWorkload serviceRate) := by
  unfold measurablePreTagWorkload
  exact Measurable.limsup
    (fun n => measurable_finitePreTagWorkload serviceRate n)

/-- The limsup direct response version is measurable. -/
theorem measurable_measurableResponse (serviceRate : Real) :
    Measurable (measurableResponse serviceRate) := by
  exact (measurable_measurablePreTagWorkload serviceRate).add measurable_tagWork |>.div
    measurable_const

/-- The direct remote-past net input has exactly the marked-renewal past
net-work convention. -/
theorem remotePastCumulativeNetInput_succ
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample) (n : Nat) :
    remotePastCumulativeNetInput
      (fun i => remotePastBatch z i - remotePastService serviceRate z i)
      (n + 1) =
      markedRenewalPastCumulativeNetWork serviceRate z n := by
  rfl

/-- Strictly stable direct Poisson/exponential input has a coalesced literal
remote-past FCFS pre-tag workload almost surely.  This is a source theorem,
not a stationary-tail or uniformization theorem. -/
theorem ae_preTagCoalesces_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      PreTagCoalesces serviceRate z := by
  have hneg : 1 - serviceRate / rate < 0 := by
    rw [sub_neg]
    exact (lt_div_iff₀ hrate).2 (by simpa using hstable)
  have hatBot : ∀ᵐ z ∂twoSidedMarkedRenewalMeasure rate,
      Tendsto
        (remotePastCumulativeNetInput
          (fun i => remotePastBatch z i - remotePastService serviceRate z i))
        atTop atBot := by
    filter_upwards [
      ae_tendsto_markedRenewalPastCumulativeNetWork_div_nat_succ hrate]
      with z hz
    have hsucc_atBot : Tendsto
        (fun n : Nat =>
          remotePastCumulativeNetInput
            (fun i => remotePastBatch z i - remotePastService serviceRate z i)
            (n + 1))
        atTop atBot := by
      have hrewrite :
          (fun n : Nat =>
            remotePastCumulativeNetInput
              (fun i => remotePastBatch z i - remotePastService serviceRate z i)
              (n + 1) / ((n + 1 : Nat) : Real)) =
            fun n : Nat =>
              markedRenewalPastCumulativeNetWork serviceRate z n /
                ((n + 1 : Nat) : Real) := by
        funext n
        rw [remotePastCumulativeNetInput_succ]
      have hratio : Tendsto
          (fun n : Nat =>
            remotePastCumulativeNetInput
              (fun i => remotePastBatch z i - remotePastService serviceRate z i)
              (n + 1) / ((n + 1 : Nat) : Real))
          atTop (nhds (1 - serviceRate / rate)) := by
        rw [hrewrite]
        exact hz
      exact tendsto_atBot_of_tendsto_div_nat_succ_neg _ _ hratio hneg
    exact tendsto_atBot_of_tendsto_succ_atBot _ hsucc_atBot
  filter_upwards [hatBot] with z hz
  rcases exists_lateBatchPreWorkload_reverseRemotePast_coalescence_at_present_of_tendsto_atBot
      (remotePastBatch z) (remotePastService serviceRate z) hz with ⟨K, hK⟩
  exact ⟨K, hK⟩

/-- On a coalescent sample, the totalized workload equals every sufficiently
remote finite replay. -/
theorem preTagWorkload_eq_finite_of_coalesces
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z) :
    ∃ K, ∀ N ≥ K,
      preTagWorkload serviceRate z = finitePreTagWorkload serviceRate z N := by
  classical
  refine ⟨Nat.find hcoal, ?_⟩
  intro N hN
  rw [preTagWorkload, dif_pos hcoal]
  exact (Nat.find_spec hcoal N hN).symm

/-- The direct canonical response has the finite literal replay value on
every sufficiently remote start whenever the pre-tag workload coalesces. -/
theorem response_eq_finite_of_coalesces
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z) :
    ∃ K, ∀ N ≥ K,
      response serviceRate z =
        (finitePreTagWorkload serviceRate z N + tagWork z) / serviceRate := by
  rcases preTagWorkload_eq_finite_of_coalesces serviceRate z hcoal with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro N hN
  simp only [response]
  rw [hK N hN]

/-- On any coalescent direct source sample, the selected finite pre-tag
workload agrees with its measurable limsup version. -/
theorem preTagWorkload_eq_measurablePreTagWorkload_of_coalesces
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z) :
    preTagWorkload serviceRate z = measurablePreTagWorkload serviceRate z := by
  rcases preTagWorkload_eq_finite_of_coalesces serviceRate z hcoal with ⟨K, hK⟩
  have heventually : ∀ᶠ N : Nat in atTop,
      finitePreTagWorkload serviceRate z N =
        finitePreTagWorkload serviceRate z K :=
    Filter.eventually_atTop.2 ⟨K, fun N hN => (hK N hN).symm.trans (hK K le_rfl)⟩
  calc
    preTagWorkload serviceRate z = finitePreTagWorkload serviceRate z K := hK K le_rfl
    _ = limsup (fun N => finitePreTagWorkload serviceRate z N) atTop := by
      symm
      calc
        limsup (fun N => finitePreTagWorkload serviceRate z N) atTop =
            limsup (fun _ : Nat => finitePreTagWorkload serviceRate z K) atTop :=
          limsup_congr heventually
        _ = finitePreTagWorkload serviceRate z K := limsup_const _
    _ = measurablePreTagWorkload serviceRate z := rfl

/-- On the direct coalescence event, the response functional agrees with its
globally measurable limsup version. -/
theorem response_eq_measurableResponse_of_coalesces
    (serviceRate : Real) (z : TwoSidedMarkedRenewalSample)
    (hcoal : PreTagCoalesces serviceRate z) :
    response serviceRate z = measurableResponse serviceRate z := by
  unfold response measurableResponse
  rw [preTagWorkload_eq_measurablePreTagWorkload_of_coalesces serviceRate z hcoal]

/-- Strictly stable direct input makes the original selected-response
functional agree almost surely with its measurable limsup version. -/
theorem ae_response_eq_measurableResponse_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    response serviceRate =ᵐ[twoSidedMarkedRenewalMeasure rate]
      measurableResponse serviceRate := by
  filter_upwards [ae_preTagCoalesces_of_rate_lt hrate hstable] with z hz
  exact response_eq_measurableResponse_of_coalesces serviceRate z hz

/-- The direct selected-response functional is almost-everywhere measurable
under its literal stable Poisson/exponential source law. -/
theorem aemeasurable_response_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    AEMeasurable (response serviceRate) (twoSidedMarkedRenewalMeasure rate) := by
  exact (measurable_measurableResponse serviceRate).aemeasurable.congr
    (ae_response_eq_measurableResponse_of_rate_lt hrate hstable).symm

/-- The direct marked-renewal response has its actual pushforward law under
strict input stability. -/
theorem response_hasLaw_of_rate_lt
    {rate serviceRate : Real} (hrate : 0 < rate) (hstable : rate < serviceRate) :
    HasLaw (response serviceRate)
      (Measure.map (response serviceRate) (twoSidedMarkedRenewalMeasure rate))
      (twoSidedMarkedRenewalMeasure rate) :=
  ⟨aemeasurable_response_of_rate_lt hrate hstable, rfl⟩

end DirectMarkedRenewalComparator

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal finite remote-past target workload immediately before the
Palm tag.  The `remoteStart` past jobs are replayed in chronological order;
there is no synthetic terminal batch at the tag. -/
def stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) : Real :=
  lateBatchPreWorkload
    (reverseRemotePastIncrement
      (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
    (reverseRemotePastIncrement
      (stationaryAdmittedTargetPalmRemotePastService target serviceRate z)
      remoteStart)
    remoteStart

/-- With no literal past job supplied, the finite replay is empty immediately
before the tag.  This records that the tag is not smuggled in as a terminal
batch of the remote-past recursion. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_zero
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z 0 = 0 := by
  simp [stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload,
    lateBatchPreWorkload]

/-- The final service interval of every nonempty remote-past replay is the
literal interval from the immediate predecessor to the Palm tag at zero. -/
theorem stationaryAdmittedTargetPalmRemotePastService_zero_eq_rate_mul_tag_sub_predecessor
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    stationaryAdmittedTargetPalmRemotePastService target serviceRate z 0 =
      serviceRate *
        (0 - candidatePalmArrival z.1.1 (Int.negSucc 0)) := by
  simpa [candidatePalmArrival_zero] using
    (stationaryAdmittedTargetPalmRemotePastService_eq_rate_mul_newerArrival_sub_arrival
      target serviceRate z 0)

/-- A finite remote-past replay followed by the tagged target job's own
literal work.  This is the target-only FCFS completion lag at constant work
rate `serviceRate`; jobs arriving after the tag do not affect this FCFS lag. -/
def stationaryAdmittedTargetPalmFiniteComparatorResponse
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) : Real :=
  (stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z remoteStart +
    stationaryAdmittedTargetPalmWorkAtZero target z) / serviceRate

/-- A zero-history tagged comparator response contains exactly the tag's own
literal work and no unrecorded past batch. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorResponse_zero
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    stationaryAdmittedTargetPalmFiniteComparatorResponse target serviceRate z 0 =
      stationaryAdmittedTargetPalmWorkAtZero target z / serviceRate := by
  simp [stationaryAdmittedTargetPalmFiniteComparatorResponse,
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_zero]

/-- The proposition that a finite remote-past replay has reached the
source-defined pre-tag workload.  It is kept explicit so the global
definition below has a total value even on the null exceptional inputs where
negative-drift coalescence has not been established. -/
def StationaryAdmittedTargetPalmComparatorPreTagCoalesces
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : Prop :=
  ∃ K, ∀ N ≥ K,
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z N =
      stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        target serviceRate z K

/-- The coalesced literal pre-tag workload of the target-only constant-rate
FCFS comparator.  The `0` fallback is only a totalization outside the
coalescence event; under strict target stability the theorem below proves
that event almost surely. -/
noncomputable def stationaryAdmittedTargetPalmComparatorPreTagWorkload
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : Real := by
  classical
  exact if h : StationaryAdmittedTargetPalmComparatorPreTagCoalesces
      target serviceRate z then
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z (Nat.find h)
  else 0

/-- The tagged target job's source-defined response functional in the
coalesced constant-rate FCFS comparator.  Since the target Palm epoch is
time zero, this is also its comparator completion time relative to the tag. -/
noncomputable def stationaryAdmittedTargetPalmComparatorResponse
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : Real :=
  (stationaryAdmittedTargetPalmComparatorPreTagWorkload target serviceRate z +
    stationaryAdmittedTargetPalmWorkAtZero target z) / serviceRate

/-- The SLA finite replay is definitionally the canonical direct marked
renewal replay of its retained target gap/work sample. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_eq_directMarkedRenewal
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z remoteStart =
      DirectMarkedRenewalComparator.finitePreTagWorkload serviceRate
        (stationaryAdmittedTargetPalmMarkedRenewalSample target z) remoteStart := by
  rfl

/-- The SLA finite tagged response is the corresponding finite direct
marked-renewal response on the retained target sample. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_directMarkedRenewal
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    stationaryAdmittedTargetPalmFiniteComparatorResponse
      target serviceRate z remoteStart =
      (DirectMarkedRenewalComparator.finitePreTagWorkload serviceRate
        (stationaryAdmittedTargetPalmMarkedRenewalSample target z) remoteStart +
        DirectMarkedRenewalComparator.tagWork
          (stationaryAdmittedTargetPalmMarkedRenewalSample target z)) / serviceRate := by
  rfl

/-- The source coalescence proposition is exactly the canonical direct
marked-renewal coalescence proposition on the retained target sample. -/
theorem stationaryAdmittedTargetPalmComparatorPreTagCoalesces_iff_directMarkedRenewal
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    StationaryAdmittedTargetPalmComparatorPreTagCoalesces target serviceRate z ↔
      DirectMarkedRenewalComparator.PreTagCoalesces serviceRate
        (stationaryAdmittedTargetPalmMarkedRenewalSample target z) := by
  rfl

/-- The coalesced SLA target pre-tag workload is exactly the direct canonical
marked-renewal functional. -/
theorem stationaryAdmittedTargetPalmComparatorPreTagWorkload_eq_directMarkedRenewal
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    stationaryAdmittedTargetPalmComparatorPreTagWorkload target serviceRate z =
      DirectMarkedRenewalComparator.preTagWorkload serviceRate
        (stationaryAdmittedTargetPalmMarkedRenewalSample target z) := by
  rfl

/-- The tagged SLA comparator response is exactly the canonical direct
Poisson/exponential marked-renewal response functional.  This is a literal
path identity, not a law-equivalence assertion about a uniformized carrier. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_eq_directMarkedRenewal
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    stationaryAdmittedTargetPalmComparatorResponse target serviceRate z =
      DirectMarkedRenewalComparator.response serviceRate
        (stationaryAdmittedTargetPalmMarkedRenewalSample target z) := by
  rfl

/-- At every finite remote start, the literal SLA target comparator response
has exactly the pushforward law of the same finite direct
Poisson/exponential marked-renewal functional.  This transports no
uniformized state or proxy workload. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorResponse_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (remoteStart : Nat) :
    HasLaw
      (fun z => stationaryAdmittedTargetPalmFiniteComparatorResponse
        target serviceRate z remoteStart)
      (Measure.map
        (fun x : TwoSidedMarkedRenewalSample =>
          (DirectMarkedRenewalComparator.finitePreTagWorkload
            serviceRate x remoteStart +
            DirectMarkedRenewalComparator.tagWork x) / serviceRate)
        (twoSidedMarkedRenewalMeasure (M.admittedRate target)))
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  let f : TwoSidedMarkedRenewalSample → Real := fun x =>
    (DirectMarkedRenewalComparator.finitePreTagWorkload
      serviceRate x remoteStart + DirectMarkedRenewalComparator.tagWork x) / serviceRate
  have hf : Measurable f := by
    simpa [f] using
      (DirectMarkedRenewalComparator.measurable_finiteResponse serviceRate remoteStart)
  have hsource := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  have hsample : Measurable (stationaryAdmittedTargetPalmMarkedRenewalSample target) :=
    measurable_fst
  have hfunc :
      (fun z => stationaryAdmittedTargetPalmFiniteComparatorResponse
        target serviceRate z remoteStart) =
        f ∘ stationaryAdmittedTargetPalmMarkedRenewalSample target := by
    funext z
    simpa [f, Function.comp_apply] using
      (stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_directMarkedRenewal
        target serviceRate z remoteStart)
  refine ⟨?_, ?_⟩
  · rw [hfunc]
    exact hf.aemeasurable.comp_aemeasurable hsample.aemeasurable
  · rw [hfunc, ← Measure.map_map hf hsample, hsource.map_eq]

/-- Under strictly stable direct target load, the SLA tagged comparator
response has exactly the pushforward law of the canonical direct
Poisson/exponential marked-renewal response functional.  This is the
source-law bridge required before any analytic response-tail proof; it is not
a bridge to the legacy uniformized carrier. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_hasLaw_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    HasLaw
      (stationaryAdmittedTargetPalmComparatorResponse target serviceRate)
      (Measure.map (DirectMarkedRenewalComparator.response serviceRate)
        (twoSidedMarkedRenewalMeasure (M.admittedRate target)))
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  have hdirect := DirectMarkedRenewalComparator.response_hasLaw_of_rate_lt
    (M.admittedRate_pos target) hstable
  have hsource := M.stationaryAdmittedTargetPalmMarkedRenewalSample_hasLaw target
  refine (hdirect.comp hsource).congr ?_
  filter_upwards [] with z
  simpa [Function.comp_apply] using
    (stationaryAdmittedTargetPalmComparatorResponse_eq_directMarkedRenewal
      target serviceRate z)

/-- The source-facing comparator response is almost-everywhere measurable
under the actual stable target-Palm law. -/
theorem aemeasurable_stationaryAdmittedTargetPalmComparatorResponse_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    AEMeasurable (stationaryAdmittedTargetPalmComparatorResponse target serviceRate)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag :=
  (M.stationaryAdmittedTargetPalmComparatorResponse_hasLaw_of_admittedRate_lt
    target serviceRate hstable).aemeasurable

/-- Every measurable response-event property transports exactly between the
literal SLA target-Palm comparator and the canonical direct marked-renewal
response.  This is the usable event-level reduction for the remaining
analytic tail theorem. -/
theorem ae_stationaryAdmittedTargetPalmComparatorResponse_iff_directMarkedRenewal_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate)
    (p : Real → Prop) (hp : Measurable p) :
    (∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      p (stationaryAdmittedTargetPalmComparatorResponse target serviceRate z)) ↔
      ∀ᵐ x ∂twoSidedMarkedRenewalMeasure (M.admittedRate target),
        p (DirectMarkedRenewalComparator.response serviceRate x) := by
  have hsource := M.stationaryAdmittedTargetPalmComparatorResponse_hasLaw_of_admittedRate_lt
    target serviceRate hstable
  have hdirect := DirectMarkedRenewalComparator.response_hasLaw_of_rate_lt
    (M.admittedRate_pos target) hstable
  exact (hsource.ae_iff hp).trans (hdirect.ae_iff hp).symm

/-- The strict response-tail mass of the literal SLA target comparator is
exactly the strict-tail mass of the canonical direct marked-renewal response.
This is a transport equality only: it deliberately does not insert the still
unproved exponential formula on the right-hand side. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_strictTail_eq_directMarkedRenewal_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate delay : Real) (hstable : M.admittedRate target < serviceRate) :
    (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      {z | delay < stationaryAdmittedTargetPalmComparatorResponse target serviceRate z} =
      (twoSidedMarkedRenewalMeasure (M.admittedRate target)).real
        {x | delay < DirectMarkedRenewalComparator.response serviceRate x} := by
  have hsource := M.stationaryAdmittedTargetPalmComparatorResponse_hasLaw_of_admittedRate_lt
    target serviceRate hstable
  have hdirect := DirectMarkedRenewalComparator.response_hasLaw_of_rate_lt
    (M.admittedRate_pos target) hstable
  change (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
      ((stationaryAdmittedTargetPalmComparatorResponse target serviceRate) ⁻¹'
        Set.Ioi delay) =
      (twoSidedMarkedRenewalMeasure (M.admittedRate target)).real
        ((DirectMarkedRenewalComparator.response serviceRate) ⁻¹' Set.Ioi delay)
  change ((M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag
      ((stationaryAdmittedTargetPalmComparatorResponse target serviceRate) ⁻¹'
        Set.Ioi delay)).toReal =
      ((twoSidedMarkedRenewalMeasure (M.admittedRate target))
        ((DirectMarkedRenewalComparator.response serviceRate) ⁻¹' Set.Ioi delay)).toReal
  apply congrArg ENNReal.toReal
  rw [← Measure.map_apply_of_aemeasurable hsource.aemeasurable measurableSet_Ioi,
    hsource.map_eq,
    Measure.map_apply_of_aemeasurable hdirect.aemeasurable measurableSet_Ioi]

/-- A target-local GPS slack condition supplies the exact source condition
for the direct target response-law bridge at its guaranteed service rate. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_hasLaw_of_gpsParameters
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hstable : M.admittedRate target < G.capacity * G.weight target) :
    HasLaw
      (stationaryAdmittedTargetPalmComparatorResponse
        target (G.capacity * G.weight target))
      (Measure.map
        (DirectMarkedRenewalComparator.response (G.capacity * G.weight target))
        (twoSidedMarkedRenewalMeasure (M.admittedRate target)))
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  exact M.stationaryAdmittedTargetPalmComparatorResponse_hasLaw_of_admittedRate_lt
    target (G.capacity * G.weight target) hstable

/-- Every finite target comparator pre-tag workload is nonnegative. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    0 ≤ stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z remoteStart := by
  exact lateBatchPreWorkload_nonneg _ _ _

/-- The totalized coalesced target comparator workload is nonnegative even
before imposing its almost-sure stability condition. -/
theorem stationaryAdmittedTargetPalmComparatorPreTagWorkload_nonneg
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    0 ≤ stationaryAdmittedTargetPalmComparatorPreTagWorkload
      target serviceRate z := by
  classical
  unfold stationaryAdmittedTargetPalmComparatorPreTagWorkload
  split_ifs with h
  · exact stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
      target serviceRate z _
  · norm_num

/-- The tagged comparator completion-lag functional has exactly its declared
work-over-rate form whenever the comparison rate is nonzero. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_mul_serviceRate
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hserviceRate : serviceRate ≠ 0) :
    stationaryAdmittedTargetPalmComparatorResponse target serviceRate z * serviceRate =
      stationaryAdmittedTargetPalmComparatorPreTagWorkload target serviceRate z +
        stationaryAdmittedTargetPalmWorkAtZero target z := by
  unfold stationaryAdmittedTargetPalmComparatorResponse
  field_simp

/-- On every sample where the literal remote-past construction coalesces,
the totalized workload equals every sufficiently remote finite replay. -/
theorem stationaryAdmittedTargetPalmComparatorPreTagWorkload_eq_finite_of_coalesces
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hcoal : StationaryAdmittedTargetPalmComparatorPreTagCoalesces
      target serviceRate z) :
    ∃ K, ∀ N ≥ K,
      stationaryAdmittedTargetPalmComparatorPreTagWorkload target serviceRate z =
        stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
          target serviceRate z N := by
  classical
  refine ⟨Nat.find hcoal, ?_⟩
  intro N hN
  rw [stationaryAdmittedTargetPalmComparatorPreTagWorkload, dif_pos hcoal]
  exact (Nat.find_spec hcoal N hN).symm

/-- The direct target source's negative drift supplies the coalescence event
for the literal target-only FCFS comparator almost surely. -/
theorem ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      StationaryAdmittedTargetPalmComparatorPreTagCoalesces
        target serviceRate z := by
  filter_upwards [
    M.ae_exists_stationaryAdmittedTargetPalmRemotePastComparatorCoalescence_of_admittedRate_lt
      target serviceRate hstable] with z hz
  exact hz

/-- Target-local GPS slack instantiates the direct target comparator at its
guaranteed GPS rate. -/
theorem ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_gpsParameters
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hstable : M.admittedRate target < G.capacity * G.weight target) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      StationaryAdmittedTargetPalmComparatorPreTagCoalesces
        target (G.capacity * G.weight target) z := by
  exact M.ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_admittedRate_lt
    target (G.capacity * G.weight target) hstable

/-- Under strict target stability, the coalesced pre-tag workload agrees
almost surely with every sufficiently remote literal finite replay. -/
theorem ae_exists_stationaryAdmittedTargetPalmComparatorPreTagWorkload_eq_finite_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ K, ∀ N ≥ K,
        stationaryAdmittedTargetPalmComparatorPreTagWorkload target serviceRate z =
          stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
            target serviceRate z N := by
  filter_upwards [
    M.ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_admittedRate_lt
      target serviceRate hstable] with z hz
  exact stationaryAdmittedTargetPalmComparatorPreTagWorkload_eq_finite_of_coalesces
    target serviceRate z hz

/-- On the source coalescence event, the tagged comparator response is the
same finite-history FCFS response for every sufficiently remote start. -/
theorem stationaryAdmittedTargetPalmComparatorResponse_eq_finite_of_coalesces
    (target : Category) (serviceRate : Real)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hcoal : StationaryAdmittedTargetPalmComparatorPreTagCoalesces
      target serviceRate z) :
    ∃ K, ∀ N ≥ K,
      stationaryAdmittedTargetPalmComparatorResponse target serviceRate z =
        stationaryAdmittedTargetPalmFiniteComparatorResponse
          target serviceRate z N := by
  rcases stationaryAdmittedTargetPalmComparatorPreTagWorkload_eq_finite_of_coalesces
    target serviceRate z hcoal with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro N hN
  simp only [stationaryAdmittedTargetPalmComparatorResponse,
    stationaryAdmittedTargetPalmFiniteComparatorResponse]
  rw [hK N hN]

/-- Under strictly stable direct target load, the tagged source has an
almost-sure, finite-history-independent constant-rate FCFS response
functional.  This is the direct-source comparator object needed by a future
distributional tail proof. -/
theorem ae_exists_stationaryAdmittedTargetPalmComparatorResponse_eq_finite_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ K, ∀ N ≥ K,
        stationaryAdmittedTargetPalmComparatorResponse target serviceRate z =
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target serviceRate z N := by
  filter_upwards [
    M.ae_stationaryAdmittedTargetPalmComparatorPreTagCoalesces_of_admittedRate_lt
      target serviceRate hstable] with z hz
  exact stationaryAdmittedTargetPalmComparatorResponse_eq_finite_of_coalesces
    target serviceRate z hz

/-- Under target-local GPS slack, the target's literal direct-source FCFS
comparator response is independent of all sufficiently remote finite replay
starts almost surely. -/
theorem ae_exists_stationaryAdmittedTargetPalmComparatorResponse_eq_finite_of_gpsParameters
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hstable : M.admittedRate target < G.capacity * G.weight target) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ K, ∀ N ≥ K,
        stationaryAdmittedTargetPalmComparatorResponse
          target (G.capacity * G.weight target) z =
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z N := by
  exact M.ae_exists_stationaryAdmittedTargetPalmComparatorResponse_eq_finite_of_admittedRate_lt
    target (G.capacity * G.weight target) hstable

/-- Strict direct target stability makes the declared comparison rate positive,
and the source tag has positive work almost surely.  Therefore the literal
constant-rate FCFS comparator response is strictly positive almost surely. -/
theorem ae_stationaryAdmittedTargetPalmComparatorResponse_pos_of_admittedRate_lt
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (serviceRate : Real) (hstable : M.admittedRate target < serviceRate) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      0 < stationaryAdmittedTargetPalmComparatorResponse target serviceRate z := by
  have hserviceRate : 0 < serviceRate :=
    lt_trans (M.admittedRate_pos target) hstable
  filter_upwards [M.ae_stationaryAdmittedTargetPassivePalmWorkAtZero_positive target]
    with z htagwork
  unfold stationaryAdmittedTargetPalmComparatorResponse
  exact div_pos
    (add_pos_of_nonneg_of_pos
    (stationaryAdmittedTargetPalmComparatorPreTagWorkload_nonneg
        target serviceRate z) htagwork)
    hserviceRate

/-- Target-local GPS slack makes the direct target comparator's tagged
response strictly positive almost surely. -/
theorem ae_stationaryAdmittedTargetPalmComparatorResponse_pos_of_gpsParameters
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category)
    (hstable : M.admittedRate target < G.capacity * G.weight target) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      0 < stationaryAdmittedTargetPalmComparatorResponse
        target (G.capacity * G.weight target) z := by
  exact M.ae_stationaryAdmittedTargetPalmComparatorResponse_pos_of_admittedRate_lt
    target (G.capacity * G.weight target) hstable

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
