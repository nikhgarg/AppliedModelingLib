import AppliedModelingLib.Queueing.Lindley.RemotePastCausalUniqueness
import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalPastReward
import Mathlib.Tactic

/-!
# Direct M/M/1 causal workload

This module defines the finite and remote-past workload replays of a
constant-rate FCFS queue driven by a two-sided marked renewal input.  It is a
generic queueing construction; its use for any particular stochastic model
requires an explicit input-law bridge.
-/

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section


/-! ## Canonical marked-renewal workload -/

/-! The constant-rate FCFS comparator on one literal two-sided
marked renewal input.  Its finite replays retain the physical predecessor
gaps and work marks exactly. -/
namespace MM1DirectCausal

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
bridge used to transport marked-renewal input approximants to the canonical direct
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
  | zero => simp [lateBatchPreWorkload]
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

/-- The tagged job's own work mark. -/
def tagWork (z : TwoSidedMarkedRenewalSample) : Real :=
  twoSidedGap 0 z.2

/-- The tag's work coordinate is measurable. -/
theorem measurable_tagWork : Measurable tagWork := by
  simpa [tagWork] using (measurable_twoSidedGap 0).comp measurable_snd

/-- The tagged constant-rate FCFS completion lag from the marked-renewal
input. -/
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
remote-past FCFS pre-tag workload almost surely.  This is a pathwise theorem,
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

/-- The canonical response has the finite literal replay value on
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

/-- On any coalescent direct input sample, the selected finite pre-tag
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
under its stable Poisson/exponential input law. -/
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

end MM1DirectCausal

end

end AppliedModelingLib.Queueing
