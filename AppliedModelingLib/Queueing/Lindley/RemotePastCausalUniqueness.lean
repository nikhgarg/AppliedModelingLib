import AppliedModelingLib.Queueing.Lindley.RemotePastInitialCoupling
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

/-!
# Causal-law uniqueness for remote-past Lindley recursions

The canonical remote-past Lindley solution is selected by empty-start replays.
This module provides the missing law-level uniqueness bridge: if a finite
nonnegative initial-state replay has a common law at every finite horizon,
then that law transfers to the canonical remote-past solution whenever the
input cumulative net work tends to `-∞` almost surely.

The result is generic.  It does not posit a stationary queue distribution,
and it does not identify any particular input or candidate law.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

noncomputable section

/-- The finite reversed replay from a specified pre-batch state at remote
index `N`, evaluated at the present. -/
def remotePastReplayFrom (initial : Real) (d : Nat -> Real) (N : Nat) : Real :=
  lindleyWorkloadFrom initial (reverseRemotePastIncrement d N) N

/-- The canonical finite empty-start replay from remote index `N`. -/
def remotePastEmptyReplay (d : Nat -> Real) (N : Nat) : Real :=
  lindleyWorkload (reverseRemotePastIncrement d N) N

/-- The totalized causal remote-past workload.  Under the negative-drift
hypothesis below, the defining limsup is eventually a literal finite replay. -/
noncomputable def remotePastCausalWorkload (d : Nat -> Real) : Real :=
  limsup (remotePastEmptyReplay d) atTop

/-- A global maximum of the outward cumulative path is a cutoff at which the
totalized causal workload is represented by one literal empty-start replay. -/
theorem remotePastCausalWorkload_eq_emptyReplay_of_global_cutoff
    (d : Nat -> Real) (K : Nat)
    (hmax : forall J,
      remotePastCumulativeNetInput d J <= remotePastCumulativeNetInput d K) :
    remotePastCausalWorkload d = remotePastEmptyReplay d K := by
  have hempty : ∀ N ≥ K,
      remotePastEmptyReplay d N = remotePastEmptyReplay d K := by
    intro N hKN
    have hcarried : (0 : Real) +
        (remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K) <= 0 := by
      simpa using (sub_nonpos.mpr (hmax N))
    have hcouple :=
      lindleyWorkloadFrom_reverseRemotePast_coalesces_at_present_of_global_cutoff
        (initial := (0 : Real)) d K N (by norm_num) hKN hmax hcarried
    change lindleyWorkload (reverseRemotePastIncrement d N) N =
      lindleyWorkload (reverseRemotePastIncrement d K) K
    calc
      lindleyWorkload (reverseRemotePastIncrement d N) N =
          lindleyWorkloadFrom 0 (reverseRemotePastIncrement d N) N :=
        congrFun (lindleyWorkload_eq_from_zero _) N
      _ = lindleyWorkload (reverseRemotePastIncrement d K) K := hcouple
  unfold remotePastCausalWorkload
  have heventually : ∀ᶠ M : Nat in atTop,
      remotePastEmptyReplay d M = remotePastEmptyReplay d K :=
    Filter.eventually_atTop.2 ⟨K, fun M hM => hempty M hM⟩
  calc
    limsup (remotePastEmptyReplay d) atTop =
        limsup (fun _ : Nat => remotePastEmptyReplay d K) atTop := by
          apply limsup_congr
          filter_upwards [heventually] with M hM
          exact hM
    _ = remotePastEmptyReplay d K := limsup_const _

theorem remotePastCausalWorkload_eq_emptyReplay_at_global_cutoff
    (d : Nat -> Real)
    (hlim : Tendsto (remotePastCumulativeNetInput d) atTop atBot) :
    ∃ K, ∀ N ≥ K,
      remotePastCausalWorkload d = remotePastEmptyReplay d K := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hmax⟩
  exact ⟨K, fun _ _ =>
    remotePastCausalWorkload_eq_emptyReplay_of_global_cutoff d K hmax⟩

/-- A finite nonnegative state placed sufficiently far in a negative-drift
remote past agrees exactly with the canonical causal workload at the present. -/
theorem eventually_remotePastReplayFrom_eq_causalWorkload_of_tendsto_atBot
    {initial : Real} (d : Nat -> Real) (hinitial : 0 <= initial)
    (hlim : Tendsto (remotePastCumulativeNetInput d) atTop atBot) :
    ∀ᶠ N : Nat in atTop,
      remotePastReplayFrom initial d N = remotePastCausalWorkload d := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hmax⟩
  have hcausal : remotePastCausalWorkload d = remotePastEmptyReplay d K := by
    exact remotePastCausalWorkload_eq_emptyReplay_of_global_cutoff d K hmax
  have htail : ∀ᶠ N : Nat in atTop,
      remotePastCumulativeNetInput d N <
        remotePastCumulativeNetInput d K - initial := by
    filter_upwards [Filter.tendsto_atBot.1 hlim
      (remotePastCumulativeNetInput d K - initial - 1)] with N hN
    linarith
  filter_upwards [htail,
    Filter.eventually_ge_atTop K] with N hN hKN
  have hcarried : initial +
      (remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K) <= 0 := by
    linarith
  have hcouple :=
    lindleyWorkloadFrom_reverseRemotePast_coalesces_at_present_of_global_cutoff
      d K N hinitial hKN hmax hcarried
  calc
    remotePastReplayFrom initial d N = remotePastEmptyReplay d K := by
      simpa [remotePastReplayFrom, remotePastEmptyReplay] using hcouple
    _ = remotePastCausalWorkload d := hcausal.symm

/-- The preceding pathwise coalescence lifted to an arbitrary source measure.
The initial state may depend on the sample; a real-valued state is finite by
construction, so no hidden integrability hypothesis is needed. -/
theorem ae_eventually_remotePastReplayFrom_eq_causalWorkload_of_tendsto_atBot
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (initial : Ω -> Real) (d : Ω -> Nat -> Real)
    (hinitial : ∀ᵐ ω ∂μ, 0 <= initial ω)
    (hlim : ∀ᵐ ω ∂μ,
      Tendsto (remotePastCumulativeNetInput (d ω)) atTop atBot) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : Nat in atTop,
      remotePastReplayFrom (initial ω) (d ω) N =
        remotePastCausalWorkload (d ω) := by
  filter_upwards [hinitial, hlim] with ω hinitω hlimω
  exact eventually_remotePastReplayFrom_eq_causalWorkload_of_tendsto_atBot
    (d ω) hinitω hlimω

/-- A generic common-law limit rule for an almost-surely eventually equal
sequence of measurable random variables.  This is the measure-level step
that turns remote-past coalescence into stationary-law uniqueness. -/
theorem hasLaw_of_ae_eventually_eq_of_all_hasLaw
    {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat -> Ω -> State) (Y : Ω -> State) (ν : Measure State)
    (hXmeas : ∀ n, Measurable (X n)) (hYmeas : Measurable Y)
    (hXlaw : ∀ n, HasLaw (X n) ν μ)
    (hXY : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop, X n ω = Y ω) :
    HasLaw Y ν μ := by
  refine ⟨hYmeas.aemeasurable, ?_⟩
  apply MeasureTheory.Measure.ext
  intro s hs
  have hindicator : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      ω ∈ (X n) ⁻¹' s ↔ ω ∈ Y ⁻¹' s := by
    filter_upwards [hXY] with ω hω
    filter_upwards [hω] with n hn
    simp only [Set.mem_preimage]
    rw [hn]
  have hmeasure : Tendsto (fun n : Nat => μ ((X n) ⁻¹' s)) atTop
      (nhds (μ (Y ⁻¹' s))) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (hYmeas hs) (fun n => hXmeas n hs) hindicator
  have hconstant : Tendsto (fun n : Nat => μ ((X n) ⁻¹' s)) atTop
      (nhds (ν s)) := by
    convert tendsto_const_nhds using 1
    funext n
    rw [← Measure.map_apply (hXmeas n) hs, (hXlaw n).map_eq]
  have heq : μ (Y ⁻¹' s) = ν s :=
    tendsto_nhds_unique hmeasure hconstant
  rw [Measure.map_apply hYmeas hs, heq]

/-- Law-level causal uniqueness for a remote-past Lindley construction.
To use this theorem, a concrete model supplies a common law for every finite
replay started from its candidate initial state.  The conclusion identifies
that candidate law with the literal remote-past causal solution; no separate
stationary-uniqueness axiom is used. -/
theorem hasLaw_remotePastCausalWorkload_of_all_replayLaws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (initial : Ω -> Real) (d : Ω -> Nat -> Real) (ν : Measure Real)
    (hinitial : ∀ᵐ ω ∂μ, 0 <= initial ω)
    (hlim : ∀ᵐ ω ∂μ,
      Tendsto (remotePastCumulativeNetInput (d ω)) atTop atBot)
    (hreplayMeas : ∀ n, Measurable (fun ω =>
      remotePastReplayFrom (initial ω) (d ω) n))
    (hcausalMeas : Measurable (fun ω => remotePastCausalWorkload (d ω)))
    (hreplayLaw : ∀ n, HasLaw
      (fun ω => remotePastReplayFrom (initial ω) (d ω) n) ν μ) :
    HasLaw (fun ω => remotePastCausalWorkload (d ω)) ν μ := by
  apply hasLaw_of_ae_eventually_eq_of_all_hasLaw μ
    (fun n ω => remotePastReplayFrom (initial ω) (d ω) n)
    (fun ω => remotePastCausalWorkload (d ω)) ν hreplayMeas hcausalMeas hreplayLaw
  exact ae_eventually_remotePastReplayFrom_eq_causalWorkload_of_tendsto_atBot
    μ initial d hinitial hlim

end

end AppliedModelingLib.Probability.Queueing
