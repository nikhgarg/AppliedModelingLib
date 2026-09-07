import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Tactic

/-!
# Measurable transport from stable finite replays

This module isolates the final measure-theoretic step shared by causal
remote-past constructions.  A model supplies total measurable finite replay
responses indexed by `Nat`.  Their pointwise `limsup` is canonical and
measurable.  If the finite replays eventually agree with an intended response
almost everywhere, the intended response agrees almost everywhere with that
canonical version; if they are eventually bounded by a comparator, the same
tail bound follows without selecting a reset time or a completion witness.

The module deliberately does not supply finite replay functions, prove their
measurability, or select an existential witness.  Those are model-specific
obligations and must remain explicit at the call site.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical response induced by a sequence of total finite replay
responses.  Under eventual equality it is the eventual literal value. -/
noncomputable def stabilizedFiniteReplayResponse
    (finiteResponse : Nat → Ω → ℝ) : Ω → ℝ :=
  fun ω => limsup (fun n => finiteResponse n ω) atTop

/-- Total measurable finite replays give a measurable canonical response. -/
theorem measurable_stabilizedFiniteReplayResponse
    (finiteResponse : Nat → Ω → ℝ)
    (hfinite_measurable : ∀ n, Measurable (finiteResponse n)) :
    Measurable (stabilizedFiniteReplayResponse finiteResponse) := by
  unfold stabilizedFiniteReplayResponse
  exact Measurable.limsup hfinite_measurable

/-- On a sample where the finite responses are eventually constant at the
intended response, the canonical limsup has exactly that value. -/
theorem stabilizedFiniteReplayResponse_eq_of_eventually_eq
    (finiteResponse : Nat → Ω → ℝ) (response : Ω → ℝ) (ω : Ω)
    (hstabilizes : ∀ᶠ n : Nat in atTop, finiteResponse n ω = response ω) :
    stabilizedFiniteReplayResponse finiteResponse ω = response ω := by
  unfold stabilizedFiniteReplayResponse
  calc
    limsup (fun n => finiteResponse n ω) atTop =
        limsup (fun _ : Nat => response ω) atTop := by
          exact limsup_congr hstabilizes
    _ = response ω := limsup_const _

/-- A canonical finite-replay limsup is comparator-bounded whenever the
literal finite replays are eventually comparator-bounded.  This is the
right tail-transport result when the intended response is *defined* by the
remote-past limit: it does not require a separately selected reset or an
already-proved eventual-constancy theorem. -/
theorem stabilizedFiniteReplayResponse_le_of_eventually_le
    (finiteResponse : Nat → Ω → ℝ) (comparator : Ω → ℝ) (ω : Ω)
    (hnonneg : ∀ᶠ n : Nat in atTop, 0 ≤ finiteResponse n ω)
    (hbound : ∀ᶠ n : Nat in atTop, finiteResponse n ω ≤ comparator ω) :
    stabilizedFiniteReplayResponse finiteResponse ω ≤ comparator ω := by
  unfold stabilizedFiniteReplayResponse
  apply limsup_le_of_le
  · exact IsCoboundedUnder.of_frequently_ge hnonneg.frequently
  · exact hbound

/-- Almost-sure transport of an eventual nonnegative finite-replay bound to
the canonical limsup response.  Nonnegativity is explicit because it is the
order-theoretic lower-bound premise needed for a real-valued `limsup`; it is
not inferred from a response-time name. -/
theorem ae_stabilizedFiniteReplayResponse_le_of_ae_eventually_nonneg_and_le
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ) (comparator : Ω → ℝ)
    (hnonneg : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop, 0 ≤ finiteResponse n ω)
    (hbound : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω ≤ comparator ω) :
    stabilizedFiniteReplayResponse finiteResponse ≤ᵐ[μ] comparator := by
  filter_upwards [hnonneg, hbound] with ω hnonnegω hboundω
  exact stabilizedFiniteReplayResponse_le_of_eventually_le
    finiteResponse comparator ω hnonnegω hboundω

/-- Strict upper-tail transport for a canonical finite-replay response under
the explicit eventual nonnegativity and comparator-bound obligations. -/
theorem measure_setOf_lt_stabilizedFiniteReplayResponse_le_of_ae_eventually_nonneg_and_le
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ) (comparator : Ω → ℝ)
    (delay : ℝ)
    (hnonneg : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop, 0 ≤ finiteResponse n ω)
    (hbound : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω ≤ comparator ω) :
    μ {ω | delay < stabilizedFiniteReplayResponse finiteResponse ω} ≤
      μ {ω | delay < comparator ω} := by
  apply measure_mono_ae
  filter_upwards [
    ae_stabilizedFiniteReplayResponse_le_of_ae_eventually_nonneg_and_le
      μ finiteResponse comparator hnonneg hbound] with ω hω hdelay
  exact hdelay.trans_le hω

/-- Almost-sure eventual agreement identifies an intended response with the
canonical measurable finite-replay response. -/
theorem ae_stabilizedFiniteReplayResponse_eq_of_ae_eventually_eq
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ) (response : Ω → ℝ)
    (hstabilizes : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω) :
    stabilizedFiniteReplayResponse finiteResponse =ᵐ[μ] response := by
  filter_upwards [hstabilizes] with ω hω
  exact stabilizedFiniteReplayResponse_eq_of_eventually_eq
    finiteResponse response ω hω

/-- An intended response which almost surely stabilizes to total measurable
finite replays is almost-everywhere measurable. -/
theorem aemeasurable_response_of_ae_eventually_eq
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ) (response : Ω → ℝ)
    (hfinite_measurable : ∀ n, Measurable (finiteResponse n))
    (hstabilizes : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω) :
    AEMeasurable response μ := by
  exact (measurable_stabilizedFiniteReplayResponse finiteResponse
    hfinite_measurable).aemeasurable.congr
      (ae_stabilizedFiniteReplayResponse_eq_of_ae_eventually_eq
        μ finiteResponse response hstabilizes)

/-- The same finite-replay measurability conclusion needs only almost-everywhere
measurable finite approximants.  A countable intersection first replaces all
approximants by measurable representatives, then preserves their eventual
agreement with the intended response. -/
theorem aemeasurable_response_of_ae_eventually_eq_aemeasurable
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ) (response : Ω → ℝ)
    (hfinite : ∀ n, AEMeasurable (finiteResponse n) μ)
    (hstabilizes : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω) :
    AEMeasurable response μ := by
  let representative : Nat → Ω → ℝ := fun n => (hfinite n).mk (finiteResponse n)
  have hrepresentative : ∀ n, Measurable (representative n) := by
    intro n
    exact (hfinite n).measurable_mk
  have hae : ∀ᵐ ω ∂μ, ∀ n, finiteResponse n ω = representative n ω := by
    rw [ae_all_iff]
    intro n
    exact (hfinite n).ae_eq_mk
  apply aemeasurable_response_of_ae_eventually_eq μ representative response
    hrepresentative
  filter_upwards [hae, hstabilizes] with omega hrepresentativeEq hstabilizes
  filter_upwards [hstabilizes] with n hn
  exact (hrepresentativeEq n).symm.trans hn

/-- If an intended response is the eventual value of finite replays and the
same replays are eventually comparator-bounded, then the intended response
is comparator-bounded.  This argument uses one index in the intersection of
the two eventual events, so it imposes no global lower-bound hypothesis on
the finite replay sequence. -/
theorem response_le_of_eventually_eq_and_eventually_le
    (finiteResponse : Nat → Ω → ℝ)
    (response comparator : Ω → ℝ) (ω : Ω)
    (hstabilizes : ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω)
    (hbound : ∀ᶠ n : Nat in atTop,
      finiteResponse n ω ≤ comparator ω) :
    response ω ≤ comparator ω := by
  rcases (hstabilizes.and hbound).exists with ⟨n, hstable, hbound⟩
  rw [hstable] at hbound
  exact hbound

/-- The canonical limsup response is comparator-bounded whenever its finite
replays both stabilize to a response and are eventually comparator-bounded. -/
theorem stabilizedFiniteReplayResponse_le_of_eventually_eq_and_eventually_le
    (finiteResponse : Nat → Ω → ℝ)
    (response comparator : Ω → ℝ) (ω : Ω)
    (hstabilizes : ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω)
    (hbound : ∀ᶠ n : Nat in atTop,
      finiteResponse n ω ≤ comparator ω) :
    stabilizedFiniteReplayResponse finiteResponse ω ≤ comparator ω := by
  rw [stabilizedFiniteReplayResponse_eq_of_eventually_eq
    finiteResponse response ω hstabilizes]
  exact response_le_of_eventually_eq_and_eventually_le
    finiteResponse response comparator ω hstabilizes hbound

/-- The intended response is comparator-bounded almost surely whenever it is
the eventual value of the finite replays and those replays are eventually
comparator-bounded almost surely. -/
theorem ae_response_le_of_ae_eventually_eq_and_ae_eventually_le
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ)
    (response comparator : Ω → ℝ)
    (hstabilizes : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω)
    (hbound : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω ≤ comparator ω) :
    response ≤ᵐ[μ] comparator := by
  filter_upwards [hstabilizes, hbound] with ω hstabilizesω hboundω
  exact response_le_of_eventually_eq_and_eventually_le
    finiteResponse response comparator ω hstabilizesω hboundω

/-- The strict upper-tail mass of an intended response is bounded by that of
the comparator whenever both arise from the same eventually stable,
eventually bounded finite replay family.  No measurable selector for a reset
or a completion witness appears in the statement. -/
theorem measure_setOf_lt_response_le_of_ae_eventually_eq_and_ae_eventually_le
    (μ : Measure Ω) (finiteResponse : Nat → Ω → ℝ)
    (response comparator : Ω → ℝ) (delay : ℝ)
    (hstabilizes : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω = response ω)
    (hbound : ∀ᵐ ω ∂μ, ∀ᶠ n : Nat in atTop,
      finiteResponse n ω ≤ comparator ω) :
    μ {ω | delay < response ω} ≤ μ {ω | delay < comparator ω} := by
  apply measure_mono_ae
  filter_upwards [ae_response_le_of_ae_eventually_eq_and_ae_eventually_le
    μ finiteResponse response comparator hstabilizes hbound] with ω hω hdelay
  exact hdelay.trans_le hω

end

end AppliedModelingLib.Probability
