import LBG24SpatialUnderreporting.ConditionOneTail
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Forward selection and endpoint-density semantics for Appendix Theorem 2

This module states the missing *model semantics* between the source's informal
continuous point-probability notation and a future stochastic proof of its
Eq. (8). It deliberately covers only the start-selection and endpoint pieces:
the ordered observed-jump data density remains a separate obligation.

In particular, this is not an Eq. (8) proof certificate. A full theorem must
still construct a rate-indexed model, connect the canonical forward Poisson
path to measurable finite report histories, and derive the ordered-jump
conditional density from that model.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
A standard-Borel carrier for a finite ordered report prefix. The first field is
the number of active arrival coordinates; the infinite stream is a measurable
padded representation, of which only indices below that count are observed.

Using a padded stream avoids the missing `StandardBorelSpace` instance for the
dependent finite-vector sigma type while preserving the source's finite report
data exactly at its active coordinates.
-/
abbrev RawFiniteArrivalHistory := ℕ × (ℕ → ℝ)

/-- The selected start paired with the raw finite observed-arrival prefix. -/
abbrev SelectedRawFiniteArrivalHistory := ℝ≥0 × RawFiniteArrivalHistory

/-- The first `n` canonical arrival epochs as a measurable finite vector. -/
def firstCanonicalArrivalVector (n : ℕ) : (ℕ → ℝ) → Fin n → ℝ :=
  fun ω i => arrivalTime i.1 ω

theorem measurable_firstCanonicalArrivalVector (n : ℕ) :
    Measurable (firstCanonicalArrivalVector n) := by
  exact measurable_pi_iff.2 fun i => measurable_arrivalTime i.1

/--
The measured arrival data available at a supplied endpoint: an active count
followed by the canonical arrival stream. This is an observed-data coordinate,
not yet the pre-end history required to condition the endpoint itself.
-/
def rawCanonicalArrivalHistory
    (endTime : (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → RawFiniteArrivalHistory :=
  fun ω => (canonicalRenewalCount (endTime ω) ω, fun i => arrivalTime i ω)

theorem measurable_rawCanonicalArrivalHistory
    (endTime : (ℕ → ℝ) → ℝ) (hendTime : Measurable endTime) :
    Measurable (rawCanonicalArrivalHistory endTime) := by
  exact
    (measurable_canonicalRenewalCount_joint.comp
      (hendTime.prodMk measurable_id)).prodMk
    (measurable_pi_iff.2 fun i => measurable_arrivalTime i)

/-- The selected start together with the measured raw arrival-data coordinate. -/
def selectedRawCanonicalArrivalHistory
    (startTime : (ℕ → ℝ) → ℝ≥0) (endTime : (ℕ → ℝ) → ℝ) :
    (ℕ → ℝ) → SelectedRawFiniteArrivalHistory :=
  fun ω => (startTime ω, rawCanonicalArrivalHistory endTime ω)

theorem measurable_selectedRawCanonicalArrivalHistory
    (startTime : (ℕ → ℝ) → ℝ≥0) (endTime : (ℕ → ℝ) → ℝ)
    (hstartTime : Measurable startTime) (hendTime : Measurable endTime) :
    Measurable (selectedRawCanonicalArrivalHistory startTime endTime) :=
  hstartTime.prodMk (measurable_rawCanonicalArrivalHistory endTime hendTime)

/--
The source-faithful start/endpoint portion of a forward Appendix-Theorem-2
model at one Poisson rate.

`history` is intentionally abstract here. A later construction will use a
measurable finite report-history coordinate, including the selected start and
the relevant ordered arrivals. The conditional-distribution fields express
Condition 2 as regular conditional laws and densities, rather than as literal
probabilities of exact continuous endpoint values.
-/
structure ForwardTheorem2SelectionEndpointDensityModel
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tail : Type*) [MeasurableSpace Tail]
    (History : Type*) [MeasurableSpace History] [StandardBorelSpace History]
    [Nonempty History]
    (startReference : Measure ℝ≥0) [SFinite startReference] where
  /-- The actual forward Poisson count process for this fixed-rate model. -/
  forward : ForwardHomogeneousPoissonCountingProcessByLaw Ω P
  /-- Condition 1's conditional start-selection kernel and future-tail independence. -/
  conditionOne : Theorem2ConditionOneSelection Ω P Tail

  /-- Measurable finite report information on which the endpoint policy may depend. -/
  history : Ω → History
  history_measurable : Measurable history
  /-- The selected start recovered from that endpoint history. -/
  historyStart : History → ℝ
  historyStart_measurable : Measurable historyStart
  historyStart_eq_start : ∀ᵐ ω ∂P,
    historyStart (history ω) = (conditionOne.startTime ω : ℝ)

  endTime : Ω → ℝ
  endTime_measurable : Measurable endTime
  horizon : Ω → ℝ
  horizon_measurable : Measurable horizon
  start_le_end : ∀ᵐ ω ∂P, (conditionOne.startTime ω : ℝ) ≤ endTime ω
  end_le_horizon : ∀ᵐ ω ∂P, endTime ω ≤ horizon ω

  /-- Conditional endpoint law indexed by the actual report history. -/
  endKernel : Kernel History ℝ
  endKernel_isMarkov : IsMarkovKernel endKernel
  /-- A jointly measurable Lebesgue density for the endpoint conditional law. -/
  endDensity : History → ℝ → ℝ≥0∞
  endDensity_measurable : Measurable (Function.uncurry endDensity)
  endKernel_eq_withDensity :
    endKernel = Kernel.withDensity
      (Kernel.const History (volume : Measure ℝ)) endDensity
  /-- The endpoint's regular conditional law given the actual report history. -/
  end_condDistrib_eq :
    condDistrib endTime history P =ᵐ[P.map history] endKernel
  /-- Condition 2: adding the selected-start realization does not change that law. -/
  end_condDistrib_given_history_start_eq :
    condDistrib endTime
      (fun ω => (history ω, conditionOne.startTime ω)) P =ᵐ[
          P.map (fun ω => (history ω, conditionOne.startTime ω))]
      Kernel.comap endKernel
        (fun hs : History × ℝ≥0 => hs.1)
        (by fun_prop)
  /-- Endpoint support after the selected start. -/
  endKernel_supported_after_start : ∀ h : History,
    endKernel h (Set.Ici (historyStart h)) = 1

  /-- A density presentation of Condition 1's start-selection kernel. -/
  startDensity : ℝ≥0 → ℝ≥0 → ℝ≥0∞
  startDensity_measurable : Measurable (Function.uncurry startDensity)
  startKernel_eq_withDensity :
    conditionOne.rateFreeStartKernel = Kernel.withDensity
      (Kernel.const ℝ≥0 startReference) startDensity

namespace ForwardTheorem2SelectionEndpointDensityModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Tail : Type*} [MeasurableSpace Tail]
  {History : Type*} [MeasurableSpace History] [StandardBorelSpace History]
  [Nonempty History]
  {startReference : Measure ℝ≥0} [SFinite startReference]

/-- The endpoint regular conditional law has the specified history-indexed density. -/
theorem end_condDistrib_eq_withDensity
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference) :
    condDistrib M.endTime M.history P =ᵐ[P.map M.history]
      Kernel.withDensity (Kernel.const History (volume : Measure ℝ)) M.endDensity :=
  M.end_condDistrib_eq.trans <|
    Filter.Eventually.of_forall fun h =>
      congrArg (fun K : Kernel History ℝ => K h) M.endKernel_eq_withDensity

/-- The same density law remains valid after explicitly adjoining the selected start. -/
theorem end_condDistrib_given_history_start_eq_withDensity
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference) :
    condDistrib M.endTime
      (fun ω => (M.history ω, M.conditionOne.startTime ω)) P =ᵐ[
        P.map (fun ω => (M.history ω, M.conditionOne.startTime ω))]
      Kernel.comap
        (Kernel.withDensity (Kernel.const History (volume : Measure ℝ)) M.endDensity)
        (fun hs : History × ℝ≥0 => hs.1)
        (by fun_prop) :=
  M.end_condDistrib_given_history_start_eq.trans <|
    Filter.Eventually.of_forall fun _ => by
      rw [M.endKernel_eq_withDensity]

/--
The endpoint assumption gives a genuine joint density, not merely a symbolic
point-probability factor: the law of `(history, endTime)` is absolutely
presented by the endpoint density over the history marginal times Lebesgue
measure.  This is the endpoint portion of the chain rule needed for Eq. (8).

The remaining Eq. (8) work is to identify the concrete *pre-end* history law
and append the ordered post-start arrival-density factors.  In particular,
this theorem deliberately does not use the observed-after-end padded history.
-/
theorem map_history_end_eq_withDensity
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference) :
    P.map (fun ω => (M.history ω, M.endTime ω)) =
      ((P.map M.history).prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ => M.endDensity he.1 he.2) := by
  letI : IsMarkovKernel M.endKernel := M.endKernel_isMarkov
  letI : IsSFiniteKernel M.endKernel := inferInstance
  letI : IsSFiniteKernel
      ((Kernel.const History (volume : Measure ℝ)).withDensity M.endDensity) :=
    M.endKernel_eq_withDensity ▸ (inferInstance : IsSFiniteKernel M.endKernel)
  calc
    P.map (fun ω => (M.history ω, M.endTime ω)) =
        (P.map M.history) ⊗ₘ condDistrib M.endTime M.history P := by
      symm
      exact ProbabilityTheory.compProd_map_condDistrib M.endTime_measurable.aemeasurable
    _ = (P.map M.history) ⊗ₘ M.endKernel := by
      rw [Measure.compProd_congr M.end_condDistrib_eq]
    _ = ((P.map M.history).prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [M.endKernel_eq_withDensity,
        Measure.compProd_withDensity M.endDensity_measurable,
        Measure.compProd_const]

/--
Kernel-composition form of the endpoint density bridge.  If the concrete
**pre-end** history has a density `historyDensity` over a base measure `μ`,
then adjoining the endpoint has the product density
`historyDensity(history) * endDensity(history, endpoint)` over
`μ × volume`.

This is the measure-theoretic composition required by a corrected Eq. (8)
model.  It is deliberately conditional on an actual history-density theorem
and on this model's regular conditional endpoint kernel; it does not claim
that the printed Conditions 1--2 provide either premise.
-/
theorem map_history_end_eq_jointDensity_of_history_density
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference)
    {μ : Measure History} [SFinite μ]
    (historyDensity : History → ℝ≥0∞)
    (historyDensity_measurable : Measurable historyDensity)
    (history_density : P.map M.history = μ.withDensity historyDensity) :
    P.map (fun ω => (M.history ω, M.endTime ω)) =
      ((μ.prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ =>
          historyDensity he.1 * M.endDensity he.1 he.2)) := by
  calc
    P.map (fun ω => (M.history ω, M.endTime ω)) =
        ((P.map M.history).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) :=
      M.map_history_end_eq_withDensity
    _ = ((μ.withDensity historyDensity).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [history_density]
    _ = ((μ.prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => historyDensity he.1)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [prod_withDensity_left historyDensity_measurable]
    _ = ((μ.prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ =>
          historyDensity he.1 * M.endDensity he.1 he.2)) := by
      simpa only [Pi.mul_apply] using
        (withDensity_mul (μ.prod (volume : Measure ℝ))
          (historyDensity_measurable.comp measurable_fst)
          M.endDensity_measurable).symm

/--
Restricted-history-event form of the endpoint density bridge.

If the history marginal restricted to a measurable history event `A` has
density `historyDensity`, then the joint law of that history event and the
endpoint has the corresponding product density.  This covers restrictions
that are measurable from the pre-end history itself.

An exact finite-arrival-count event additionally involves the next terminal
gap, and is generally *not* history-measurable.  The corrected predictable
product-kernel certificate for that case is
`EndpointProductKernelOnSubmeasure` below.
-/
theorem map_history_end_restrict_eq_jointDensity_of_history_density
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference)
    {A : Set History} (hA : MeasurableSet A)
    {μ : Measure History} [SFinite μ]
    (historyDensity : History → ℝ≥0∞)
    (historyDensity_measurable : Measurable historyDensity)
    (history_density : (P.map M.history).restrict A = μ.withDensity historyDensity) :
    (P.map (fun ω => (M.history ω, M.endTime ω))).restrict
        (A ×ˢ Set.univ) =
      ((μ.prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ =>
          historyDensity he.1 * M.endDensity he.1 he.2)) := by
  calc
    (P.map (fun ω => (M.history ω, M.endTime ω))).restrict
        (A ×ˢ Set.univ) =
        (((P.map M.history).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2)).restrict
            (A ×ˢ Set.univ) := by
      rw [M.map_history_end_eq_withDensity]
    _ = (((P.map M.history).prod (volume : Measure ℝ)).restrict
        (A ×ˢ Set.univ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [restrict_withDensity (hA.prod MeasurableSet.univ)]
    _ = (((P.map M.history).restrict A).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [Measure.restrict_prod_eq_prod_univ]
    _ = ((μ.withDensity historyDensity).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [history_density]
    _ = ((μ.prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => historyDensity he.1)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [prod_withDensity_left historyDensity_measurable]
    _ = ((μ.prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ =>
          historyDensity he.1 * M.endDensity he.1 he.2)) := by
      simpa only [Pi.mul_apply] using
        (withDensity_mul (μ.prod (volume : Measure ℝ))
          (historyDensity_measurable.comp measurable_fst)
          M.endDensity_measurable).symm

/--
Corrected endpoint product-kernel condition on an observed submeasure `Q`.

For an exact-count Poisson observation, `Q` is normally the underlying path
measure restricted to the terminal-survival event.  That event depends on the
next gap and cannot in general be represented by restricting the history
marginal alone.  This field is the formal event-level consequence required of
a stagewise predictable endpoint policy: after forming `Q`, the endpoint
still composes with the pre-end history through the same endpoint density.

It is deliberately an explicit model premise.  The printed Conditions 1--2
do not establish it; proving it from a concrete predictable endpoint clock is
the remaining stochastic construction.
-/
structure EndpointProductKernelOnSubmeasure
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference)
    (Q : Measure Ω) : Prop where
  map_history_end_eq_withDensity :
    Q.map (fun ω => (M.history ω, M.endTime ω)) =
      ((Q.map M.history).prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ => M.endDensity he.1 he.2)

namespace EndpointProductKernelOnSubmeasure

/--
Compose the corrected endpoint product-kernel condition on `Q` with an actual
history subdensity.  Unlike the full-probability marginal bridge, this theorem
is directly applicable to an exact-count terminal-survival submeasure.
-/
theorem map_history_end_eq_jointDensity_of_history_density
    {M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference}
    {Q : Measure Ω}
    (C : EndpointProductKernelOnSubmeasure M Q)
    {μ : Measure History} [SFinite μ]
    (historyDensity : History → ℝ≥0∞)
    (historyDensity_measurable : Measurable historyDensity)
    (history_density : Q.map M.history = μ.withDensity historyDensity) :
    Q.map (fun ω => (M.history ω, M.endTime ω)) =
      ((μ.prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ =>
          historyDensity he.1 * M.endDensity he.1 he.2)) := by
  calc
    Q.map (fun ω => (M.history ω, M.endTime ω)) =
        ((Q.map M.history).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) :=
      C.map_history_end_eq_withDensity
    _ = ((μ.withDensity historyDensity).prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [history_density]
    _ = ((μ.prod (volume : Measure ℝ)).withDensity
          (fun he : History × ℝ => historyDensity he.1)).withDensity
          (fun he : History × ℝ => M.endDensity he.1 he.2) := by
      rw [prod_withDensity_left historyDensity_measurable]
    _ = ((μ.prod (volume : Measure ℝ)).withDensity
        (fun he : History × ℝ =>
          historyDensity he.1 * M.endDensity he.1 he.2)) := by
      simpa only [Pi.mul_apply] using
        (withDensity_mul (μ.prod (volume : Measure ℝ))
          (historyDensity_measurable.comp measurable_fst)
          M.endDensity_measurable).symm

end EndpointProductKernelOnSubmeasure

/-- The setwise form of `map_history_end_eq_withDensity`. -/
theorem map_history_end_apply
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail History startReference)
    (s : Set (History × ℝ)) (hs : MeasurableSet s) :
    P.map (fun ω => (M.history ω, M.endTime ω)) s =
      ∫⁻ he in s, M.endDensity he.1 he.2 ∂
        ((P.map M.history).prod (volume : Measure ℝ)) := by
  rw [M.map_history_end_eq_withDensity, withDensity_apply _ hs]

end ForwardTheorem2SelectionEndpointDensityModel

end

end LBG24SpatialUnderreporting
