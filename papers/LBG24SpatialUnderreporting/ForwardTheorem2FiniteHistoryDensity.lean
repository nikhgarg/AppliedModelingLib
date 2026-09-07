import LBG24SpatialUnderreporting.ForwardTheorem2SelectionEndpointDensity
import LBG24SpatialUnderreporting.ForwardPoissonFiniteArrivalDensity

/-!
# Corrected finite-history endpoint density for LBG Appendix Theorem 2

This module specializes the generic endpoint/history kernel composition to the
actual finite exponential-renewal terminal **subdensity**.  It is a fixed-rate
corrected-model bridge: its explicit premises are an exact-count path
submeasure and the missing predictable endpoint product-kernel condition on
that submeasure.  It does not infer either premise from the printed
Conditions 1--2.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Tail : Type*} [MeasurableSpace Tail]
  {startReference : Measure ℝ≥0} [SFinite startReference]

/--
Fixed-rate exact-count form of the corrected endpoint product-kernel bridge.
The finite Poisson terminal density is the pushforward of an underlying
terminal-survival **submeasure** and has total mass
`P(N(horizon) = count)`.  The additional certificate says that the endpoint
kernel remains a product kernel after forming that submeasure; this is the
formal no-lookahead/predictability condition needed for the source proof.
Once the concrete pre-end history has the stated subdensity, the endpoint
composes with it into an actual joint subdensity.

The unresolved source-model work is precisely to construct this submeasure
and certificate uniformly across rates, for the selected real-valued start
and a stagewise predictable endpoint policy.
-/
theorem finiteArrival_submeasure_history_end_eq_jointDensity
    {count : ℕ} {rate horizon : ℝ}
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail (Fin count → ℝ) startReference)
    (Q : Measure Ω)
    (predictableEndpoint :
      ForwardTheorem2SelectionEndpointDensityModel.EndpointProductKernelOnSubmeasure
        M Q)
    (history_density : Q.map M.history =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count)) :
    Q.map (fun ω => (M.history ω, M.endTime ω)) =
      (((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (fun he : (Fin count → ℝ) × ℝ =>
          finiteArrivalTerminalDensity rate horizon count he.1 *
            M.endDensity he.1 he.2)) := by
  exact predictableEndpoint.map_history_end_eq_jointDensity_of_history_density
    (μ := (volume : Measure (Fin count → ℝ)))
    (finiteArrivalTerminalDensity rate horizon count)
    (measurable_finiteArrivalTerminalDensity rate horizon count)
    history_density

/--
The same corrected exact-count joint density in ordered-arrival normal form.
Its Poisson rate dependence is visibly `rate ^ count * exp (-rate * horizon)`
on the ordered simplex; the endpoint factor is supplied by the corrected
pre-end kernel model.
-/
theorem finiteArrival_submeasure_history_end_eq_orderedJointDensity
    {count : ℕ} {rate horizon : ℝ}
    (rate_pos : 0 < rate) (horizon_nonneg : 0 ≤ horizon)
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail (Fin count → ℝ) startReference)
    (Q : Measure Ω)
    (predictableEndpoint :
      ForwardTheorem2SelectionEndpointDensityModel.EndpointProductKernelOnSubmeasure
        M Q)
    (history_density : Q.map M.history =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count)) :
    Q.map (fun ω => (M.history ω, M.endTime ω)) =
      (((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (fun he : (Fin count → ℝ) × ℝ =>
          finiteArrivalOrderedDensity rate horizon count he.1 *
            M.endDensity he.1 he.2)) := by
  rw [finiteArrival_submeasure_history_end_eq_jointDensity
    M Q predictableEndpoint history_density,
    finiteArrivalTerminalDensity_eq_finiteArrivalOrderedDensity
      rate_pos horizon_nonneg count]

/--
Under the corrected exact-count submeasure premise, adjoining the endpoint
does not change the total mass of the observed count event: it is exactly the
Poisson count likelihood.  This is a genuine submeasure statement, not a
normalization assumption on a probability marginal.
-/
theorem finiteArrival_submeasure_history_end_real_univ_eq_countLikelihood
    {count : ℕ} {rate horizon : ℝ}
    (M : ForwardTheorem2SelectionEndpointDensityModel
      Ω P Tail (Fin count → ℝ) startReference)
    (Q : Measure Ω)
    (history_density : Q.map M.history =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count))
    (rate_pos : 0 < rate) (horizon_nonneg : 0 ≤ horizon) :
    (Q.map (fun ω => (M.history ω, M.endTime ω))).real Set.univ =
      countLikelihood rate horizon count := by
  calc
    (Q.map (fun ω => (M.history ω, M.endTime ω))).real Set.univ =
        (Q.map M.history).real Set.univ := by
      rw [Measure.real_def, Measure.real_def]
      rw [Measure.map_apply (M.history_measurable.prodMk M.endTime_measurable)
          MeasurableSet.univ,
        Measure.map_apply M.history_measurable MeasurableSet.univ]
      simp
    _ = ((volume : Measure (Fin count → ℝ)).withDensity
      (finiteArrivalTerminalDensity rate horizon count)).real Set.univ := by
      rw [history_density]
    _ = countLikelihood rate horizon count :=
      finiteArrivalTerminalDensity_mass_real_eq_countLikelihood
        rate_pos horizon_nonneg count

end

end LBG24SpatialUnderreporting
