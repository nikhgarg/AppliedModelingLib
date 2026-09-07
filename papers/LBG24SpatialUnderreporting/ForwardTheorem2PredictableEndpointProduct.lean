import LBG24SpatialUnderreporting.ForwardTheorem2SelectionEndpointDensity
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteDensity

/-!
# Finite predictable endpoint product model for LBG Appendix Theorem 2

This module records the missing no-lookahead primitive behind the corrected
Eq. (8) proof.  At a visible pre-end prefix, the next unobserved Poisson gap
and a candidate endpoint are conditionally drawn from a product kernel.  Thus
the endpoint cannot inspect that next gap before it is selected.

The source's printed Conditions 1--2 do not state this product law.  A full
stagewise construction will instantiate this finite primitive at every report
stage and then condition on whether the candidate endpoint or next report
arrives first.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
A one-stage corrected endpoint model.  Conditional on `preHistory`, the next
unobserved report gap has exponential law `expMeasure rate`, while the
candidate endpoint has the rate-free kernel `endKernel`; the product-law field
is the formal no-lookahead requirement.

The candidate endpoint may subsequently lose to the next arrival.  Iterating
this model over report stages is the route to the source's survival-integral
factors in the corrected multi-report likelihood.
-/
structure FinitePredictableEndpointProductModel
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Prefix : Type*) [MeasurableSpace Prefix] [StandardBorelSpace Prefix]
    [Nonempty Prefix]
    (rate : ℝ) where
  /-- Information available before drawing the next report gap and endpoint. -/
  preHistory : Ω → Prefix
  preHistory_measurable : Measurable preHistory
  /-- The next unobserved Poisson interarrival gap. -/
  nextGap : Ω → ℝ
  nextGap_measurable : Measurable nextGap
  /-- Candidate endpoint drawn before seeing `nextGap`. -/
  endTime : Ω → ℝ
  endTime_measurable : Measurable endTime
  /-- Rate-free endpoint kernel indexed by the visible prefix. -/
  endKernel : Kernel Prefix ℝ
  endKernel_isMarkov : IsMarkovKernel endKernel
  endDensity : Prefix → ℝ → ℝ≥0∞
  endDensity_measurable : Measurable (Function.uncurry endDensity)
  endKernel_eq_withDensity :
    endKernel = Kernel.withDensity
      (Kernel.const Prefix (volume : Measure ℝ)) endDensity
  /--
  Corrected predictable/product-kernel premise.  In particular, conditioning
  on the candidate endpoint does not alter the next-gap law; this rules out
  an endpoint policy that reads future reports.
  -/
  preHistory_nextGap_end_product :
    P.map (fun ω => (preHistory ω, (nextGap ω, endTime ω))) =
      (P.map preHistory) ⊗ₘ
        ((Kernel.const Prefix (expMeasure rate)) ×ₖ endKernel)

namespace FinitePredictableEndpointProductModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Prefix : Type*} [MeasurableSpace Prefix] [StandardBorelSpace Prefix]
  [Nonempty Prefix] {rate : ℝ}

/--
The checked product-law form of the no-lookahead premise.  This theorem is a
named use site for a later stagewise induction: its left side is the actual
law of visible history, next gap, and candidate endpoint.
-/
theorem map_preHistory_nextGap_end_eq_product
    (M : FinitePredictableEndpointProductModel Ω P Prefix rate) :
    P.map (fun ω => (M.preHistory ω, (M.nextGap ω, M.endTime ω))) =
      (P.map M.preHistory) ⊗ₘ
        ((Kernel.const Prefix (expMeasure rate)) ×ₖ M.endKernel) :=
  M.preHistory_nextGap_end_product

/--
Rectangle form of the no-lookahead product law.  Given a visible prefix in
`A`, the next-gap event `G` and endpoint event `E` contribute the product of
the exponential-gap mass and the endpoint-kernel mass.  This is the one-stage
conditional factorization used when deciding whether the next report or the
candidate endpoint occurs first.
-/
theorem rectangle_factorization
    (M : FinitePredictableEndpointProductModel Ω P Prefix rate)
    {A : Set Prefix} {G E : Set ℝ} (rate_pos : 0 < rate)
    (hA : MeasurableSet A) (hG : MeasurableSet G) (hE : MeasurableSet E) :
    P.map (fun ω => (M.preHistory ω, (M.nextGap ω, M.endTime ω)))
        (A ×ˢ (G ×ˢ E)) =
      ∫⁻ h in A, (expMeasure rate) G * M.endKernel h E ∂P.map M.preHistory := by
  letI : IsMarkovKernel M.endKernel := M.endKernel_isMarkov
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  rw [M.preHistory_nextGap_end_product]
  rw [Measure.compProd_apply_prod hA (hG.prod hE)]
  apply lintegral_congr
  intro h
  rw [Kernel.prod_apply_prod]
  rfl

/--
Response-tail specialization of `rectangle_factorization`: after a visible
prefix in `A`, the event of no next report for `elapsed` time and an endpoint
event `E` factor through the exponential tail and the endpoint kernel.  This
is the one-stage stochastic counterpart of the survival factor used in the
corrected Appendix-B.2 calculation.
-/
theorem tail_rectangle_factorization
    (M : FinitePredictableEndpointProductModel Ω P Prefix rate)
    {A : Set Prefix} {E : Set ℝ} (rate_pos : 0 < rate) (elapsed : ℝ)
    (hA : MeasurableSet A) (hE : MeasurableSet E) :
    P.map (fun ω => (M.preHistory ω, (M.nextGap ω, M.endTime ω)))
        (A ×ˢ (Set.Ioi elapsed ×ˢ E)) =
      ∫⁻ h in A, (expMeasure rate) (Set.Ioi elapsed) * M.endKernel h E
        ∂P.map M.preHistory :=
  M.rectangle_factorization rate_pos hA measurableSet_Ioi hE

/-- The endpoint kernel's density presentation is available at each stage. -/
theorem endKernel_eq_density
    (M : FinitePredictableEndpointProductModel Ω P Prefix rate) :
    M.endKernel = Kernel.withDensity
      (Kernel.const Prefix (volume : Measure ℝ)) M.endDensity :=
  M.endKernel_eq_withDensity

end FinitePredictableEndpointProductModel

end

end LBG24SpatialUnderreporting
