import AppliedModelingLib.Foundations.Probability.ForwardStoppedPoisson

/-!
# Forward stopped-Poisson bridge for spatial-underreporting Lemma 2

The paper's residual-waiting argument concerns a report process beginning at
an incident, so this bridge intentionally uses a forward nonnegative-time
process.  It reduces the paper-facing exponential survival statement to an
explicit strong-Markov conditional-increment certificate; it does not claim
that fixed-time independent increments alone establish that certificate.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped NNReal

noncomputable section

/--
Appendix Lemma 2's conditional no-report statement after a valid forward
stopping time.  `C` is the precise remaining strong-Markov path-space input:
it identifies the conditional law of the post-stop count under the stopped
filtration.  The conclusion is an almost-everywhere equality of regular
conditional probabilities, not informal conditioning notation.
-/
theorem lemma2_conditional_no_report_after_forward_stopping
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : ForwardStoppedPoissonIncrementLawCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.isStoppingTime.measurableSpace ω).real
          {ω' | forwardPostStopIntervalCount H.process C.stopTime u ω' = 0} =
        noArrivalProb H.process.rate (u : ℝ) :=
  C.conditional_postStop_zero_real u

/--
The same Appendix Lemma 2 conclusion as an exponential waiting-time survival
tail.  This is the form used in the source proof after conditioning on the
valid start time.
-/
theorem lemma2_conditional_no_report_exponential_tail_after_forward_stopping
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : ForwardStoppedPoissonIncrementLawCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.isStoppingTime.measurableSpace ω).real
          {ω' | forwardPostStopIntervalCount H.process C.stopTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk H.process.rate H.process.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal :=
  C.conditional_postStop_zero_real_eq_exponential_tail u

end
end LBG24SpatialUnderreporting
