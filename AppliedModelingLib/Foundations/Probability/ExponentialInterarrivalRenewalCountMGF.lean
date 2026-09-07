import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.PoissonMomentGenerating

/-!
# Generating functions of canonical exponential renewal counts

This module transports the exact Poisson marginal of a canonical exponential
renewal count into reusable integrability and probability-generating-function
identities.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- Every real power of a fixed-time canonical exponential renewal count is
integrable. -/
theorem integrable_pow_canonicalRenewalCount {rate t : ℝ}
    (hrate : 0 < rate) (ht : 0 ≤ t) (q : ℝ) :
    Integrable (fun omega : ℕ → ℝ => q ^ canonicalRenewalCount t omega)
      (exponentialInterarrivalMeasure rate) := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  have hcount := canonicalRenewalCount_hasLaw_poisson hrate ht
  have htarget : Integrable (fun n : ℕ => q ^ n)
      (Measure.map (canonicalRenewalCount t) (exponentialInterarrivalMeasure rate)) := by
    rw [hcount.map_eq]
    exact integrable_pow_poissonMeasure r q
  simpa [Function.comp_def] using htarget.comp_aemeasurable hcount.aemeasurable

/-- The probability generating function of a fixed-time canonical exponential
renewal count has the Poisson form at exposure `rate * t`. -/
theorem integral_pow_canonicalRenewalCount {rate t : ℝ}
    (hrate : 0 < rate) (ht : 0 ≤ t) (q : ℝ) :
    ∫ omega : ℕ → ℝ, q ^ canonicalRenewalCount t omega
      ∂exponentialInterarrivalMeasure rate =
      Real.exp ((rate * t) * (q - 1)) := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  calc
    ∫ omega : ℕ → ℝ, q ^ canonicalRenewalCount t omega
        ∂exponentialInterarrivalMeasure rate =
        ∫ n : ℕ, q ^ n ∂poissonMeasure r := by
          simpa [r, Function.comp_def] using
            (canonicalRenewalCount_hasLaw_poisson hrate ht).integral_comp
              (f := fun n : ℕ => q ^ n)
              (measurable_of_countable _).aestronglyMeasurable
    _ = Real.exp ((r : ℝ) * (q - 1)) :=
      integral_pow_poissonMeasure r q
    _ = Real.exp ((rate * t) * (q - 1)) := by rfl

end

end AppliedModelingLib.Probability.PoissonProcess
