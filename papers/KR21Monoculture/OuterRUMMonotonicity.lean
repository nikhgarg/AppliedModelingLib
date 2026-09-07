import KR21Monoculture.Theorem2OuterConditionalSource

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture
namespace DistributionalAccuracyFamily

/-!
# Outer transport of Definition 1 monotonicity for KR21

The source's Theorem 1 uses the strict dominance comparison against a human
opponent.  At a fixed value profile this follows from Definition 1's strict
first-choice and weak removal monotonicity.  This module proves the separate
measure-theoretic step: strict pointwise monotonicity integrates to the actual
outer-D comparison when both finite-ranking payoffs are integrable.

No RUM family name, source-model record, or caller-supplied conclusion is used
as a substitute for the pointwise removal statement.
-/

/--
The source's strict algorithm-against-human dominance inequality lifts from
almost-everywhere pointwise Definition 1 removal monotonicity to its actual
outer value law.  The four finite payoffs are visible integrability premises,
so the argument cannot rely on Lean's totalized integral.
-/
theorem outer_algorithmAgainstHuman_gt_h_of_ae_removalMonotonicity
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ)
    (hhuman_first : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) D)
    (hhuman_second : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value)
        (F.dist thetaH value) value) D)
    (halgorithm_first : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaA value) value) D)
    (halgorithm_second : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaA value)
        (F.dist thetaH value) value) D)
    (hpoint : ∀ᵐ value ∂D,
      AccuracyFamily.Theorem1RemovalMonotonicityAt
        (F.pointFamily value) thetaA thetaH) :
    F.theorem1_h D thetaA thetaH <
      F.theorem1_algorithmAgainstHuman D thetaA thetaH := by
  have hhuman : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value +
        expectedSecondMoverIndependent (F.dist thetaH value)
          (F.dist thetaH value) value) D :=
    hhuman_first.add hhuman_second
  have halgorithm : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaA value) value +
        expectedSecondMoverIndependent (F.dist thetaA value)
          (F.dist thetaH value) value) D :=
    halgorithm_first.add halgorithm_second
  have hstrict : ∀ᵐ value ∂D,
      expectedFirstMoverUtility (F.dist thetaH value) value +
          expectedSecondMoverIndependent (F.dist thetaH value)
            (F.dist thetaH value) value <
        expectedFirstMoverUtility (F.dist thetaA value) value +
          expectedSecondMoverIndependent (F.dist thetaA value)
            (F.dist thetaH value) value := by
    filter_upwards [hpoint] with value hmono
    exact AccuracyFamily.theorem1_algorithmAgainstHuman_gt_h_of_monotonicity
      (F.pointFamily value) thetaA thetaH
      (AccuracyFamily.theorem1MonotonicityAt_of_removalMonotonicity
        (F.pointFamily value) thetaA thetaH hmono)
  change
    (∫ value, expectedFirstMoverUtility (F.dist thetaH value) value ∂D) +
        ∫ value, expectedSecondMoverIndependent (F.dist thetaH value)
          (F.dist thetaH value) value ∂D <
      (∫ value, expectedFirstMoverUtility (F.dist thetaA value) value ∂D) +
        ∫ value, expectedSecondMoverIndependent (F.dist thetaA value)
          (F.dist thetaH value) value ∂D
  rw [← integral_add hhuman_first hhuman_second,
    ← integral_add halgorithm_first halgorithm_second]
  exact integral_lt_integral_of_ae_lt_of_probability D hhuman halgorithm hstrict

end DistributionalAccuracyFamily
end KR21Monoculture
