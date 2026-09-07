import AppliedModelingLib.Foundations.Probability.GaussianQuantile

namespace AppliedModelingLib
namespace Admissions

noncomputable section

/-!
# Strategic Admissions Application Decisions

Reusable cutoff and payoff primitives for binary apply/not-apply decisions in
strategic admissions models.

## Main declarations

- `strategicApplyCutoff`
- `strategicApplyPayoff`
- `strategicTwoSchoolApplyPayoff`
- `strategicTwoSchoolApplicationRegion`
-/

/--
Projected-skill cutoff for a one-school full-policy application decision.

If projected full-policy admission is `1 - Φ((threshold - q) / scale)` and
applying has cost/value ratio `α`, the indifferent projected-skill cutoff is
`threshold - scale * Φ⁻¹(1 - α)`.
-/
def strategicApplyCutoff
    (Q : Probability.StandardGaussianQuantileAPI)
    (admissionThreshold scale costRatio : ℝ) : ℝ :=
  admissionThreshold - scale * Q.quantile (1 - costRatio)

/-- Payoff for the binary apply/not-apply decision. -/
def strategicApplyPayoff
    (value cost admissionProbability : ℝ) (apply : Bool) : ℝ :=
  if apply then value * admissionProbability - cost else 0

/--
Incremental payoff for a two-school application decision with a fallback school.

Below the second school's no-test threshold, applying to the preferred school
has value `v1`; above that threshold, the fallback value `v2` is already
available, so the incremental value is `v1 - v2`.
-/
def strategicTwoSchoolApplyPayoff
    (school2SubThreshold v1 v2 cost admissionProbability q : ℝ)
    (apply : Bool) : ℝ :=
  if apply then
    if q < school2SubThreshold then
      v1 * admissionProbability - cost
    else
      (v1 - v2) * admissionProbability - cost
  else
    0

/--
Low/high application region for the two-school case.

Applicants apply either below the fallback school's no-test cutoff but above
the low cutoff, or above both the fallback cutoff and the high cutoff.
-/
def strategicTwoSchoolApplicationRegion
    (school2SubThreshold lowCutoff highCutoff q : ℝ) : Prop :=
  (q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
    (school2SubThreshold ≤ q ∧ highCutoff ≤ q)

end

end Admissions
end AppliedModelingLib
