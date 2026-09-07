import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite heterogeneous utility populations

The alignment-distortion model keeps the distribution of users, the utility
profile, comparison-pair sampling, and reference policy semantically distinct.
This module supplies only their finite data types and the unit-interval utility
condition; welfare and preference aggregation live in sibling modules.

## Main declarations

- `FiniteUtilityProfile`
- `UnitIntervalUtilityProfile`
- `ComparisonPairSampling`
- `ReferenceAlternativePolicy`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

/-- A user's cardinal utility for each finite alternative. -/
abbrev FiniteUtilityProfile (User Alternative : Type*) := User → Alternative → ℝ

/-- The source distortion model's utility normalization to the unit interval. -/
def UnitIntervalUtilityProfile {User Alternative : Type*}
    (utility : FiniteUtilityProfile User Alternative) : Prop :=
  ∀ user alternative, 0 ≤ utility user alternative ∧ utility user alternative ≤ 1

/-- A comparison-pair distribution, intentionally distinct from a user distribution. -/
abbrev ComparisonPairSampling (Alternative : Type*) := PMF (Alternative × Alternative)

/-- A context-free reference policy over alternatives, kept distinct from comparison sampling. -/
abbrev ReferenceAlternativePolicy (Alternative : Type*) := PMF Alternative

end Welfare
end Alignment
end AppliedModelingLib
