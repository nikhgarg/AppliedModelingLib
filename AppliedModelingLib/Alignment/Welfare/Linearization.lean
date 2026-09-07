import AppliedModelingLib.Alignment.Welfare.SigmoidBounds

/-!
# Lifting Bradley--Terry linearization bounds over a population

The distortion analysis of Gölz--Haghtalab--Yang (2025) first bounds a
single user's centered Bradley--Terry win probability by affine utility
expressions, then takes a population expectation.  This module exposes both
that reusable lifting step and the published unit-interval sigmoid coefficients.

## Main declarations

- `HasPointwiseBradleyTerryLinearization`
- `hasPointwiseBradleyTerryLinearization_source`
- `populationBradleyTerryPreference_linearization_of_pointwise`
- `populationBradleyTerryPreference_linearization_source`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

open Learning.HumanFeedback

/--
Pointwise affine bounds for the centered Bradley--Terry win probability.  For
the source Lemma 1, `lowerSlope` is `ℓ_β` and `upperSlope` is `L = 1 / 4`.
-/
def HasPointwiseBradleyTerryLinearization
    {User Alternative : Type*} (utility : FiniteUtilityProfile User Alternative)
    (btScale lowerSlope upperSlope : ℝ) : Prop :=
  ∀ user first second,
    btScale * (lowerSlope * utility user first - upperSlope * utility user second) ≤
        Real.sigmoid (btScale * (utility user first - utility user second)) - (1 : ℝ) / 2 ∧
      Real.sigmoid (btScale * (utility user first - utility user second)) - (1 : ℝ) / 2 ≤
        btScale * (upperSlope * utility user first - lowerSlope * utility user second)

/--
The source Lemma 1 pointwise sandwich, with `L = 1 / 4` and
`ℓ_β = (σ(β) - 1 / 2) / β`, for utilities normalized to `[0, 1]`.
-/
theorem hasPointwiseBradleyTerryLinearization_source
    {User Alternative : Type*} (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility) {btScale : ℝ} (hbtScale : 0 < btScale) :
    HasPointwiseBradleyTerryLinearization utility btScale
      (sigmoidChordSlope btScale) ((1 : ℝ) / 4) := by
  intro user first second
  constructor
  · have hupper := sigmoid_centered_bradleyTerry_upper hbtScale
      (hutility user second) (hutility user first)
    have hneg : btScale * (utility user second - utility user first) =
        -(btScale * (utility user first - utility user second)) := by ring
    rw [hneg, Real.sigmoid_neg] at hupper
    nlinarith
  · exact sigmoid_centered_bradleyTerry_upper hbtScale
      (hutility user first) (hutility user second)

/--
Population expectation preserves the source Lemma 1 affine shape once its
single-user Bradley--Terry bounds have been established.
-/
theorem populationBradleyTerryPreference_linearization_of_pointwise
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale lowerSlope upperSlope : ℝ)
    (hlinear : HasPointwiseBradleyTerryLinearization utility
      btScale lowerSlope upperSlope)
    (first second : Alternative) :
    btScale *
          (lowerSlope * populationAverageUtility population utility first -
            upperSlope * populationAverageUtility population utility second) ≤
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second -
          (1 : ℝ) / 2 ∧
      (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second -
          (1 : ℝ) / 2 ≤
        btScale *
          (upperSlope * populationAverageUtility population utility first -
            lowerSlope * populationAverageUtility population utility second) := by
  change
    btScale *
          (lowerSlope * populationAverageUtility population utility first -
            upperSlope * populationAverageUtility population utility second) ≤
        pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user first - utility user second))) - (1 : ℝ) / 2 ∧
      pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user first - utility user second))) - (1 : ℝ) / 2 ≤
        btScale *
          (upperSlope * populationAverageUtility population utility first -
            lowerSlope * populationAverageUtility population utility second)
  have hlower := pmfExp_le_pmfExp_of_forall_le population
    (fun user =>
      btScale * (lowerSlope * utility user first - upperSlope * utility user second))
    (fun user =>
      Real.sigmoid (btScale * (utility user first - utility user second)) - (1 : ℝ) / 2)
    (fun user => (hlinear user first second).1)
  have hupper := pmfExp_le_pmfExp_of_forall_le population
    (fun user =>
      Real.sigmoid (btScale * (utility user first - utility user second)) - (1 : ℝ) / 2)
    (fun user =>
      btScale * (upperSlope * utility user first - lowerSlope * utility user second))
    (fun user => (hlinear user first second).2)
  constructor
  · calc
      btScale *
            (lowerSlope * populationAverageUtility population utility first -
              upperSlope * populationAverageUtility population utility second) =
          pmfExp population (fun user =>
            btScale * (lowerSlope * utility user first - upperSlope * utility user second)) := by
              simp [populationAverageUtility, pmfExp_const_mul, pmfExp_sub]
      _ ≤ pmfExp population (fun user =>
            Real.sigmoid (btScale * (utility user first - utility user second)) - (1 : ℝ) / 2) :=
        hlower
      _ = pmfExp population (fun user =>
            Real.sigmoid (btScale * (utility user first - utility user second))) - (1 : ℝ) / 2 := by
        rw [pmfExp_sub, pmfExp_const]
  · calc
      pmfExp population (fun user =>
            Real.sigmoid (btScale * (utility user first - utility user second))) - (1 : ℝ) / 2 =
          pmfExp population (fun user =>
            Real.sigmoid (btScale * (utility user first - utility user second)) - (1 : ℝ) / 2) := by
              rw [pmfExp_sub, pmfExp_const]
      _ ≤ pmfExp population (fun user =>
            btScale * (upperSlope * utility user first - lowerSlope * utility user second)) :=
        hupper
      _ = btScale *
            (upperSlope * populationAverageUtility population utility first -
              lowerSlope * populationAverageUtility population utility second) := by
              simp [populationAverageUtility, pmfExp_const_mul, pmfExp_sub]

/--
Lemma 1 of Gölz--Haghtalab--Yang (2025), specialized to a finite population
and the source's unit-interval utility normalization.  This is the exact
published affine sandwich for population expected Bradley--Terry win rates.
-/
theorem populationBradleyTerryPreference_linearization_source
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility) {btScale : ℝ} (hbtScale : 0 < btScale)
    (first second : Alternative) :
    btScale *
          (sigmoidChordSlope btScale * populationAverageUtility population utility first -
            (1 : ℝ) / 4 * populationAverageUtility population utility second) ≤
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second -
          (1 : ℝ) / 2 ∧
      (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second -
          (1 : ℝ) / 2 ≤
        btScale *
          ((1 : ℝ) / 4 * populationAverageUtility population utility first -
            sigmoidChordSlope btScale * populationAverageUtility population utility second) :=
  populationBradleyTerryPreference_linearization_of_pointwise
    (User := User) (Alternative := Alternative) population utility btScale
    (sigmoidChordSlope btScale) ((1 : ℝ) / 4)
    (hasPointwiseBradleyTerryLinearization_source utility hutility hbtScale) first second

end Welfare
end Alignment
end AppliedModelingLib
