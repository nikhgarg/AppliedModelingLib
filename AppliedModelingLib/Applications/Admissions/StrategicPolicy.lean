import AppliedModelingLib.GameTheory.Choice.BinaryPolicyGame
import Mathlib.Tactic.Linarith

namespace AppliedModelingLib
namespace Admissions

/-!
# Strategic Admissions Policy Surfaces

Reusable surfaces for two-policy strategic admissions games and weighted
groupwise admitted-merit objectives.

## Main declarations

- `StrategicPolicySurface`
- `overrideSchoolValue`
- `overrideSchoolMeritRow`
- `twoGroupWeightedOutcome`
- `twoGroupWeightedOutcomeObjective`
- `twoGroupWeightedOutcomeObjective_le_iff_groupA_of_groupB_eq`
- `twoGroupWeightedOutcomeObjective_lt_of_groupwise_lt`
-/

/--
Strategic policy surface for admissions papers: test-taking mass, groupwise
admitted merit, diversity rows, and an equilibrium predicate over policy pairs.
-/
structure StrategicPolicySurface
    (Group Policy School Equilibrium : Type*) where
  massTestTaking : Group → Policy → ℝ
  admittedAcademicMerit : School → Group → Policy → ℝ
  diversity : School → Policy → ℝ
  policyPairIsEquilibrium : Policy → Policy → Prop
  equilibriumPredicate : Equilibrium → Prop

/-- Override one school's scalar row while leaving every other row unchanged. -/
def overrideSchoolValue
    {School : Type*} [DecidableEq School]
    (target : School) (value : ℝ) (fallback : School → ℝ) : School → ℝ :=
  fun J => if J = target then value else fallback J

@[simp] theorem overrideSchoolValue_self
    {School : Type*} [DecidableEq School]
    (target : School) (value : ℝ) (fallback : School → ℝ) :
    overrideSchoolValue target value fallback target = value := by
  simp [overrideSchoolValue]

theorem overrideSchoolValue_of_ne
    {School : Type*} [DecidableEq School]
    {target J : School} (hJ : J ≠ target) (value : ℝ)
    (fallback : School → ℝ) :
    overrideSchoolValue target value fallback J = fallback J := by
  simp [overrideSchoolValue, hJ]

/-- Override one school's groupwise merit row while leaving every other row unchanged. -/
def overrideSchoolMeritRow
    {Group School : Type*} [DecidableEq School]
    (target : School) (value : Group → ℝ)
    (fallback : School → Group → ℝ) : School → Group → ℝ :=
  fun J g => if J = target then value g else fallback J g

@[simp] theorem overrideSchoolMeritRow_self
    {Group School : Type*} [DecidableEq School]
    (target : School) (value : Group → ℝ)
    (fallback : School → Group → ℝ) (g : Group) :
    overrideSchoolMeritRow target value fallback target g = value g := by
  simp [overrideSchoolMeritRow]

theorem overrideSchoolMeritRow_of_ne
    {Group School : Type*} [DecidableEq School]
    {target J : School} (hJ : J ≠ target) (value : Group → ℝ)
    (fallback : School → Group → ℝ) (g : Group) :
    overrideSchoolMeritRow target value fallback J g = fallback J g := by
  simp [overrideSchoolMeritRow, hJ]

/-- Weighted two-group admitted academic merit for a school under one policy state. -/
def twoGroupWeightedOutcome
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (policy : Policy) : ℝ :=
  populationShare groupA * S.admittedAcademicMerit J groupA policy +
    populationShare groupB * S.admittedAcademicMerit J groupB policy

/-- Weighted two-group admitted academic merit induced by a policy-pair map. -/
def twoGroupWeightedOutcomeObjective
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 : Policy) : ℝ :=
  twoGroupWeightedOutcome S J groupA groupB populationShare
    (policyPair P1 P2)

/-- If group `A` contributes zero, the two-group objective is group `B`'s contribution. -/
theorem twoGroupWeightedOutcomeObjective_eq_groupB_of_groupA_zero
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 : Policy)
    (hzeroA :
      populationShare groupA *
          S.admittedAcademicMerit J groupA (policyPair P1 P2) = 0) :
    twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 =
      populationShare groupB *
        S.admittedAcademicMerit J groupB (policyPair P1 P2) := by
  simp [twoGroupWeightedOutcomeObjective, twoGroupWeightedOutcome, hzeroA]

/-- Zero group-`A` merit gives the group-`B` objective formula. -/
theorem twoGroupWeightedOutcomeObjective_eq_groupB_of_groupA_merit_zero
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 : Policy)
    (hzeroA :
      S.admittedAcademicMerit J groupA (policyPair P1 P2) = 0) :
    twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 =
      populationShare groupB *
        S.admittedAcademicMerit J groupB (policyPair P1 P2) :=
  twoGroupWeightedOutcomeObjective_eq_groupB_of_groupA_zero
    S policyPair J groupA groupB populationShare P1 P2 (by simp [hzeroA])

/-- If group `B` contributes zero, the two-group objective is group `A`'s contribution. -/
theorem twoGroupWeightedOutcomeObjective_eq_groupA_of_groupB_zero
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 : Policy)
    (hzeroB :
      populationShare groupB *
          S.admittedAcademicMerit J groupB (policyPair P1 P2) = 0) :
    twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 =
      populationShare groupA *
        S.admittedAcademicMerit J groupA (policyPair P1 P2) := by
  simp [twoGroupWeightedOutcomeObjective, twoGroupWeightedOutcome, hzeroB]

/-- Zero group-`B` merit gives the group-`A` objective formula. -/
theorem twoGroupWeightedOutcomeObjective_eq_groupA_of_groupB_merit_zero
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 : Policy)
    (hzeroB :
      S.admittedAcademicMerit J groupB (policyPair P1 P2) = 0) :
    twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 =
      populationShare groupA *
        S.admittedAcademicMerit J groupA (policyPair P1 P2) :=
  twoGroupWeightedOutcomeObjective_eq_groupA_of_groupB_zero
    S policyPair J groupA groupB populationShare P1 P2 (by simp [hzeroB])

/--
If group `B`'s admitted merit is unchanged, a two-group objective comparison
is exactly the group-`A` comparison when group `A` has positive population
weight.
-/
theorem twoGroupWeightedOutcomeObjective_le_iff_groupA_of_groupB_eq
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 P1' P2' : Policy)
    (hshareA : 0 < populationShare groupA)
    (hgroupB :
      S.admittedAcademicMerit J groupB (policyPair P1 P2) =
        S.admittedAcademicMerit J groupB (policyPair P1' P2')) :
    (twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 ≤
      twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1' P2') ↔
      S.admittedAcademicMerit J groupA (policyPair P1 P2) ≤
        S.admittedAcademicMerit J groupA (policyPair P1' P2') := by
  unfold twoGroupWeightedOutcomeObjective twoGroupWeightedOutcome
  rw [hgroupB]
  constructor
  · intro h
    nlinarith [hshareA, h]
  · intro h
    have hmul :
        populationShare groupA *
            S.admittedAcademicMerit J groupA (policyPair P1 P2) ≤
          populationShare groupA *
            S.admittedAcademicMerit J groupA (policyPair P1' P2') :=
      mul_le_mul_of_nonneg_left h hshareA.le
    nlinarith [hmul]

/--
If group `A`'s admitted merit is unchanged, a two-group objective comparison
is exactly the group-`B` comparison when group `B` has positive population
weight.
-/
theorem twoGroupWeightedOutcomeObjective_le_iff_groupB_of_groupA_eq
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 P1' P2' : Policy)
    (hshareB : 0 < populationShare groupB)
    (hgroupA :
      S.admittedAcademicMerit J groupA (policyPair P1 P2) =
        S.admittedAcademicMerit J groupA (policyPair P1' P2')) :
    (twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 ≤
      twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1' P2') ↔
      S.admittedAcademicMerit J groupB (policyPair P1 P2) ≤
        S.admittedAcademicMerit J groupB (policyPair P1' P2') := by
  unfold twoGroupWeightedOutcomeObjective twoGroupWeightedOutcome
  rw [hgroupA]
  constructor
  · intro h
    nlinarith [hshareB, h]
  · intro h
    have hmul :
        populationShare groupB *
            S.admittedAcademicMerit J groupB (policyPair P1 P2) ≤
          populationShare groupB *
            S.admittedAcademicMerit J groupB (policyPair P1' P2') :=
      mul_le_mul_of_nonneg_left h hshareB.le
    nlinarith [hmul]

/-- Group-`A` cancellation plus named scalar formulas. -/
theorem twoGroupWeightedOutcomeObjective_le_iff_groupA_formula_of_groupB_eq
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 P1' P2' : Policy) {lhs rhs : ℝ}
    (hshareA : 0 < populationShare groupA)
    (hgroupB :
      S.admittedAcademicMerit J groupB (policyPair P1 P2) =
        S.admittedAcademicMerit J groupB (policyPair P1' P2'))
    (hlhs :
      S.admittedAcademicMerit J groupA (policyPair P1 P2) = lhs)
    (hrhs :
      S.admittedAcademicMerit J groupA (policyPair P1' P2') = rhs) :
    (twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 ≤
      twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1' P2') ↔
      lhs ≤ rhs := by
  rw [twoGroupWeightedOutcomeObjective_le_iff_groupA_of_groupB_eq
    S policyPair J groupA groupB populationShare P1 P2 P1' P2'
    hshareA hgroupB, hlhs, hrhs]

/-- Group-`B` cancellation plus named scalar formulas. -/
theorem twoGroupWeightedOutcomeObjective_le_iff_groupB_formula_of_groupA_eq
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 P1' P2' : Policy) {lhs rhs : ℝ}
    (hshareB : 0 < populationShare groupB)
    (hgroupA :
      S.admittedAcademicMerit J groupA (policyPair P1 P2) =
        S.admittedAcademicMerit J groupA (policyPair P1' P2'))
    (hlhs :
      S.admittedAcademicMerit J groupB (policyPair P1 P2) = lhs)
    (hrhs :
      S.admittedAcademicMerit J groupB (policyPair P1' P2') = rhs) :
    (twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 ≤
      twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1' P2') ↔
      lhs ≤ rhs := by
  rw [twoGroupWeightedOutcomeObjective_le_iff_groupB_of_groupA_eq
    S policyPair J groupA groupB populationShare P1 P2 P1' P2'
    hshareB hgroupA, hlhs, hrhs]

/--
If both group-specific admitted merits strictly increase and both population
shares are positive, then the weighted two-group objective strictly increases.
-/
theorem twoGroupWeightedOutcomeObjective_lt_of_groupwise_lt
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 P1' P2' : Policy)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hA :
      S.admittedAcademicMerit J groupA (policyPair P1 P2) <
        S.admittedAcademicMerit J groupA (policyPair P1' P2'))
    (hB :
      S.admittedAcademicMerit J groupB (policyPair P1 P2) <
        S.admittedAcademicMerit J groupB (policyPair P1' P2')) :
    twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 <
      twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1' P2' := by
  unfold twoGroupWeightedOutcomeObjective twoGroupWeightedOutcome
  exact
    add_lt_add
      (mul_lt_mul_of_pos_left hA hshareA)
      (mul_lt_mul_of_pos_left hB hshareB)

/--
If both group-specific admitted merits weakly increase and both population
shares are nonnegative, then the weighted two-group objective weakly increases.
-/
theorem twoGroupWeightedOutcomeObjective_le_of_groupwise_le
    {Group Policy School Equilibrium : Type*}
    (S : StrategicPolicySurface Group Policy School Equilibrium)
    (policyPair : Policy → Policy → Policy)
    (J : School) (groupA groupB : Group) (populationShare : Group → ℝ)
    (P1 P2 P1' P2' : Policy)
    (hshareA : 0 ≤ populationShare groupA)
    (hshareB : 0 ≤ populationShare groupB)
    (hA :
      S.admittedAcademicMerit J groupA (policyPair P1 P2) ≤
        S.admittedAcademicMerit J groupA (policyPair P1' P2'))
    (hB :
      S.admittedAcademicMerit J groupB (policyPair P1 P2) ≤
        S.admittedAcademicMerit J groupB (policyPair P1' P2')) :
    twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1 P2 ≤
      twoGroupWeightedOutcomeObjective S policyPair J
        groupA groupB populationShare P1' P2' := by
  unfold twoGroupWeightedOutcomeObjective twoGroupWeightedOutcome
  exact
    add_le_add
      (mul_le_mul_of_nonneg_left hA hshareA)
      (mul_le_mul_of_nonneg_left hB hshareB)

end Admissions
end AppliedModelingLib
