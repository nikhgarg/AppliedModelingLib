import Mathlib.Data.Real.Basic

namespace AppliedModelingLib
namespace Admissions

/-!
# Admissions Policy Surfaces

Reusable policy metric surfaces for admissions/testing models.

The structure records the scalar quantities that policy-comparison statements
typically expose: population share, capacity, group-policy precision/access
values, policy diversity, individual-fairness gaps, and groupwise academic
merit.

## Main declarations

- `PolicySurface`
- `GroupFair`
- `IndividualFair`
- `GroupAcademicMeritWeaklyImproves`
- `DiversityWeaklyImproves`
-/

/-- Metric surface for admissions/testing policy comparisons. -/
structure PolicySurface (Group Policy : Type*) where
  populationShareB : ℝ
  capacity : ℝ
  precision : Group → Policy → ℝ
  accessLevel : Group → ℝ
  estimatedSkillMean : Group → Policy → ℝ
  estimatedSkillVariance : Group → Policy → ℝ
  admissionThreshold : Policy → ℝ
  diversity : Policy → ℝ
  individualFairnessGap : Policy → ℝ → ℝ
  academicMerit : Group → Policy → ℝ

/-- Group fairness: admitted underrepresented-group share matches population share. -/
def GroupFair {Group Policy : Type*}
    (S : PolicySurface Group Policy) (P : Policy) : Prop :=
  S.diversity P = S.populationShareB

/-- Individual fairness: no skill-level admission-probability gap. -/
def IndividualFair {Group Policy : Type*}
    (S : PolicySurface Group Policy) (P : Policy) : Prop :=
  ∀ q : ℝ, S.individualFairnessGap P q = 0

theorem not_groupFair_of_diversity_ne
    {Group Policy : Type*}
    {S : PolicySurface Group Policy} {P : Policy}
    (hne : S.diversity P ≠ S.populationShareB) :
    ¬ GroupFair S P := by
  intro hfair
  exact hne hfair

theorem not_groupFair_of_diversity_lt
    {Group Policy : Type*}
    {S : PolicySurface Group Policy} {P : Policy}
    (hlt : S.diversity P < S.populationShareB) :
    ¬ GroupFair S P :=
  not_groupFair_of_diversity_ne (ne_of_lt hlt)

theorem not_individualFair_of_gap_ne
    {Group Policy : Type*}
    {S : PolicySurface Group Policy} {P : Policy}
    (q : ℝ) (hne : S.individualFairnessGap P q ≠ 0) :
    ¬ IndividualFair S P := by
  intro hfair
  exact hne (hfair q)

/-- Group academic merit weakly improves when moving from one policy to another. -/
def GroupAcademicMeritWeaklyImproves {Group Policy : Type*}
    (S : PolicySurface Group Policy) (g : Group)
    (fromPolicy toPolicy : Policy) : Prop :=
  S.academicMerit g fromPolicy ≤ S.academicMerit g toPolicy

/-- Diversity weakly improves when moving from one policy to another. -/
def DiversityWeaklyImproves {Group Policy : Type*}
    (S : PolicySurface Group Policy) (fromPolicy toPolicy : Policy) : Prop :=
  S.diversity fromPolicy ≤ S.diversity toPolicy

end Admissions
end AppliedModelingLib
