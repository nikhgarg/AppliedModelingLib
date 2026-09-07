import AppliedModelingLib.Alignment.Welfare.AverageUtility
import AppliedModelingLib.Learning.HumanFeedback.PairwisePreference
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Population-aggregated Bradley--Terry comparisons

Each user has their own utility vector.  Pairwise comparison probabilities are
formed by averaging individual Bradley--Terry probabilities, not by applying a
sigmoid to the population-average utility; the latter equality is generally
false and is a central issue in the distortion paper.

## Main declarations

- `populationBradleyTerryPreference`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

open Learning.HumanFeedback

/-- Aggregate independent user Bradley--Terry comparisons into one valid preference model. -/
noncomputable def populationBradleyTerryPreference
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) : PairwisePreference PUnit Alternative where
  prob _ first second :=
    pmfExp population fun user =>
      Real.sigmoid (btScale * (utility user first - utility user second))
  nonneg _ first second :=
    pmfExp_nonneg_of_forall_nonneg population _ fun user => Real.sigmoid_nonneg _
  le_one _ first second :=
    pmfExp_le_of_forall_le population _ 1 fun user => Real.sigmoid_le_one _
  complementary := by
    intro _ first second
    rw [← pmfExp_add, ← pmfExp_const population 1]
    refine pmfExp_congr population fun user => ?_
    have hneg : btScale * (utility user second - utility user first) =
        -(btScale * (utility user first - utility user second)) := by ring
    rw [hneg, Real.sigmoid_neg]
    ring

/-- Every finite population Bradley--Terry comparison probability is strictly
positive: it is a finite expectation of strictly positive logistic terms. -/
theorem populationBradleyTerryPreference_prob_pos
    {User Alternative : Type*} [Fintype User] [DecidableEq User] [Nonempty User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (first second : Alternative) :
    0 < (populationBradleyTerryPreference population utility btScale).prob
      PUnit.unit.{1} first second := by
  change 0 < pmfExp population (fun user =>
    Real.sigmoid (btScale * (utility user first - utility user second)))
  exact pmfExp_pos_of_support_forall_pos population _ fun _ _ => Real.sigmoid_pos _

end Welfare
end Alignment
end AppliedModelingLib
