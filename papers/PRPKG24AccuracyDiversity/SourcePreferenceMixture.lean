import PRPKG24AccuracyDiversity.Basic
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Source-selected type mixture

The paper's equation (3) first draws the user's preferred type and then takes
the conditional value associated with that type. This module records that
outer draw as an actual finite PMF, rather than merely as a vector of weights.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

open AppliedModelingLib

/-- The finite law used for the paper's initial draw of a preferred item type. -/
abbrev SourcePreferenceLaw (T : ℕ) := PMF (ItemType T)

/--
The finite `gamma`-homogeneity normalizer is nonzero for a genuine preferred-
type PMF.  This discharges the denominator obligation in Definitions 1 and 2
from the source probability model itself: a PMF has a positive-support atom,
and every real power of that atom is positive.
-/
theorem sourcePreferenceLaw_gamma_normalizer_ne_zero
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (gamma : ℝ) :
    (∑ i : ItemType T, ((preferenceLaw i).toReal) ^ gamma) ≠ 0 := by
  obtain ⟨t, ht⟩ := preferenceLaw.support_nonempty
  have hmass : 0 < preferenceLaw t := (preferenceLaw.apply_pos_iff t).2 ht
  have hmass_real : 0 < (preferenceLaw t).toReal := by
    exact ENNReal.toReal_pos hmass.ne' (preferenceLaw.apply_ne_top t)
  have hpow_pos : 0 < ((preferenceLaw t).toReal) ^ gamma :=
    Real.rpow_pos_of_pos hmass_real gamma
  apply ne_of_gt
  refine lt_of_lt_of_le hpow_pos ?_
  exact Finset.single_le_sum
    (fun i _ => Real.rpow_nonneg ENNReal.toReal_nonneg gamma)
    (Finset.mem_univ t)

/--
`M` realizes a source-selected-type law when its likelihood coordinate is the
real mass of each atom of that law. Because the law is a `PMF`, normalization
and nonnegativity are carried by the object rather than supplied as separate
unverified assumptions.
-/
def ConsumptionModel.RealizesSourcePreferenceLaw {T : ℕ}
    (M : ConsumptionModel T) (preferenceLaw : SourcePreferenceLaw T) : Prop :=
  ∀ t, M.likelihood t = (preferenceLaw t).toReal

/--
Equation (3) as an expectation over the source-selected preferred type.

The inner value is conditional on the selected type; this result asserts no
independence or joint-law condition between distinct type-specific outcomes.
-/
theorem ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp {T : ℕ}
    (M : ConsumptionModel T) (a : CountAllocation T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hlaw : M.RealizesSourcePreferenceLaw preferenceLaw) :
    M.objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t => M.valueOfCount t (a.count t)) := by
  rw [ConsumptionModel.objective_eq_allocation_objective]
  unfold AppliedModelingLib.Allocation.objective AppliedModelingLib.pmfExp
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [hlaw t]

end PRPKG24AccuracyDiversity
