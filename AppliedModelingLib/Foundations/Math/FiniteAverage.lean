import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Finite arithmetic averages

Domain-neutral arithmetic averages of finite families in real normed spaces.
The definition is total at an empty index type: the inverse cardinality and
the finite sum are both zero.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The arithmetic average of a finite family, totalized as zero when the
index type is empty. -/
noncomputable def finiteAverage {Index Value : Type*}
    [Fintype Index] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (value : Index → Value) : Value :=
  ((Fintype.card Index : ℝ)⁻¹) • ∑ index, value index

/-- On a finite real family, `finiteAverage` is the ordinary sum divided by
the cardinality. -/
theorem finiteAverage_real_eq_div_card {Index : Type*} [Fintype Index]
    (value : Index → ℝ) :
    finiteAverage value = (∑ index, value index) / (Fintype.card Index : ℝ) := by
  simp only [finiteAverage, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm]

end AppliedModelingLib
