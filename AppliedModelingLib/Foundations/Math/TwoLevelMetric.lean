import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Two-level graph metrics

A symmetric proximity relation gives a metric-valued distance by assigning one
positive distance to related distinct points and a second distance to all
other distinct points. The only nontrivial triangle condition is that the far
distance is at most twice the near distance.
-/

namespace AppliedModelingLib

/-- Distance zero on the diagonal, `near` on close pairs, and `far` otherwise. -/
def twoLevelDistance {Vertex : Type*} [DecidableEq Vertex]
    (close : Vertex → Vertex → Prop)
    [DecidableRel close] (near far : ℝ) (left right : Vertex) : ℝ :=
  if left = right then 0 else if close left right then near else far

@[simp] theorem twoLevelDistance_self {Vertex : Type*}
    [DecidableEq Vertex] (close : Vertex → Vertex → Prop) [DecidableRel close]
    (near far : ℝ) (vertex : Vertex) :
    twoLevelDistance close near far vertex vertex = 0 := by
  simp [twoLevelDistance]

/-- A symmetric proximity relation gives a symmetric two-level distance. -/
theorem twoLevelDistance_comm {Vertex : Type*}
    [DecidableEq Vertex] (close : Vertex → Vertex → Prop) [DecidableRel close]
    (hclose : Symmetric close) (near far : ℝ) (left right : Vertex) :
    twoLevelDistance close near far left right =
      twoLevelDistance close near far right left := by
  by_cases heq : left = right
  · subst right
    simp
  · have hreverse : right ≠ left := Ne.symm heq
    by_cases hnear : close left right
    · simp [twoLevelDistance, heq, hreverse, hnear, hclose hnear]
    · have hnotReverse : ¬close right left := fun h => hnear (hclose h)
      simp [twoLevelDistance, heq, hreverse, hnear, hnotReverse]

/-- Positive near and far levels make zero distance equivalent to equality. -/
theorem twoLevelDistance_eq_zero_iff {Vertex : Type*}
    [DecidableEq Vertex] (close : Vertex → Vertex → Prop) [DecidableRel close]
    {near far : ℝ} (hnear : 0 < near) (hfar : 0 < far)
    (left right : Vertex) :
    twoLevelDistance close near far left right = 0 ↔ left = right := by
  by_cases heq : left = right
  · simp [heq]
  · by_cases hclose : close left right <;>
      simp [twoLevelDistance, heq, hclose, hnear.ne', hfar.ne']

/--
Triangle inequality for a two-level distance. The far level may not exceed two
near steps; the near level may not exceed the far level.
-/
theorem twoLevelDistance_triangle {Vertex : Type*}
    [DecidableEq Vertex] (close : Vertex → Vertex → Prop) [DecidableRel close]
    {near far : ℝ} (hnear : 0 ≤ near) (hnearFar : near ≤ far)
    (hfarTwoNear : far ≤ near + near)
    (left middle right : Vertex) :
    twoLevelDistance close near far left right ≤
      twoLevelDistance close near far left middle +
        twoLevelDistance close near far middle right := by
  by_cases hlm : left = middle
  · subst middle
    simp
  by_cases hmr : middle = right
  · subst right
    simp
  by_cases hlr : left = right
  · subst right
    simp only [twoLevelDistance, if_neg hlm, if_neg hmr]
    split_ifs <;> linarith
  simp only [twoLevelDistance, if_neg hlm, if_neg hmr, if_neg hlr]
  split_ifs <;> linarith

end AppliedModelingLib
