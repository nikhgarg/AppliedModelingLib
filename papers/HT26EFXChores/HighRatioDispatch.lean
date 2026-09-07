import HT26EFXChores.B1HighDispatch
import HT26EFXChores.B2Dispatch
import HT26EFXChores.B3OuterDispatch
import HT26EFXChores.M01M2Combination

/-!
# Complete normalized high-ratio dispatcher

For `r > 2`, the source partitions the M01-pool cardinality modulo four.
The `b = 0,1,2,3` routes are proved in their respective source-case modules;
this file performs only the arithmetic dispatch.

Source: `EFXadditivechores.tex`, Cases B.1--B.4.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Every normalized four-agent `\{1,r\}` chore instance with `r > 2` admits
an EFX allocation. -/
theorem existsEfxOfOneOrR_highRatio
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  let a : ℕ := (m01ChorePool cost chores).card / 4
  let b : ℕ := (m01ChorePool cost chores).card % 4
  have hcard : (m01ChorePool cost chores).card = 4 * a + b := by
    dsimp [a, b]
    have hmod := Nat.mod_add_div (m01ChorePool cost chores).card 4
    omega
  have hb : b < 4 := by
    dsimp [b]
    exact Nat.mod_lt _ (by omega)
  interval_cases b
  · have hzero : (m01ChorePool cost chores).card = 4 * a := by omega
    exact existsEfxOfOneOrR_b0 Item r cost chores a hr hcost hzero
  · have hone : (m01ChorePool cost chores).card = 4 * a + 1 := by omega
    exact existsEfxOfOneOrR_b1 Item r cost chores a hr hcost hone
  · have htwo : (m01ChorePool cost chores).card = 4 * a + 2 := by omega
    exact existsEfxOfOneOrR_b2 Item r cost chores a hr hcost htwo
  · have hthree : (m01ChorePool cost chores).card = 4 * a + 3 := by omega
    exact existsEfxOfOneOrR_b3 Item r cost chores a hr hcost hthree

end HT26EFXChores
