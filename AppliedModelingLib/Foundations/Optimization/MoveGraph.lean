import Mathlib.Logic.Relation
import AppliedModelingLib.Foundations.Optimization.Certificate

namespace AppliedModelingLib
namespace Optimization

/-!
# Move-Graph Optimality

Reusable wrappers for exchange and local-move optimization proofs.

## Main declarations

- `MovePreservesFeasibility`: one move keeps the point feasible.
- `MoveNonincreasingOn`: each feasible move weakly decreases an objective.
- `MoveNondecreasingOn`: each feasible move weakly increases an objective.
- `isMaximizerOn_of_reachable_nonincreasing`: reachability plus nonincreasing
  moves proves global maximization.
- `isMinimizerOn_of_reachable_nondecreasing`: reachability plus nondecreasing
  moves proves global minimization.
-/

/-- Every feasible move remains feasible. -/
def MovePreservesFeasibility {α : Type*} (feasible : α → Prop)
    (move : α → α → Prop) : Prop :=
  ∀ {x y}, feasible x → move x y → feasible y

/-- The objective weakly decreases along every feasible move. -/
def MoveNonincreasingOn {α : Type*} (feasible : α → Prop)
    (move : α → α → Prop) (objective : α → ℝ) : Prop :=
  ∀ {x y}, feasible x → move x y → objective y ≤ objective x

/-- The objective weakly increases along every feasible move. -/
def MoveNondecreasingOn {α : Type*} (feasible : α → Prop)
    (move : α → α → Prop) (objective : α → ℝ) : Prop :=
  ∀ {x y}, feasible x → move x y → objective x ≤ objective y

namespace MoveNonincreasingOn

variable {α : Type*} {feasible : α → Prop} {move : α → α → Prop}
  {objective : α → ℝ} {x y : α}

/--
If moves preserve feasibility and never increase the objective, then any
reachable point has objective at most the starting point.
-/
theorem le_and_feasible_of_reflTransGen
    (hstep : MoveNonincreasingOn feasible move objective)
    (hpreserve : MovePreservesFeasibility feasible move)
    (hpath : Relation.ReflTransGen move x y) :
    feasible x → objective y ≤ objective x ∧ feasible y := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl =>
      intro hx
      exact ⟨le_rfl, hx⟩
  | single hmove =>
      intro hx
      exact ⟨hstep hx hmove, hpreserve hx hmove⟩
  | trans _ _ hleft hright =>
      intro hx
      rcases hleft hx with ⟨hle_left, hmid⟩
      rcases hright hmid with ⟨hle_right, hy⟩
      exact ⟨le_trans hle_right hle_left, hy⟩

/-- Reachable points have objective at most the starting point. -/
theorem le_of_reflTransGen
    (hstep : MoveNonincreasingOn feasible move objective)
    (hpreserve : MovePreservesFeasibility feasible move)
    (hpath : Relation.ReflTransGen move x y) (hx : feasible x) :
    objective y ≤ objective x :=
  (hstep.le_and_feasible_of_reflTransGen hpreserve hpath hx).1

end MoveNonincreasingOn

namespace MoveNondecreasingOn

variable {α : Type*} {feasible : α → Prop} {move : α → α → Prop}
  {objective : α → ℝ} {x y : α}

/--
If moves preserve feasibility and never decrease the objective, then any
reachable point has objective at least the starting point.
-/
theorem le_and_feasible_of_reflTransGen
    (hstep : MoveNondecreasingOn feasible move objective)
    (hpreserve : MovePreservesFeasibility feasible move)
    (hpath : Relation.ReflTransGen move x y) :
    feasible x → objective x ≤ objective y ∧ feasible y := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl =>
      intro hx
      exact ⟨le_rfl, hx⟩
  | single hmove =>
      intro hx
      exact ⟨hstep hx hmove, hpreserve hx hmove⟩
  | trans _ _ hleft hright =>
      intro hx
      rcases hleft hx with ⟨hle_left, hmid⟩
      rcases hright hmid with ⟨hle_right, hy⟩
      exact ⟨le_trans hle_left hle_right, hy⟩

/-- Reachable points have objective at least the starting point. -/
theorem le_of_reflTransGen
    (hstep : MoveNondecreasingOn feasible move objective)
    (hpreserve : MovePreservesFeasibility feasible move)
    (hpath : Relation.ReflTransGen move x y) (hx : feasible x) :
    objective x ≤ objective y :=
  (hstep.le_and_feasible_of_reflTransGen hpreserve hpath hx).1

end MoveNondecreasingOn

/--
If every feasible point is reachable from `x` by feasible objective-nonincreasing
moves, then `x` is a global maximizer.
-/
theorem isMaximizerOn_of_reachable_nonincreasing
    {α : Type*} {feasible : α → Prop} {move : α → α → Prop}
    {objective : α → ℝ} {x : α}
    (hx : feasible x)
    (hpreserve : MovePreservesFeasibility feasible move)
    (hstep : MoveNonincreasingOn feasible move objective)
    (hreach : ∀ y, feasible y → Relation.ReflTransGen move x y) :
    IsMaximizerOn feasible objective x := by
  constructor
  · exact hx
  · intro y hy
    exact hstep.le_of_reflTransGen hpreserve (hreach y hy) hx

/--
If every feasible point is reachable from `x` by feasible objective-nondecreasing
moves, then `x` is a global minimizer.
-/
theorem isMinimizerOn_of_reachable_nondecreasing
    {α : Type*} {feasible : α → Prop} {move : α → α → Prop}
    {objective : α → ℝ} {x : α}
    (hx : feasible x)
    (hpreserve : MovePreservesFeasibility feasible move)
    (hstep : MoveNondecreasingOn feasible move objective)
    (hreach : ∀ y, feasible y → Relation.ReflTransGen move x y) :
    IsMinimizerOn feasible objective x := by
  constructor
  · exact hx
  · intro y hy
    exact hstep.le_of_reflTransGen hpreserve (hreach y hy) hx

end Optimization
end AppliedModelingLib
