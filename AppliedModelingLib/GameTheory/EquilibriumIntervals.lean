import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Monotone

/-!
# Equilibrium Sets That Are Upper Intervals

This module isolates the order-theoretic seam behind equilibrium claims of the
form “once one action is an equilibrium, every larger feasible action up to a
maximal action is also an equilibrium.”  Those premises determine an upper
interval, but do not by themselves determine whether its lower endpoint is
included.  Relative closedness supplies exactly the missing endpoint fact.

The proofs use Mathlib's conditionally complete real order, in particular
`exists_lt_of_csInf_lt` and `IsClosed.csInf_mem`, from
[`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean)
and
[`Mathlib/Topology/Order/Monotone.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/Monotone.lean),
in the Apache-2.0-licensed
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
repository at pinned commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external code or proof is copied or ported.
-/

namespace AppliedModelingLib

open Set

/--
A set of real actions is upward closed through `upper` when membership of one
action implies membership of every weakly larger action up to `upper`.
-/
def IsUpwardClosedThrough (actions : Set ℝ) (upper : ℝ) : Prop :=
  ∀ ⦃lower higher⦄, lower ∈ actions → lower ≤ higher → higher ≤ upper →
    higher ∈ actions

/--
If the infimum belongs to a bounded feasible equilibrium set that is upward
closed through its top endpoint, the set is the corresponding closed interval.
-/
theorem eq_Icc_csInf_of_isUpwardClosedThrough_of_csInf_mem
    {actions : Set ℝ} {feasibleLower feasibleUpper : ℝ}
    (hsubset : actions ⊆ Icc feasibleLower feasibleUpper)
    (hupper : feasibleUpper ∈ actions)
    (hupward : IsUpwardClosedThrough actions feasibleUpper)
    (hinf : sInf actions ∈ actions) :
    actions = Icc (sInf actions) feasibleUpper := by
  have hbounded : BddBelow actions :=
    ⟨feasibleLower, fun action haction => (hsubset haction).1⟩
  apply Set.Subset.antisymm
  · intro action haction
    exact ⟨csInf_le hbounded haction, (hsubset haction).2⟩
  · intro action haction
    exact hupward hinf haction.1 haction.2

/--
If the infimum does not belong to the same bounded upward equilibrium set, the
set is the corresponding lower-open, upper-closed interval.
-/
theorem eq_Ioc_csInf_of_isUpwardClosedThrough_of_csInf_not_mem
    {actions : Set ℝ} {feasibleLower feasibleUpper : ℝ}
    (hsubset : actions ⊆ Icc feasibleLower feasibleUpper)
    (hupper : feasibleUpper ∈ actions)
    (hupward : IsUpwardClosedThrough actions feasibleUpper)
    (hinf : sInf actions ∉ actions) :
    actions = Ioc (sInf actions) feasibleUpper := by
  have hnonempty : actions.Nonempty := ⟨feasibleUpper, hupper⟩
  have hbounded : BddBelow actions :=
    ⟨feasibleLower, fun action haction => (hsubset haction).1⟩
  apply Set.Subset.antisymm
  · intro action haction
    have hinf_le : sInf actions ≤ action := csInf_le hbounded haction
    have hinf_ne : sInf actions ≠ action := by
      intro heq
      apply hinf
      simpa [heq] using haction
    exact ⟨lt_of_le_of_ne hinf_le hinf_ne, (hsubset haction).2⟩
  · intro action haction
    obtain ⟨lower, hlower, hlower_action⟩ :=
      exists_lt_of_csInf_lt hnonempty haction.1
    exact hupward hlower hlower_action.le haction.2

/--
The exact conclusion of bounded upward closure: the equilibrium set has a
lower endpoint between the feasible endpoints and is either closed or open at
that endpoint.  No topological regularity is assumed.
-/
theorem exists_eq_Icc_or_eq_Ioc_of_isUpwardClosedThrough
    {actions : Set ℝ} {feasibleLower feasibleUpper : ℝ}
    (hsubset : actions ⊆ Icc feasibleLower feasibleUpper)
    (hupper : feasibleUpper ∈ actions)
    (hupward : IsUpwardClosedThrough actions feasibleUpper) :
    ∃ lowerEndpoint ∈ Icc feasibleLower feasibleUpper,
      actions = Icc lowerEndpoint feasibleUpper ∨
        actions = Ioc lowerEndpoint feasibleUpper := by
  have hnonempty : actions.Nonempty := ⟨feasibleUpper, hupper⟩
  have hbounded : BddBelow actions :=
    ⟨feasibleLower, fun action haction => (hsubset haction).1⟩
  have hlower : feasibleLower ≤ sInf actions :=
    le_csInf hnonempty fun action haction => (hsubset haction).1
  have hupperBound : sInf actions ≤ feasibleUpper :=
    csInf_le hbounded hupper
  refine ⟨sInf actions, ⟨hlower, hupperBound⟩, ?_⟩
  by_cases hinf : sInf actions ∈ actions
  · exact Or.inl
      (eq_Icc_csInf_of_isUpwardClosedThrough_of_csInf_mem
        hsubset hupper hupward hinf)
  · exact Or.inr
      (eq_Ioc_csInf_of_isUpwardClosedThrough_of_csInf_not_mem
        hsubset hupper hupward hinf)

/--
A closed bounded equilibrium set satisfying upward closure is a closed
interval.  Closedness is the exact extra premise that rules out the lower-open
alternative.
-/
theorem exists_eq_Icc_of_isClosed_of_isUpwardClosedThrough
    {actions : Set ℝ} {feasibleLower feasibleUpper : ℝ}
    (hsubset : actions ⊆ Icc feasibleLower feasibleUpper)
    (hupper : feasibleUpper ∈ actions)
    (hupward : IsUpwardClosedThrough actions feasibleUpper)
    (hclosed : IsClosed actions) :
    ∃ lowerEndpoint ∈ Icc feasibleLower feasibleUpper,
      actions = Icc lowerEndpoint feasibleUpper := by
  have hnonempty : actions.Nonempty := ⟨feasibleUpper, hupper⟩
  have hbounded : BddBelow actions :=
    ⟨feasibleLower, fun action haction => (hsubset haction).1⟩
  have hinf : sInf actions ∈ actions := hclosed.csInf_mem hnonempty hbounded
  have hlower : feasibleLower ≤ sInf actions :=
    le_csInf hnonempty fun action haction => (hsubset haction).1
  have hupperBound : sInf actions ≤ feasibleUpper :=
    csInf_le hbounded hupper
  exact ⟨sInf actions, ⟨hlower, hupperBound⟩,
    eq_Icc_csInf_of_isUpwardClosedThrough_of_csInf_mem
      hsubset hupper hupward hinf⟩

end AppliedModelingLib
