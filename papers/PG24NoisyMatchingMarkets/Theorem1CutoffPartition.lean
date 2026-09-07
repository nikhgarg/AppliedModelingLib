import PG24NoisyMatchingMarkets.MainTheorems
import Mathlib.Tactic

/-!
# PG24 Theorem 1 cutoff-block repair

The attenuation appendix in `source_tex/proof-attenuating.tex` splits colleges
at the dense-window pivot `P*`.  Its displayed blocks omit colleges with
cutoff exactly `P*`, even though the following dense-window argument treats
those colleges as part of the upper block.  This module uses the repaired
half-open partition: cutoffs strictly below the pivot and cutoffs at or above
the pivot.

This is finite cutoff-vector bookkeeping only.  In particular, it does not
assume any tail bound, cutoff geometry, capacity filling, or atomlessness.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open AppliedModelingLib.Matching

universe u

/-- Colleges in an active block whose cutoff is strictly below a pivot. -/
def theorem1CutoffBelowBlock {College : Type u} [DecidableEq College]
    (active : Finset College) (cutoff : College → ℝ) (pivot : ℝ) :
    Finset College :=
  active.filter (fun c => cutoff c < pivot)

/-- Colleges in an active block whose cutoff is at or above a pivot. -/
def theorem1CutoffAtOrAboveBlock {College : Type u} [DecidableEq College]
    (active : Finset College) (cutoff : College → ℝ) (pivot : ℝ) :
    Finset College :=
  active.filter (fun c => pivot ≤ cutoff c)

/-- The closed dense cutoff window used by the source proof. -/
def theorem1CutoffWindowBlock {College : Type u} [DecidableEq College]
    (active : Finset College) (cutoff : College → ℝ) (pivot width : ℝ) :
    Finset College :=
  active.filter (fun c => pivot ≤ cutoff c ∧ cutoff c ≤ pivot + width)

/--
The repaired low/high cutoff blocks partition the active colleges.  Equality
at the pivot belongs to the upper block, so no cutoff is dropped.

This corrects the block definitions at `proof-attenuating.tex:92-102` and
the analogous Case 2 split at `:251-259`.
-/
theorem theorem1CutoffBelowBlock_union_atOrAboveBlock
    {College : Type u} [DecidableEq College]
    (active : Finset College) (cutoff : College → ℝ) (pivot : ℝ) :
    active = theorem1CutoffBelowBlock active cutoff pivot ∪
      theorem1CutoffAtOrAboveBlock active cutoff pivot := by
  ext c
  simp only [theorem1CutoffBelowBlock, theorem1CutoffAtOrAboveBlock,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hc
    rcases lt_or_ge (cutoff c) pivot with hbelow | hatOrAbove
    · exact Or.inl ⟨hc, hbelow⟩
    · exact Or.inr ⟨hc, hatOrAbove⟩
  · intro hc
    rcases hc with hbelow | hatOrAbove
    · exact hbelow.1
    · exact hatOrAbove.1

/-- The repaired low and upper cutoff blocks are disjoint. -/
theorem theorem1CutoffBelowBlock_disjoint_atOrAboveBlock
    {College : Type u} [DecidableEq College]
    (active : Finset College) (cutoff : College → ℝ) (pivot : ℝ) :
    Disjoint (theorem1CutoffBelowBlock active cutoff pivot)
      (theorem1CutoffAtOrAboveBlock active cutoff pivot) := by
  rw [Finset.disjoint_left]
  intro c hbelow hatOrAbove
  exact (not_lt_of_ge (Finset.mem_filter.mp hatOrAbove).2)
    (Finset.mem_filter.mp hbelow).2

/--
Every cutoff in the source's closed dense window belongs to the repaired upper
block.  Unlike the source's open `(P*, infinity)` block, this includes a
cutoff exactly equal to `P*`.

This is the set inclusion needed at `proof-attenuating.tex:139-145`.
-/
theorem theorem1CutoffWindowBlock_subset_atOrAboveBlock
    {College : Type u} [DecidableEq College]
    (active : Finset College) (cutoff : College → ℝ) (pivot width : ℝ) :
    theorem1CutoffWindowBlock active cutoff pivot width ⊆
      theorem1CutoffAtOrAboveBlock active cutoff pivot := by
  intro c hc
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2.1⟩

/--
Capacity decomposes exactly across the repaired cutoff partition.  This is
only finite capacity arithmetic; an application to matched mass must still
supply the paper model's exact-fill bridge separately.
-/
theorem theorem1_activeCapacity_eq_below_add_atOrAbove
    {College : Type u} [DecidableEq College]
    (active : Finset College) (capacity cutoff : College → ℝ) (pivot : ℝ) :
    activeCapacity active capacity =
      activeCapacity (theorem1CutoffBelowBlock active cutoff pivot) capacity +
        activeCapacity (theorem1CutoffAtOrAboveBlock active cutoff pivot)
          capacity :=
  activeCapacity_eq_add_of_partition capacity
    (theorem1CutoffBelowBlock_union_atOrAboveBlock active cutoff pivot)
    (theorem1CutoffBelowBlock_disjoint_atOrAboveBlock active cutoff pivot)

end

end PG24NoisyMatchingMarkets
