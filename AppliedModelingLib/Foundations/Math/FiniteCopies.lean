import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Finite copy expansions

This module turns a natural-valued weight on a finite base type into a literal
finite population of distinguishable copies.  It supplies the elementary
counting and summation bridge used by reductions that are described with
integer multiplicities but analyzed as weighted finite sums.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- `FiniteCopies weight` contains `weight base` distinguishable copies of each base point. -/
abbrev FiniteCopies {Base : Type*} (weight : Base → ℕ) :=
  Σ base : Base, Fin (weight base)

/-- The size of a finite copy expansion is the sum of its multiplicities. -/
@[simp] theorem finiteCopies_card
    {Base : Type*} [Fintype Base] (weight : Base → ℕ) :
    Fintype.card (FiniteCopies weight) = ∑ base : Base, weight base := by
  rw [Fintype.card_sigma]
  simp

/-- Summing a lifted real-valued observable over copies equals its multiplicity-weighted sum. -/
theorem finiteCopies_sum_lift
    {Base : Type*} [Fintype Base] (weight : Base → ℕ) (value : Base → ℝ) :
    (∑ copy : FiniteCopies weight, value copy.1) =
      ∑ base : Base, (weight base : ℝ) * value base := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro base _
  simp

/-- Counting copies satisfying a base predicate is the sum of their selected multiplicities. -/
theorem finiteCopies_sum_indicator
    {Base : Type*} [Fintype Base] (weight : Base → ℕ) (predicate : Base → Prop)
    [DecidablePred predicate] :
    (∑ copy : FiniteCopies weight, if predicate copy.1 then 1 else 0) =
      ∑ base : Base, if predicate base then weight base else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro base _
  by_cases h : predicate base <;> simp [h]

/-- The real-valued indicator count is the cast of the corresponding natural copy count. -/
theorem finiteCopies_sum_indicator_real
    {Base : Type*} [Fintype Base] (weight : Base → ℕ) (predicate : Base → Prop)
    [DecidablePred predicate] :
    (∑ copy : FiniteCopies weight, if predicate copy.1 then (1 : ℝ) else 0) =
      ∑ base : Base, if predicate base then (weight base : ℝ) else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro base _
  by_cases h : predicate base <;> simp [h]

/-- A constant contribution over a finite predicate support is its cardinality times the constant. -/
theorem fintype_sum_indicator_const_real
    {Base : Type*} [Fintype Base] (predicate : Base → Prop)
    [DecidablePred predicate] (constant : ℝ) :
    (∑ base : Base, if predicate base then constant else 0) =
      (({base | predicate base} : Set Base).ncard : ℝ) * constant := by
  classical
  have htoFinset : ({base | predicate base} : Set Base).toFinset =
      Finset.univ.filter predicate := by
    ext base
    simp
  rw [Set.ncard_eq_toFinset_card', htoFinset]
  change (∑ base ∈ Finset.univ, if predicate base then constant else 0) = _
  rw [← Finset.sum_filter]
  simp

end AppliedModelingLib
