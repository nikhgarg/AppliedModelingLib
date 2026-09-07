import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite self-bounding functions

Maurer--Pontil's empirical-variance argument invokes a self-bounding tail
theorem for functions of independent variables.  This module supplies the
finite replacement infimum and the *deterministic* hypotheses of that theorem
on a finite carrier.  A probability tail theorem must still be derived from
these verified hypotheses; these definitions do not stand in for one.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The least value of an objective after replacing one coordinate by any
member of its finite input carrier. -/
noncomputable def finiteCoordinateReplacementInf
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (sample : Fin n → α) (coordinate : Fin n) : ℝ :=
  let replacements : Finset ℝ := Finset.univ.image fun value : α =>
    objective (Function.update sample coordinate value)
  replacements.min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Replacing a coordinate by any particular carrier value bounds the finite
replacement infimum from above. -/
theorem finiteCoordinateReplacementInf_le_replacement
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (sample : Fin n → α) (coordinate : Fin n)
    (value : α) :
    finiteCoordinateReplacementInf objective sample coordinate ≤
      objective (Function.update sample coordinate value) := by
  unfold finiteCoordinateReplacementInf
  dsimp
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩

/-- Replacing the distinguished coordinate before taking its replacement
infimum does not change the available set of replacement objectives. -/
theorem finiteCoordinateReplacementInf_update
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (sample : Fin n → α) (coordinate : Fin n)
    (value : α) :
    finiteCoordinateReplacementInf objective
      (Function.update sample coordinate value) coordinate =
      finiteCoordinateReplacementInf objective sample coordinate := by
  simp [finiteCoordinateReplacementInf, Function.update_idem]

/-- On a finite carrier, the replacement infimum is attained by an actual
replacement value. -/
theorem exists_replacement_eq_finiteCoordinateReplacementInf
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (sample : Fin n → α) (coordinate : Fin n) :
    ∃ value : α,
      objective (Function.update sample coordinate value) =
        finiteCoordinateReplacementInf objective sample coordinate := by
  unfold finiteCoordinateReplacementInf
  dsimp
  have hmem :
      (Finset.univ.image fun value : α =>
        objective (Function.update sample coordinate value)).min'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) ∈
        Finset.univ.image fun value : α =>
          objective (Function.update sample coordinate value) :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨value, _, hvalue⟩
  exact ⟨value, hvalue⟩

/-- The loss incurred relative to the best one-coordinate replacement. -/
noncomputable def finiteCoordinateReplacementDrop
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (sample : Fin n → α) (coordinate : Fin n) : ℝ :=
  objective sample - finiteCoordinateReplacementInf objective sample coordinate

/-- A replacement drop is nonnegative because retaining the old coordinate is
one of the permitted replacements. -/
theorem finiteCoordinateReplacementDrop_nonneg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (sample : Fin n → α) (coordinate : Fin n) :
    0 ≤ finiteCoordinateReplacementDrop objective sample coordinate := by
  unfold finiteCoordinateReplacementDrop
  have hle := finiteCoordinateReplacementInf_le_replacement
    objective sample coordinate (sample coordinate)
  simpa using sub_nonneg.mpr hle

/-- The deterministic self-bounding conditions used by the source tail
argument.  They are facts to prove about an objective, never probabilistic
assumptions discharged by a certificate. -/
structure FiniteSelfBounding
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (objective : (Fin n → α) → ℝ) (scale : ℝ) : Prop where
  drop_le_one : ∀ sample coordinate,
    finiteCoordinateReplacementDrop objective sample coordinate ≤ 1
  sum_sq_drop_le : ∀ sample,
    (∑ coordinate : Fin n,
      (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2) ≤
        scale * objective sample

/-- A positive self-bounding scale forces the objective itself to be
nonnegative: its squared replacement-drop sum is nonnegative and bounded
above by `scale * objective`. -/
theorem FiniteSelfBounding.objective_nonneg_of_pos_scale
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {objective : (Fin n → α) → ℝ} {scale : ℝ}
    (hself : FiniteSelfBounding objective scale) (hscale : 0 < scale)
    (sample : Fin n → α) :
    0 ≤ objective sample := by
  have hsquares_nonneg : 0 ≤ ∑ coordinate : Fin n,
      (finiteCoordinateReplacementDrop objective sample coordinate) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hscaled : 0 ≤ scale * objective sample :=
    le_trans hsquares_nonneg (hself.sum_sq_drop_le sample)
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hscaled) hscale

/-- A symmetric zero-diagonal double sum separates into the two rows and
columns involving one chosen coordinate plus the untouched minor.  This is
the algebraic replacement identity used in the empirical-variance
self-bounding verification. -/
theorem finiteDoubleSum_decompose_at
    {β : Type*} {n : ℕ} (kernel : β → β → ℝ)
    (kernel_symmetric : ∀ left right, kernel left right = kernel right left)
    (kernel_diagonal : ∀ value, kernel value value = 0)
    (sample : Fin n → β) (coordinate : Fin n) :
    (∑ left : Fin n, ∑ right : Fin n, kernel (sample left) (sample right)) =
      2 * (∑ right : Fin n, kernel (sample coordinate) (sample right)) +
        ∑ left ∈ Finset.univ.erase coordinate,
          ∑ right ∈ Finset.univ.erase coordinate,
            kernel (sample left) (sample right) := by
  classical
  have houter :
      (∑ left : Fin n, ∑ right : Fin n, kernel (sample left) (sample right)) =
        (∑ right : Fin n, kernel (sample coordinate) (sample right)) +
          ∑ left ∈ Finset.univ.erase coordinate,
            ∑ right : Fin n, kernel (sample left) (sample right) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ coordinate)]
  have hinner (left : Fin n) :
      (∑ right : Fin n, kernel (sample left) (sample right)) =
        kernel (sample left) (sample coordinate) +
          ∑ right ∈ Finset.univ.erase coordinate,
            kernel (sample left) (sample right) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ coordinate)]
  have hrow :
      (∑ right : Fin n, kernel (sample coordinate) (sample right)) =
        ∑ right ∈ Finset.univ.erase coordinate,
          kernel (sample coordinate) (sample right) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ coordinate),
      kernel_diagonal]
    ring
  have hcolumn :
      (∑ left ∈ Finset.univ.erase coordinate,
        kernel (sample left) (sample coordinate)) =
        ∑ right ∈ Finset.univ.erase coordinate,
          kernel (sample coordinate) (sample right) := by
    apply Finset.sum_congr rfl
    intro index _
    exact kernel_symmetric _ _
  calc
    (∑ left : Fin n, ∑ right : Fin n, kernel (sample left) (sample right)) =
        (∑ right : Fin n, kernel (sample coordinate) (sample right)) +
          ∑ left ∈ Finset.univ.erase coordinate,
            ∑ right : Fin n, kernel (sample left) (sample right) := houter
    _ = (∑ right : Fin n, kernel (sample coordinate) (sample right)) +
          ∑ left ∈ Finset.univ.erase coordinate,
            (kernel (sample left) (sample coordinate) +
              ∑ right ∈ Finset.univ.erase coordinate,
                kernel (sample left) (sample right)) := by
          apply congrArg (fun total : ℝ =>
            (∑ right : Fin n, kernel (sample coordinate) (sample right)) + total)
          apply Finset.sum_congr rfl
          intro left _
          exact hinner left
    _ = (∑ right : Fin n, kernel (sample coordinate) (sample right)) +
          (∑ left ∈ Finset.univ.erase coordinate,
            kernel (sample left) (sample coordinate)) +
          ∑ left ∈ Finset.univ.erase coordinate,
            ∑ right ∈ Finset.univ.erase coordinate,
              kernel (sample left) (sample right) := by
          rw [Finset.sum_add_distrib]
          ring
    _ = 2 * (∑ right : Fin n, kernel (sample coordinate) (sample right)) +
          ∑ left ∈ Finset.univ.erase coordinate,
            ∑ right ∈ Finset.univ.erase coordinate,
              kernel (sample left) (sample right) := by
          rw [hcolumn, ← hrow]
          ring

/-- Changing one coordinate changes a symmetric zero-diagonal double sum by
twice the change in that coordinate's row. -/
theorem finiteDoubleSum_sub_update_eq_two_rowDifference
    {β : Type*} {n : ℕ} (kernel : β → β → ℝ)
    (kernel_symmetric : ∀ left right, kernel left right = kernel right left)
    (kernel_diagonal : ∀ value, kernel value value = 0)
    (sample : Fin n → β) (coordinate : Fin n) (value : β) :
    (∑ left : Fin n, ∑ right : Fin n, kernel (sample left) (sample right)) -
        (∑ left : Fin n, ∑ right : Fin n,
          kernel ((Function.update sample coordinate value) left)
            ((Function.update sample coordinate value) right)) =
      2 * ((∑ right : Fin n, kernel (sample coordinate) (sample right)) -
        ∑ right : Fin n,
          kernel ((Function.update sample coordinate value) coordinate)
            ((Function.update sample coordinate value) right)) := by
  classical
  let updated := Function.update sample coordinate value
  have hminor :
      (∑ left ∈ Finset.univ.erase coordinate,
        ∑ right ∈ Finset.univ.erase coordinate,
          kernel (updated left) (updated right)) =
        ∑ left ∈ Finset.univ.erase coordinate,
          ∑ right ∈ Finset.univ.erase coordinate,
            kernel (sample left) (sample right) := by
    apply Finset.sum_congr rfl
    intro left hleft
    have hleft_ne : left ≠ coordinate := (Finset.mem_erase.mp hleft).1
    apply Finset.sum_congr rfl
    intro right hright
    have hright_ne : right ≠ coordinate := (Finset.mem_erase.mp hright).1
    simp [updated, hleft_ne, hright_ne]
  change
    (∑ left : Fin n, ∑ right : Fin n, kernel (sample left) (sample right)) -
        (∑ left : Fin n, ∑ right : Fin n, kernel (updated left) (updated right)) =
      2 * ((∑ right : Fin n, kernel (sample coordinate) (sample right)) -
        ∑ right : Fin n, kernel (updated coordinate) (updated right))
  rw [finiteDoubleSum_decompose_at kernel kernel_symmetric kernel_diagonal sample coordinate,
    finiteDoubleSum_decompose_at kernel kernel_symmetric kernel_diagonal updated coordinate]
  let oldRow : ℝ := ∑ right : Fin n, kernel (sample coordinate) (sample right)
  let newRow : ℝ := ∑ right : Fin n, kernel (updated coordinate) (updated right)
  let oldMinor : ℝ := ∑ left ∈ Finset.univ.erase coordinate,
    ∑ right ∈ Finset.univ.erase coordinate,
      kernel (sample left) (sample right)
  let newMinor : ℝ := ∑ left ∈ Finset.univ.erase coordinate,
    ∑ right ∈ Finset.univ.erase coordinate,
      kernel (updated left) (updated right)
  have hminor' : newMinor = oldMinor := hminor
  have hgoal : 2 * oldRow + oldMinor - (2 * newRow + newMinor) =
      2 * (oldRow - newRow) := by
    rw [hminor']
    ring
  simpa only [oldRow, newRow, oldMinor, newMinor] using hgoal

end AppliedModelingLib
