import SeshadriUgander2020IIATesting.Perturbations

/-!
# The alternating-cycle obstruction in Lemma 2

The middle part of the source proof of Lemma 2 informally follows a cycle and
describes a ``waterbed effect''.  This file makes that step algebraic.  Along
an oriented simple cycle, the products of the alternating `w_C * γ_x` terms
are equal (a cyclic permutation only reorders the `γ` factors).  Consequently
they cannot all lie respectively above and below one common positive midpoint.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace CycleAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The product identity obtained by alternating around a cycle.  `next` is
the successor permutation of the item vertices; no analytic assumption is
used here. -/
theorem alternating_product_eq (next : Equiv.Perm ι) (w γ : ι → ℝ) :
    (∏ i, w i * γ i) = ∏ i, w i * γ (next i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [next.prod_comp Finset.univ γ (by simp)]

/-- Source Lemma 2's local sign obstruction.  If all `w` and `γ` values are
nonnegative, an alternating cycle cannot make every high-sign entry exceed a
positive midpoint while making every low-sign entry fall below it. -/
theorem exists_alternating_sign_failure (next : Equiv.Perm ι) (w γ : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hγ_nonneg : ∀ i, 0 ≤ γ i)
    (midpoint : ℝ) (hmidpoint_pos : 0 < midpoint) :
    ∃ i, w i * γ i ≤ midpoint ∨ midpoint ≤ w i * γ (next i) := by
  by_contra hfailure
  push Not at hfailure
  have hhigh : ∀ i, midpoint < w i * γ i := fun i => (hfailure i).1
  have hlow : ∀ i, w i * γ (next i) < midpoint := fun i => (hfailure i).2
  have hw_pos : ∀ i, 0 < w i := by
    intro i
    exact pos_of_mul_pos_left (hmidpoint_pos.trans (hhigh i)) (hγ_nonneg i)
  have hγ_pos : ∀ i, 0 < γ i := by
    intro i
    exact pos_of_mul_pos_right (hmidpoint_pos.trans (hhigh i)) (hw_nonneg i)
  have hlow_pos : ∀ i, 0 < w i * γ (next i) := by
    intro i
    exact mul_pos (hw_pos i) (hγ_pos (next i))
  have hproduct_lt : (∏ i, w i * γ (next i)) < ∏ i, w i * γ i := by
    apply Finset.prod_lt_prod
    · intro i _
      exact hlow_pos i
    · intro i _
      exact le_of_lt ((hlow i).trans (hhigh i))
    · obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨i, Finset.mem_univ _, (hlow i).trans (hhigh i)⟩
  have hproduct_eq := alternating_product_eq next w γ
  exact (ne_of_lt hproduct_lt) hproduct_eq.symm

/-- A high-sign failure incurs at least the indicated gap in absolute error. -/
theorem high_sign_error_lower_bound {z midpoint gap : ℝ}
    (hgap_nonneg : 0 ≤ gap) (hz : z ≤ midpoint) :
    gap ≤ |z - (midpoint + gap)| := by
  rw [abs_of_nonpos]
  · linarith
  · linarith

/-- A low-sign failure incurs at least the indicated gap in absolute error. -/
theorem low_sign_error_lower_bound {z midpoint gap : ℝ}
    (hgap_nonneg : 0 ≤ gap) (hz : midpoint ≤ z) :
    gap ≤ |z - (midpoint - gap)| := by
  rw [abs_of_nonneg]
  · linarith
  · linarith

/-- The formal finite-cycle version of the local lower bound in the proof of
source Lemma 2.  At least one alternating incidence contributes `gap` to the
absolute-error objective. -/
theorem alternating_cycle_loss_lower_bound (next : Equiv.Perm ι) (w γ : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hγ_nonneg : ∀ i, 0 ≤ γ i)
    (midpoint gap : ℝ) (hmidpoint_pos : 0 < midpoint) (hgap_nonneg : 0 ≤ gap) :
    gap ≤ ∑ i, (|w i * γ i - (midpoint + gap)| +
      |w i * γ (next i) - (midpoint - gap)|) := by
  obtain ⟨i, hhigh | hlow⟩ :=
    exists_alternating_sign_failure next w γ hw_nonneg hγ_nonneg midpoint hmidpoint_pos
  · calc
      gap ≤ |w i * γ i - (midpoint + gap)| :=
        high_sign_error_lower_bound hgap_nonneg hhigh
      _ ≤ |w i * γ i - (midpoint + gap)| +
          |w i * γ (next i) - (midpoint - gap)| :=
        le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ ∑ j, (|w j * γ j - (midpoint + gap)| +
          |w j * γ (next j) - (midpoint - gap)|) :=
        Finset.single_le_sum
          (f := fun j => |w j * γ j - (midpoint + gap)| +
            |w j * γ (next j) - (midpoint - gap)|)
          (fun j _ => by positivity) (Finset.mem_univ i)
  · calc
      gap ≤ |w i * γ (next i) - (midpoint - gap)| :=
        low_sign_error_lower_bound hgap_nonneg hlow
      _ ≤ |w i * γ i - (midpoint + gap)| +
          |w i * γ (next i) - (midpoint - gap)| :=
        le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ ∑ j, (|w j * γ j - (midpoint + gap)| +
          |w j * γ (next j) - (midpoint - gap)|) :=
        Finset.single_le_sum
          (f := fun j => |w j * γ j - (midpoint + gap)| +
            |w j * γ (next j) - (midpoint - gap)|)
          (fun j _ => by positivity) (Finset.mem_univ i)

/-- The same local obstruction for the opposite orientation of a cycle.  It
is not a separate source assumption: reindexing the forward result along the
inverse cycle permutation exchanges the high and low incidences. -/
theorem alternating_cycle_loss_lower_bound_reverse (next : Equiv.Perm ι)
    (w γ : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hγ_nonneg : ∀ i, 0 ≤ γ i)
    (midpoint gap : ℝ) (hmidpoint_pos : 0 < midpoint) (hgap_nonneg : 0 ≤ gap) :
    gap ≤ ∑ i, (|w i * γ i - (midpoint - gap)| +
      |w i * γ (next i) - (midpoint + gap)|) := by
  have hforward := alternating_cycle_loss_lower_bound next.symm
    (fun i => w (next.symm i)) γ
    (fun i => hw_nonneg (next.symm i)) hγ_nonneg midpoint gap hmidpoint_pos hgap_nonneg
  have hreindex :
      (∑ i, (|w (next.symm i) * γ i - (midpoint + gap)| +
        |w (next.symm i) * γ (next.symm i) - (midpoint - gap)|)) =
        ∑ i, (|w i * γ i - (midpoint - gap)| +
          |w i * γ (next i) - (midpoint + gap)|) := by
    refine (Fintype.sum_equiv next _ _ ?_).symm
    intro i
    rw [next.symm_apply_apply]
    ring_nf
  rw [hreindex] at hforward
  exact hforward

/-- Both possible orientations of a cycle satisfy the same local absolute
loss bound.  The real sign is deliberately explicit so this theorem can be
applied to the `{-1,1}` orientation signs in Lemma 2. -/
theorem alternating_cycle_loss_lower_bound_signed (next : Equiv.Perm ι)
    (w γ : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hγ_nonneg : ∀ i, 0 ≤ γ i)
    (midpoint gap s : ℝ) (hmidpoint_pos : 0 < midpoint) (hgap_nonneg : 0 ≤ gap)
    (hs : s = 1 ∨ s = -1) :
    gap ≤ ∑ i, (|w i * γ i - (midpoint + s * gap)| +
      |w i * γ (next i) - (midpoint - s * gap)|) := by
  rcases hs with hs | hs
  · subst s
    simpa using alternating_cycle_loss_lower_bound next w γ hw_nonneg hγ_nonneg
      midpoint gap hmidpoint_pos hgap_nonneg
  · subst s
    simpa using alternating_cycle_loss_lower_bound_reverse next w γ hw_nonneg hγ_nonneg
      midpoint gap hmidpoint_pos hgap_nonneg

end CycleAlgebra

end SeshadriUgander2020IIATesting
