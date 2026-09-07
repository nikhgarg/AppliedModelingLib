import AppliedModelingLib.Foundations.Probability.RealDistribution

import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Finite Low-Mass Partitions of Real Intervals

This file packages finite measurable partitions of intervals `(a, b]` for a
finite real measure.  It is designed for cake-cutting reductions where point
masses have first been made small enough that a moving-cut construction can
produce finitely many pieces of mass at most a requested cap.
-/

/-- A finite measurable partition of `(a, b]` whose pieces have `μ.real` mass at most `α`. -/
structure RealIntervalPartition (μ : Measure ℝ) (α a b : ℝ) where
  Piece : Type
  instFintype : Fintype Piece
  instDecidableEq : DecidableEq Piece
  pieceSet : Piece → Set ℝ
  measurable_piece : ∀ piece, MeasurableSet (pieceSet piece)
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ pieceSet
  cover : Set.iUnion pieceSet = Ioc a b
  piece_mass_le : ∀ piece, μ.real (pieceSet piece) ≤ α

namespace RealIntervalPartition

variable {μ : Measure ℝ} {α a b c : ℝ}

/-- The one-piece partition used when `(a, b]` is already small. -/
def single (hsmall : intervalOCMass μ a b ≤ α) :
    RealIntervalPartition μ α a b where
  Piece := PUnit
  instFintype := inferInstance
  instDecidableEq := inferInstance
  pieceSet := fun _ => Ioc a b
  measurable_piece := by
    intro _
    exact measurableSet_Ioc
  pairwiseDisjoint := by
    intro p _ q _ hpq
    cases p
    cases q
    exact (hpq rfl).elim
  cover := by
    ext x
    simp
  piece_mass_le := by
    intro _
    exact hsmall

/-- Add one initial interval piece in front of an existing residual partition. -/
def cons (hac : a ≤ c) (hcb : c ≤ b)
    (hfirst : intervalOCMass μ a c ≤ α)
    (P : RealIntervalPartition μ α c b) :
    RealIntervalPartition μ α a b where
  Piece := PUnit ⊕ P.Piece
  instFintype := by
    letI := P.instFintype
    infer_instance
  instDecidableEq := by
    letI := P.instDecidableEq
    infer_instance
  pieceSet := fun piece =>
    match piece with
    | Sum.inl _ => Ioc a c
    | Sum.inr p => P.pieceSet p
  measurable_piece := by
    intro piece
    cases piece with
    | inl _ => exact measurableSet_Ioc
    | inr p => exact P.measurable_piece p
  pairwiseDisjoint := by
    have hres_subset : ∀ p, P.pieceSet p ⊆ Ioc c b := by
      intro p x hx
      have hxU : x ∈ Set.iUnion P.pieceSet := Set.mem_iUnion.mpr ⟨p, hx⟩
      simpa [P.cover] using hxU
    intro p _ q _ hpq
    cases p with
    | inl pu =>
        cases q with
        | inl qu =>
            cases pu
            cases qu
            exact (hpq rfl).elim
        | inr q =>
            change Disjoint (Ioc a c) (P.pieceSet q)
            rw [Set.disjoint_left]
            intro x hx_first hx_q
            exact (not_lt_of_ge hx_first.2) ((hres_subset q hx_q).1)
    | inr p =>
        cases q with
        | inl qu =>
            change Disjoint (P.pieceSet p) (Ioc a c)
            rw [Set.disjoint_left]
            intro x hx_p hx_first
            exact (not_lt_of_ge hx_first.2) ((hres_subset p hx_p).1)
        | inr q =>
            have hpq' : p ≠ q := by
              intro hpq_eq
              exact hpq (by simp [hpq_eq])
            exact P.pairwiseDisjoint (by simp) (by simp) hpq'
  cover := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨piece, hxpiece⟩
      cases piece with
      | inl _ =>
          exact ⟨hxpiece.1, hxpiece.2.trans hcb⟩
      | inr p =>
          have hxres : x ∈ Set.iUnion P.pieceSet := Set.mem_iUnion.mpr ⟨p, hxpiece⟩
          have hxcb : x ∈ Ioc c b := by simpa [P.cover] using hxres
          exact ⟨lt_of_le_of_lt hac hxcb.1, hxcb.2⟩
    · intro hx
      by_cases hxc : x ≤ c
      · exact Set.mem_iUnion.mpr ⟨Sum.inl PUnit.unit, ⟨hx.1, hxc⟩⟩
      · have hxres : x ∈ Ioc c b := ⟨lt_of_not_ge hxc, hx.2⟩
        have hxU : x ∈ Set.iUnion P.pieceSet := by simpa [P.cover] using hxres
        rcases Set.mem_iUnion.mp hxU with ⟨p, hxp⟩
        exact Set.mem_iUnion.mpr ⟨Sum.inr p, hxp⟩
  piece_mass_le := by
    intro piece
    cases piece with
    | inl _ => exact hfirst
    | inr p => exact P.piece_mass_le p

end RealIntervalPartition

/--
Auxiliary bounded-mass induction: if `(a, b]` has mass at most
`k * (α / 2)` and all point masses are at most `α / 2`, then `(a, b]`
admits a finite partition into pieces of mass at most `α`.
-/
theorem exists_realIntervalPartition_aux
    (μ : Measure ℝ) [IsFiniteMeasure μ] {α : ℝ}
    (hα : 0 < α)
    (hsingleton : ∀ x : ℝ, μ.real ({x} : Set ℝ) ≤ α / 2) :
    ∀ k : ℕ, ∀ a b : ℝ,
      intervalOCMass μ a b ≤ (k : ℝ) * (α / 2) →
        Nonempty (RealIntervalPartition μ α a b) := by
  intro k
  induction k with
  | zero =>
      intro a b hmass
      refine ⟨RealIntervalPartition.single ?_⟩
      have hnonneg : 0 ≤ intervalOCMass μ a b := intervalOCMass_nonneg μ a b
      have hzero : (0 : ℝ) * (α / 2) = 0 := by ring
      have hle_zero : intervalOCMass μ a b ≤ 0 := by simpa [hzero] using hmass
      linarith
  | succ k ih =>
      intro a b hmass
      by_cases hsmall : intervalOCMass μ a b ≤ α
      · exact ⟨RealIntervalPartition.single hsmall⟩
      · have hbig : α < intervalOCMass μ a b := lt_of_not_ge hsmall
        rcases exists_intervalOCMass_gt_half_le_of_gt μ hα hsingleton hbig with
          ⟨c, hac, hcb, hhalf_lt_piece, hfirst⟩
        have hadd :=
          intervalOCMass_add_intervalOCMass_eq μ hac hcb
        have hsucc :
            ((Nat.succ k : ℕ) : ℝ) * (α / 2) =
              (k : ℝ) * (α / 2) + α / 2 := by
          norm_num [Nat.cast_succ]
          ring
        have hres_bound :
            intervalOCMass μ c b ≤ (k : ℝ) * (α / 2) := by
          nlinarith [hmass, hadd, le_of_lt hhalf_lt_piece, hsucc]
        rcases ih c b hres_bound with ⟨P⟩
        exact ⟨RealIntervalPartition.cons hac hcb hfirst P⟩

/--
Finite low-mass partition theorem for real intervals.  The `α / 2` singleton
bound is the endpoint-jump guard used by the moving-cut proof.
-/
theorem exists_realIntervalPartition_of_singleton_le_half
    (μ : Measure ℝ) [IsFiniteMeasure μ] {α a b : ℝ}
    (hα : 0 < α)
    (hsingleton : ∀ x : ℝ, μ.real ({x} : Set ℝ) ≤ α / 2) :
    Nonempty (RealIntervalPartition μ α a b) := by
  have hhalf_pos : 0 < α / 2 := by linarith
  obtain ⟨k, hk⟩ :=
    exists_nat_ge (intervalOCMass μ a b / (α / 2))
  have hmass :
      intervalOCMass μ a b ≤ (k : ℝ) * (α / 2) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hk (le_of_lt hhalf_pos)
    have hdiv :
        intervalOCMass μ a b / (α / 2) * (α / 2) =
          intervalOCMass μ a b := by
      field_simp [ne_of_gt hhalf_pos]
    nlinarith
  exact exists_realIntervalPartition_aux μ hα hsingleton k a b hmass

end

end Probability
end AppliedModelingLib
