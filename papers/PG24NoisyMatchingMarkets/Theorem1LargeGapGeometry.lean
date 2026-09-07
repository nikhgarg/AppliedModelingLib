import PG24NoisyMatchingMarkets.Theorem1TailMassHelpers
import Mathlib.Tactic

/-!
# PG24 Theorem 1 large-gap cutoff geometry

The Case 2 argument in `source_tex/proof-attenuating.tex:73-86,251-265`
uses a pigeonhole step: when every sufficiently early cutoff window is too
sparse, repeated rank windows force a large gap between the first cutoff and
an early ranked cutoff.  This file formalizes that finite rank calculation
with integer ranks.  It deliberately leaves the conversion from the source's
real-valued powers `C^phi2` and `C^phi3` to integer window and prefix sizes
to its caller, so no rounding convention is hidden in the statement.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The `stride + 1` consecutive ranked cutoffs beginning at `start` fit in a
closed window of width `width`.  Under sorted cutoffs this is precisely the
rank-level form of a dense cutoff window; it does not choose a convention for
rounding the source's real-valued cutoff counts.
-/
def theorem1TailDenseRankWindow
    (cutoff : ℕ → ℝ) (start stride : ℕ) (width : ℝ) : Prop :=
  ∀ j : ℕ, start ≤ j → j ≤ start + stride →
    cutoff start ≤ cutoff j ∧ cutoff j ≤ cutoff start + width

/--
For a nondecreasing cutoff sequence, a rank window is dense exactly when its
last cutoff lies within the window anchored at its first cutoff.
-/
theorem theorem1Tail_dense_rank_window_iff_endpoint_le
    (cutoff : ℕ → ℝ) (start stride : ℕ) (width : ℝ)
    (hmono : Monotone cutoff) :
    theorem1TailDenseRankWindow cutoff start stride width ↔
      cutoff (start + stride) ≤ cutoff start + width := by
  constructor
  · intro hdense
    exact (hdense (start + stride) (by omega) le_rfl).2
  · intro hend j hstart hj
    exact ⟨hmono hstart, (hmono hj).trans hend⟩

/--
The negated dense-window condition is the strict rank separation used by the
large-gap branch.
-/
theorem theorem1Tail_not_dense_rank_window_iff
    (cutoff : ℕ → ℝ) (start stride : ℕ) (width : ℝ)
    (hmono : Monotone cutoff) :
    ¬ theorem1TailDenseRankWindow cutoff start stride width ↔
      cutoff start + width < cutoff (start + stride) := by
  rw [theorem1Tail_dense_rank_window_iff_endpoint_le cutoff start stride width hmono]
  exact not_le

/--
Accumulating strict separation of consecutive cutoff rank blocks.  This is
the finite telescoping core of the Case 2 pigeonhole argument.  The caller
provides exactly the rank-window separation it has established; no cutoff
ordering, density, or market-clearing property is assumed here.
-/
theorem theorem1Tail_rank_stride_gap_accumulates
    (cutoff : ℕ → ℝ) (stride blocks : ℕ) (width : ℝ)
    (hblocks_pos : 0 < blocks)
    (hstep : ∀ r : ℕ, r < blocks →
      cutoff (r * stride) + width < cutoff ((r + 1) * stride)) :
    cutoff 0 + (blocks : ℝ) * width < cutoff (blocks * stride) := by
  induction blocks with
  | zero => omega
  | succ blocks ih =>
      by_cases hblocks_zero : blocks = 0
      · subst blocks
        have hfirst := hstep 0 (by omega)
        norm_num at hfirst ⊢
        exact hfirst
      · have hblocks_pos' : 0 < blocks := Nat.pos_of_ne_zero hblocks_zero
        have hprefix :
            cutoff 0 + (blocks : ℝ) * width < cutoff (blocks * stride) :=
          ih hblocks_pos' (by
            intro r hr
            exact hstep r (lt_trans hr (Nat.lt_succ_self blocks)))
        have hlast := hstep blocks (Nat.lt_succ_self blocks)
        have hcombined :
            cutoff 0 + ((blocks : ℝ) + 1) * width <
              cutoff ((blocks + 1) * stride) := by
          linarith
        simpa [Nat.cast_succ, Nat.succ_eq_add_one] using hcombined

/--
If every rank window of `stride + 1` cutoffs within the first `blocks` blocks
has width strictly greater than `width`, the first and last block endpoints
are separated by more than `blocks * width`.

For the source proof, this is the exact integer-rank form of ``no dense
window before `P*`'' needed before applying the claimed pigeonhole argument
at `proof-attenuating.tex:261-265`.
-/
theorem theorem1Tail_rank_stride_gap_of_no_dense_rank_window
    (cutoff : ℕ → ℝ) (stride blocks : ℕ) (width : ℝ)
    (hblocks_pos : 0 < blocks)
    (hseparated : ∀ i : ℕ, i + stride ≤ blocks * stride →
      cutoff i + width < cutoff (i + stride)) :
    cutoff 0 + (blocks : ℝ) * width < cutoff (blocks * stride) := by
  apply theorem1Tail_rank_stride_gap_accumulates
    cutoff stride blocks width hblocks_pos
  intro r hr
  have hrsucc : r + 1 ≤ blocks := Nat.succ_le_iff.mpr hr
  have hindex : r * stride + stride ≤ blocks * stride := by
    calc
      r * stride + stride = (r + 1) * stride := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_mul r stride).symm
      _ ≤ blocks * stride := Nat.mul_le_mul_right stride hrsucc
  simpa [Nat.succ_mul] using hseparated (r * stride) hindex

/--
The Case 2 finite pigeonhole conclusion in direct dense-window form.  If no
`stride + 1` consecutive ranks in the relevant early prefix fit in a closed
window of width `width`, the cutoff range across `blocks` such rank blocks is
strictly larger than `blocks * width`.

This corresponds to the geometry invoked at
`source_tex/proof-attenuating.tex:73-86,261-265`; mapping its real powers to
the integer `stride` and `blocks` remains an explicit source-proof obligation.
-/
theorem theorem1Tail_rank_stride_gap_of_no_dense_rank_windows
    (cutoff : ℕ → ℝ) (stride blocks : ℕ) (width : ℝ)
    (hblocks_pos : 0 < blocks)
    (hmono : Monotone cutoff)
    (hno_dense : ∀ i : ℕ, i + stride ≤ blocks * stride →
      ¬ theorem1TailDenseRankWindow cutoff i stride width) :
    cutoff 0 + (blocks : ℝ) * width < cutoff (blocks * stride) := by
  apply theorem1Tail_rank_stride_gap_of_no_dense_rank_window
    cutoff stride blocks width hblocks_pos
  intro i hi
  exact (theorem1Tail_not_dense_rank_window_iff cutoff i stride width hmono).mp
    (hno_dense i hi)

/--
Monotonicity extends the finite block-endpoint gap to any later ranked cutoff.
This is the form used when the source's early prefix contains at least the
integer number of separated rank blocks.
-/
theorem theorem1Tail_rank_stride_gap_to_later_rank
    (cutoff : ℕ → ℝ) (stride blocks terminal : ℕ) (width : ℝ)
    (hblocks_pos : 0 < blocks)
    (hseparated : ∀ i : ℕ, i + stride ≤ blocks * stride →
      cutoff i + width < cutoff (i + stride))
    (hmono : Monotone cutoff)
    (hterminal : blocks * stride ≤ terminal) :
    cutoff 0 + (blocks : ℝ) * width < cutoff terminal := by
  calc
    cutoff 0 + (blocks : ℝ) * width < cutoff (blocks * stride) :=
      theorem1Tail_rank_stride_gap_of_no_dense_rank_window
        cutoff stride blocks width hblocks_pos hseparated
    _ ≤ cutoff terminal := hmono hterminal

end

end PG24NoisyMatchingMarkets
