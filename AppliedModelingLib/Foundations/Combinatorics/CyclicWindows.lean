import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Finite cyclic windows

A cyclic window is a translate of the first `width` residues in a finite
cycle.  The two facts below are the exact balanced-design properties needed
when a randomized mechanism must expose a block of coordinates while giving
every individual coordinate the same exposure probability.
-/

namespace AppliedModelingLib
namespace Combinatorics

open scoped BigOperators ENNReal

noncomputable section

/-- The `width` consecutive residues beginning at `start`, represented as a
finite subset of the cyclic group `ZMod modulus`. -/
def cyclicWindow (modulus width : ℕ) [NeZero modulus]
    (start : ZMod modulus) : Finset (ZMod modulus) :=
  Finset.univ.image fun offset : Fin width => start + (offset.val : ZMod modulus)

/-- A cyclic window has its declared cardinality as long as it does not wrap
more than once around the cycle. -/
theorem cyclicWindow_card (modulus width : ℕ) [NeZero modulus]
    (hwidth : width ≤ modulus) (start : ZMod modulus) :
    (cyclicWindow modulus width start).card = width := by
  let translate : Fin width → ZMod modulus :=
    fun offset => start + (offset.val : ZMod modulus)
  have hinjective : Function.Injective translate := by
    intro first second heq
    have hcast : (first.val : ZMod modulus) = (second.val : ZMod modulus) := by
      exact add_left_cancel (a := start) (by simpa [translate] using heq)
    have hval : first.val = second.val := by
      have := congrArg ZMod.val hcast
      simpa [ZMod.val_natCast_of_lt (first.isLt.trans_le hwidth),
        ZMod.val_natCast_of_lt (second.isLt.trans_le hwidth)] using this
    exact Fin.ext hval
  unfold cyclicWindow
  change (Finset.univ.image translate).card = width
  rw [Finset.card_image_of_injective _ hinjective]
  simp

/-- For a fixed coordinate, exactly `width` cyclic starting points contain
it.  Equivalently, the uniform random cyclic window contains each coordinate
with probability `width / modulus`. -/
theorem cyclicWindow_cover_card (modulus width : ℕ) [NeZero modulus]
    (hwidth : width ≤ modulus) (point : ZMod modulus) :
    Fintype.card {start : ZMod modulus | point ∈ cyclicWindow modulus width start} = width := by
  let coverStart : Fin width → {start : ZMod modulus |
      point ∈ cyclicWindow modulus width start} := fun offset =>
    ⟨point - (offset.val : ZMod modulus), by
      change point ∈ Finset.univ.image (fun other : Fin width =>
        point - (offset.val : ZMod modulus) + (other.val : ZMod modulus))
      apply Finset.mem_image.mpr
      refine ⟨offset, Finset.mem_univ _, ?_⟩
      dsimp
      abel⟩
  have hinjective : Function.Injective coverStart := by
    intro first second heq
    have hcast : (first.val : ZMod modulus) = (second.val : ZMod modulus) := by
      have hvalue := congrArg Subtype.val heq
      dsimp [coverStart] at hvalue
      have hneg : -(first.val : ZMod modulus) = -(second.val : ZMod modulus) := by
        calc
          -(first.val : ZMod modulus) =
              (point - (first.val : ZMod modulus)) - point := by abel
          _ = (point - (second.val : ZMod modulus)) - point := by rw [hvalue]
          _ = -(second.val : ZMod modulus) := by abel
      exact neg_injective hneg
    have hval : first.val = second.val := by
      have := congrArg ZMod.val hcast
      simpa [ZMod.val_natCast_of_lt (first.isLt.trans_le hwidth),
        ZMod.val_natCast_of_lt (second.isLt.trans_le hwidth)] using this
    exact Fin.ext hval
  have hsurjective : Function.Surjective coverStart := by
    intro start
    have hmem := start.property
    change point ∈ Finset.univ.image (fun offset : Fin width =>
      start.val + (offset.val : ZMod modulus)) at hmem
    rcases Finset.mem_image.mp hmem with ⟨offset, _, hpoint⟩
    refine ⟨offset, ?_⟩
    apply Subtype.ext
    dsimp [coverStart]
    exact sub_eq_iff_eq_add.mpr hpoint.symm
  simpa using Fintype.card_congr (Equiv.ofBijective coverStart ⟨hinjective, hsurjective⟩).symm

/-- Under the uniform choice of a cyclic starting point, every coordinate is
included with probability exactly `width / modulus`. -/
theorem pmfProb_uniform_cyclicWindow_contains (modulus width : ℕ) [NeZero modulus]
    (hwidth : width ≤ modulus) (point : ZMod modulus) :
    AppliedModelingLib.pmfProb (PMF.uniformOfFintype (ZMod modulus))
      (fun start => point ∈ cyclicWindow modulus width start) =
      (width : ℝ) / modulus := by
  classical
  let event : ZMod modulus → Prop := fun start => point ∈ cyclicWindow modulus width start
  have hcard : (Finset.univ.filter event).card = width := by
    rw [← Fintype.card_subtype event]
    exact cyclicWindow_cover_card modulus width hwidth point
  unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp
  simp_rw [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum]
  change (((Fintype.card (ZMod modulus) : ℝ≥0∞)⁻¹).toReal) *
      (∑ start : ZMod modulus, if event start then (1 : ℝ) else 0) =
    (width : ℝ) / modulus
  have hsum : (∑ start : ZMod modulus, if event start then (1 : ℝ) else 0) =
      (Finset.univ.filter event).card := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum, hcard]
  simp [ZMod.card, div_eq_mul_inv]
  ring

end

end Combinatorics
end AppliedModelingLib
