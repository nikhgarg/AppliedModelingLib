import PG24NoisyMatchingMarkets.Theorem3DenseGapExponents
import Mathlib.Tactic

/-!
# PG24 Theorem 3 rounded cutoff ranks

The dense-cluster / large-gap argument uses real powers of the coalition size
as cardinality and rank thresholds.  These definitions and lemmas make the
integer choices explicit: a dense-window threshold is rounded up, while the
last rank at or below a real prefix threshold is rounded down.

They are finite-index arithmetic only.  They do not assume any cutoff,
capacity, probability, or endpoint claim from the paper.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- Integer threshold for a cutoff window required to contain `C ^ exponent` cutoffs. -/
def theorem3DenseWindowCount (C : ℕ) (exponent : ℝ) : ℕ :=
  ⌈Real.rpow (C : ℝ) exponent⌉₊

/-- Integer rank at or below a real-valued early-prefix threshold. -/
def theorem3EarlyPrefixRank (C : ℕ) (exponent : ℝ) : ℕ :=
  ⌊Real.rpow (C : ℝ) exponent⌋₊

/-- Number of full dense-window blocks that fit in the rounded early prefix. -/
def theorem3DenseGapBlockCount (C : ℕ) (denseExponent prefixExponent : ℝ) : ℕ :=
  theorem3EarlyPrefixRank C prefixExponent /
    theorem3DenseWindowCount C denseExponent

/-- A positive coalition size gives a nonzero rounded dense-window count. -/
theorem theorem3DenseWindowCount_pos {C : ℕ} {exponent : ℝ}
    (hC_pos : 0 < C) :
    0 < theorem3DenseWindowCount C exponent := by
  rw [show theorem3DenseWindowCount C exponent =
    ⌈Real.rpow (C : ℝ) exponent⌉₊ from rfl, Nat.ceil_pos]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hC_pos) _

/--
When the source exponent is at most one, its ceiling is still a valid index
of a coalition of size `C`.  This prevents a hidden out-of-range use of
`P_(C^phi)`.
-/
theorem theorem3DenseWindowCount_le_coalitionSize {C : ℕ} {exponent : ℝ}
    (hC_one : 1 ≤ C) (hexponent_le_one : exponent ≤ 1) :
    theorem3DenseWindowCount C exponent ≤ C := by
  rw [show theorem3DenseWindowCount C exponent =
    ⌈Real.rpow (C : ℝ) exponent⌉₊ from rfl, Nat.ceil_le]
  calc
    Real.rpow (C : ℝ) exponent ≤ Real.rpow (C : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hC_one)
        hexponent_le_one
    _ = (C : ℝ) := Real.rpow_one _

/--
For a strict sublinear source exponent, the rounded floor is a strict valid
rank of a coalition of size `C`.  This is the indexing side of the source's
informal `P_(C^phi)` notation.
-/
theorem theorem3EarlyPrefixRank_lt_coalitionSize {C : ℕ} {exponent : ℝ}
    (hC_one_lt : 1 < C) (hexponent_lt_one : exponent < 1) :
    theorem3EarlyPrefixRank C exponent < C := by
  unfold theorem3EarlyPrefixRank
  apply (Nat.floor_lt (a := Real.rpow (C : ℝ) exponent) (n := C)
    (Real.rpow_nonneg (Nat.cast_nonneg C) _)).2
  calc
    Real.rpow (C : ℝ) exponent < Real.rpow (C : ℝ) 1 :=
      Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hC_one_lt)
        hexponent_lt_one
    _ = (C : ℝ) := Real.rpow_one _

/--
An integer cardinality is at least the source's real dense-window threshold
exactly when it is at least the explicit ceiling.  Thus the ceiling is a
faithful, rather than strengthened, replacement for ``at least `C^phi`''.
-/
theorem theorem3_denseWindow_card_ge_iff
    {C : ℕ} {exponent : ℝ} {ι : Type*} (window : Finset ι) :
    Real.rpow (C : ℝ) exponent ≤ (window.card : ℝ) ↔
      theorem3DenseWindowCount C exponent ≤ window.card := by
  rw [show theorem3DenseWindowCount C exponent =
    ⌈Real.rpow (C : ℝ) exponent⌉₊ from rfl, Nat.ceil_le]

/--
An integer cardinality is strictly below the source's real prefix threshold
exactly when it is strictly below the explicit ceiling.
-/
theorem theorem3_card_lt_realThreshold_iff_card_lt_denseWindowCount
    {C : ℕ} {exponent : ℝ} {ι : Type*} (window : Finset ι) :
    (window.card : ℝ) < Real.rpow (C : ℝ) exponent ↔
      window.card < theorem3DenseWindowCount C exponent := by
  rw [show theorem3DenseWindowCount C exponent =
    ⌈Real.rpow (C : ℝ) exponent⌉₊ from rfl, Nat.lt_ceil]

/--
The strict sparse-prefix case has a usable weak natural-number bound by the
floor of the same source threshold.  This is the form needed for capacity
bookkeeping without replacing a strict source inequality by a stronger one.
-/
theorem theorem3_card_le_earlyPrefixRank_of_lt
    {C : ℕ} {exponent : ℝ} {ι : Type*} (window : Finset ι)
    (hwindow : (window.card : ℝ) < Real.rpow (C : ℝ) exponent) :
    window.card ≤ theorem3EarlyPrefixRank C exponent := by
  rw [show theorem3EarlyPrefixRank C exponent =
    ⌊Real.rpow (C : ℝ) exponent⌋₊ from rfl]
  apply Nat.le_floor
  exact hwindow.le

/-- The rounded block count fills no more than the rounded early prefix. -/
theorem theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank
    (C : ℕ) (denseExponent prefixExponent : ℝ) :
    theorem3DenseGapBlockCount C denseExponent prefixExponent *
        theorem3DenseWindowCount C denseExponent ≤
      theorem3EarlyPrefixRank C prefixExponent := by
  unfold theorem3DenseGapBlockCount
  exact Nat.div_mul_le_self _ _

/--
If one rounded dense window fits into the rounded early prefix, the block
count is positive, so the finite telescoping large-gap lemma has a legitimate
nonempty number of blocks.
-/
theorem theorem3DenseGapBlockCount_pos_of_denseWindowCount_le_earlyPrefixRank
    {C : ℕ} {denseExponent prefixExponent : ℝ}
    (hC_pos : 0 < C)
    (hfit : theorem3DenseWindowCount C denseExponent ≤
      theorem3EarlyPrefixRank C prefixExponent) :
    0 < theorem3DenseGapBlockCount C denseExponent prefixExponent := by
  unfold theorem3DenseGapBlockCount
  exact Nat.div_pos hfit
    (theorem3DenseWindowCount_pos (C := C) (exponent := denseExponent) hC_pos)

end

end PG24NoisyMatchingMarkets
