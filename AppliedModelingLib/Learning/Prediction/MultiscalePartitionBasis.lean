import AppliedModelingLib.Learning.Prediction.Approximation
import AppliedModelingLib.Foundations.Math.LinearCompressedSensing

/-!
# Incoherent multiscale partition coordinates

A finite incoherent row system gives a small common coordinate family that
approximates the indicators of the cells of any partition.  Repeating these
coordinates on dyadic blocks is the codeword/interval step in multiscale
approximate-basis constructions for one-dimensional convex functions.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators
open AppliedModelingLib.Math.LinearCompressedSensing

/-- The indicator of one cell of a partition represented by `cellOf`. -/
def partitionCellIndicator
    {Point Cell : Type*} [DecidableEq Cell]
    (cellOf : Point → Cell) (cell : Cell) : Point → ℝ :=
  fun point => if cellOf point = cell then 1 else 0

/-- A coordinate of a finite row system, pulled back along a partition map. -/
def incoherentPartitionCoordinate
    {Point Cell : Type*} {dimension : ℕ}
    (rows : Cell → Fin dimension → ℝ) (cellOf : Point → Cell)
    (coordinate : Fin dimension) : Point → ℝ :=
  fun point => rows (cellOf point) coordinate

/-- The index of the equal-size block containing a point of a finite grid.
The grid has exactly `cellCount * blockSize` points, so the blocks form a
genuine partition with no unassigned endpoint. -/
def uniformBlockCell (cellCount blockSize : ℕ) (hblockSize : 0 < blockSize) :
    Fin (cellCount * blockSize) → Fin cellCount := fun point ↦
  ⟨point.1 / blockSize,
    (Nat.div_lt_iff_lt_mul hblockSize).mpr point.2⟩

/-- The indicator of one equal-size finite-grid block. -/
def uniformBlockIndicator (cellCount blockSize : ℕ) (hblockSize : 0 < blockSize)
    (cell : Fin cellCount) : Fin (cellCount * blockSize) → ℝ :=
  partitionCellIndicator (uniformBlockCell cellCount blockSize hblockSize) cell

/-- Every coordinate of a unit-diagonal incoherent row system has absolute
value at most one.  This is the bounded-coordinate fact needed to use such a
row system as a source-paper approximate basis. -/
theorem muIncoherentLE_abs_entry_le_one
    {Cell : Type*} [Fintype Cell] {dimension : ℕ}
    (rows : Cell → Fin dimension → ℝ) (error : ℝ)
    (hincoherent : MuIncoherentLE rows error) :
    ∀ cell coordinate, |rows cell coordinate| ≤ 1 := by
  intro cell coordinate
  have hterm : rows cell coordinate * rows cell coordinate ≤
      ∑ other, rows cell other * rows cell other := by
    exact Finset.single_le_sum (fun other _ => mul_self_nonneg (rows cell other))
      (Finset.mem_univ coordinate)
  have hself : ∑ other, rows cell other * rows cell other = 1 :=
    hincoherent.self_inner cell
  have hsq : rows cell coordinate ^ 2 ≤ 1 := by
    rw [pow_two]
    exact hterm.trans_eq hself
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (rows cell coordinate + 1)],
    by nlinarith [sq_nonneg (rows cell coordinate - 1)]⟩

/--
An incoherent finite row system approximates every cell indicator after its
coordinates are pulled back along a partition.  The coefficient vector for
cell `i` is precisely row `i`; the diagonal inner product is one and every
off-diagonal inner product has magnitude at most `error`.

The individual coefficient bound follows from the unit diagonal of the
incoherent row system, so no separate bounded-coordinate certificate is
needed.
-/
theorem incoherentPartition_isFixedFiniteApproximateBasis
    {Point Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {dimension : ℕ} (rows : Cell → Fin dimension → ℝ) (cellOf : Point → Cell)
    (error : ℝ) (herror : 0 ≤ error)
    (hincoherent : MuIncoherentLE rows error) :
    IsFixedFiniteApproximateBasis
      (Set.range (partitionCellIndicator cellOf))
      (incoherentPartitionCoordinate rows cellOf) error (dimension : ℝ) := by
  have hcoordinate := muIncoherentLE_abs_entry_le_one rows error hincoherent
  intro target htarget
  rcases htarget with ⟨cell, rfl⟩
  refine ⟨rows cell, ?_, ?_, ?_⟩
  · exact hcoordinate cell
  · calc
      (∑ coordinate, |rows cell coordinate|) ≤ ∑ _coordinate : Fin dimension, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact hcoordinate cell coordinate
      _ = (dimension : ℝ) := by simp
  · intro point
    change |(if cellOf point = cell then 1 else 0) -
      inner (rows cell) (rows (cellOf point))| ≤ error
    by_cases hcell : cellOf point = cell
    · subst hcell
      rw [hincoherent.self_inner]
      simp [herror]
    · rw [if_neg hcell]
      simpa using hincoherent.offdiag_abs_le (by
        intro h
        exact hcell h.symm)

/-- Source-faithful approximate-dimension form of the incoherent partition
construction.  The basis coordinates are bounded by one and coefficients are
unrestricted, exactly as in the usual definition of a uniform approximate
basis.  The stronger controlled theorem above remains available when a later
online-learning reduction needs an explicit coefficient-mass budget. -/
theorem incoherentPartition_isFixedFiniteUniformApproximateBasis
    {Point Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {dimension : ℕ} (rows : Cell → Fin dimension → ℝ) (cellOf : Point → Cell)
    (error : ℝ) (herror : 0 ≤ error)
    (hincoherent : MuIncoherentLE rows error) :
    IsFixedFiniteUniformApproximateBasis
      (Set.range (partitionCellIndicator cellOf))
      (incoherentPartitionCoordinate rows cellOf) error := by
  refine ⟨?_, ?_⟩
  · intro coordinate point
    exact muIncoherentLE_abs_entry_le_one rows error hincoherent (cellOf point) coordinate
  · intro target htarget
    rcases incoherentPartition_isFixedFiniteApproximateBasis rows cellOf error herror hincoherent
      target htarget with ⟨coefficient, _hboundedCoefficient, _hnorm, herror⟩
    exact ⟨coefficient, herror⟩

/-- The codeword construction at one dyadic scale: an incoherent row system
on block labels uniformly approximates every equal-size block indicator on
the finite grid.  Taking `blockSize = 2^h` is the level-`h` component of the
multiscale interval basis. -/
theorem incoherentUniformBlock_isFixedFiniteUniformApproximateBasis
    {cellCount blockSize dimension : ℕ} (hblockSize : 0 < blockSize)
    (rows : Fin cellCount → Fin dimension → ℝ) (error : ℝ) (herror : 0 ≤ error)
    (hincoherent : MuIncoherentLE rows error) :
    IsFixedFiniteUniformApproximateBasis
      (Set.range (uniformBlockIndicator cellCount blockSize hblockSize))
      (incoherentPartitionCoordinate rows
        (uniformBlockCell cellCount blockSize hblockSize)) error := by
  exact incoherentPartition_isFixedFiniteUniformApproximateBasis rows
    (uniformBlockCell cellCount blockSize hblockSize) error herror hincoherent

end AppliedModelingLib.Learning.Prediction
