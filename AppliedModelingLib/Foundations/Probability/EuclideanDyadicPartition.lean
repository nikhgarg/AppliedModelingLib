import AppliedModelingLib.Foundations.Probability.MetricPartitionTransport
import Mathlib.MeasureTheory.Function.Floor

/-!
# Euclidean dyadic partitions

This module implements the nested half-open dyadic cubes of
Fournier--Guillin (2015), Notation 4, on `(-1, 1]^d`.  Level `l` has
`2^(d*l)` cubes.  Each cube is represented by its coordinate indices,
assigned using a ceiling convention that puts a grid boundary in the cell on
its left.  Cell centers are anchors.

The construction instantiates `FiniteQuantizationHierarchy` with terminal
radius `sqrt d / 2^l` and parent-anchor step radius
`sqrt d / 2^(l+1)`.  These are deterministic geometric facts; this module
contains no concentration assertion.

Source: Nicolas Fournier and Arnaud Guillin, *On the rate of convergence in
Wasserstein distance of the empirical measure*, Probability Theory and
Related Fields 162 (2015), Notation 4 and Lemma 5:
<https://perso.lpsm.paris/~nfournier/a58.pdf>.

## Library provenance

A search of the pinned Mathlib checkout and official online Mathlib
documentation found no dyadic-cube partition hierarchy to reuse.  This local
construction uses, without copying source:

* `Nat.ceil_le`, `Nat.lt_ceil`, `Nat.ceil_pos`, and
  `Nat.ceil_lt_add_one` from
  [`Algebra/Order/Floor/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Defs.lean)
  and
  [`Algebra/Order/Floor/Semiring.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Semiring.lean);
* `Nat.measurable_ceil` from
  [`MeasureTheory/Function/Floor.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/Floor.lean);
* `EuclideanSpace.dist_eq` from
  [`Analysis/InnerProductSpace/PiL2.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/InnerProductSpace/PiL2.lean);
* `Real.sqrt_mul` and `Real.sqrt_sq_eq_abs` from
  [`Data/Real/Sqrt.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Real/Sqrt.lean).
* `MeasurableSet.standardBorel` from
  [`MeasureTheory/Constructions/Polish/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean),
  used to expose the measurable half-open cube as a standard Borel space.

All links pin this repository's Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, licensed Apache-2.0.  No
Mathlib source is copied or modified.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The source compact interval `(-1, 1]`. -/
def halfOpenUnitInterval : Set ℝ := Set.Ioc (-1) 1

/-- The half-open Euclidean cube `(-1, 1]^dimension`. -/
abbrev HalfOpenUnitCube (dimension : ℕ) :=
  {x : EuclideanSpace ℝ (Fin dimension) // ∀ i, x i ∈ halfOpenUnitInterval}

/-- The source half-open cube is a measurable subset of Euclidean space. -/
theorem measurableSet_halfOpenUnitCube (dimension : ℕ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin dimension) |
      ∀ i, x i ∈ halfOpenUnitInterval} := by
  rw [show {x : EuclideanSpace ℝ (Fin dimension) | ∀ i, x i ∈ halfOpenUnitInterval} =
      ⋂ i : Fin dimension, {x | x i ∈ halfOpenUnitInterval} by
    ext x
    simp]
  apply MeasurableSet.iInter
  intro coordinate
  exact measurableSet_Ioc.preimage (by fun_prop)

noncomputable instance (dimension : ℕ) : StandardBorelSpace (HalfOpenUnitCube dimension) :=
  (measurableSet_halfOpenUnitCube dimension).standardBorel

/-- One of the `2^level` coordinate intervals at a dyadic level. -/
abbrev dyadicCellIndex (level : ℕ) := Fin (2 ^ level)

/-- A product index for one dyadic cube in the given dimension and level. -/
abbrev dyadicCubeIndex (dimension level : ℕ) :=
  Fin dimension → dyadicCellIndex level

def normalizedUnitCoordinate (x : ℝ) : ℝ := (x + 1) / 2

theorem measurable_normalizedUnitCoordinate : Measurable normalizedUnitCoordinate := by
  unfold normalizedUnitCoordinate
  fun_prop

theorem normalizedUnitCoordinate_pos {x : ℝ} (hx : x ∈ halfOpenUnitInterval) :
    0 < normalizedUnitCoordinate x := by
  rcases hx with ⟨hx, _⟩
  unfold normalizedUnitCoordinate
  linarith

theorem normalizedUnitCoordinate_le_one {x : ℝ} (hx : x ∈ halfOpenUnitInterval) :
    normalizedUnitCoordinate x ≤ 1 := by
  rcases hx with ⟨_, hx⟩
  unfold normalizedUnitCoordinate
  linarith

def dyadicCoordinateNumber (level : ℕ) (x : ℝ) : ℕ :=
  Nat.ceil (((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x) - 1

theorem dyadicCoordinateNumber_lt (level : ℕ) (x : ℝ)
    (hx : x ∈ halfOpenUnitInterval) : dyadicCoordinateNumber level x < 2 ^ level := by
  let scale : ℕ := 2 ^ level
  let position : ℝ := (scale : ℝ) * normalizedUnitCoordinate x
  have hscale_pos : 0 < scale := by positivity
  have hposition_pos : 0 < position :=
    mul_pos (by exact_mod_cast hscale_pos) (normalizedUnitCoordinate_pos hx)
  have hposition_le : position ≤ (scale : ℝ) := by
    calc
      position ≤ (scale : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (normalizedUnitCoordinate_le_one hx)
          (by exact_mod_cast hscale_pos.le)
      _ = scale := by ring
  have hceil_pos : 0 < Nat.ceil position := Nat.ceil_pos.mpr hposition_pos
  have hceil_le : Nat.ceil position ≤ scale := Nat.ceil_le.mpr hposition_le
  change Nat.ceil position - 1 < scale
  omega

/--
The unique half-open dyadic cell containing a coordinate.  The formula
`ceil (2^level * (x + 1) / 2) - 1` assigns a grid boundary to the interval on
its left, matching the source's `Ioc` convention.
-/
def dyadicCoordinateIndex (level : ℕ) (x : ℝ) (hx : x ∈ halfOpenUnitInterval) :
    dyadicCellIndex level :=
  ⟨dyadicCoordinateNumber level x, dyadicCoordinateNumber_lt level x hx⟩

theorem dyadicCoordinateIndex_val_add_one
    (level : ℕ) (x : ℝ) (hx : x ∈ halfOpenUnitInterval) :
    (dyadicCoordinateIndex level x hx).val + 1 =
      Nat.ceil ((2 ^ level : ℕ) * normalizedUnitCoordinate x) := by
  unfold dyadicCoordinateIndex
  change dyadicCoordinateNumber level x + 1 = _
  unfold dyadicCoordinateNumber
  have hpos : 0 < Nat.ceil
      ((2 ^ level : ℕ) * normalizedUnitCoordinate x) := by
    apply Nat.ceil_pos.mpr
    exact mul_pos (by positivity) (normalizedUnitCoordinate_pos hx)
  omega

theorem nat_ceil_two_mul_sub_one_div_two {a : ℝ} (ha : 0 < a) :
    (Nat.ceil (2 * a) - 1) / 2 = Nat.ceil a - 1 := by
  let c : ℕ := Nat.ceil a
  let ctwo : ℕ := Nat.ceil (2 * a)
  have hcpos : 0 < c := by
    exact Nat.ceil_pos.mpr ha
  have hctwopos : 0 < ctwo := by
    exact Nat.ceil_pos.mpr (by positivity)
  have hc_lt : (c : ℝ) < a + 1 := Nat.ceil_lt_add_one ha.le
  have hlower_real : ((2 * (c - 1) : ℕ) : ℝ) < 2 * a := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]
    linarith
  have hlower : 2 * (c - 1) < ctwo := by
    exact Nat.lt_ceil.mpr hlower_real
  have hupper : ctwo ≤ 2 * c := by
    apply Nat.ceil_le.mpr
    have hceil := Nat.le_ceil a
    norm_num [Nat.cast_mul]
    linarith
  dsimp [c, ctwo] at *
  omega

/-- Forget the final binary refinement by integer division by two. -/
def dyadicParentCoordinate (level : ℕ) :
    dyadicCellIndex (level + 1) → dyadicCellIndex level := fun index ↦
  ⟨index.val / 2, by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr
    simpa [pow_succ, Nat.mul_comm] using index.isLt⟩

theorem dyadicParentCoordinate_coordinateIndex
    (level : ℕ) (x : ℝ) (hx : x ∈ halfOpenUnitInterval) :
    dyadicParentCoordinate level (dyadicCoordinateIndex (level + 1) x hx) =
      dyadicCoordinateIndex level x hx := by
  apply Fin.ext
  change (dyadicCoordinateIndex (level + 1) x hx).val / 2 =
    (dyadicCoordinateIndex level x hx).val
  have hchild := dyadicCoordinateIndex_val_add_one (level + 1) x hx
  have hparent := dyadicCoordinateIndex_val_add_one level x hx
  have hscale :
      ((2 ^ (level + 1) : ℕ) : ℝ) * normalizedUnitCoordinate x =
        2 * (((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x) := by
    norm_num [pow_succ]
    ring
  have hpos : 0 < ((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x :=
    mul_pos (by positivity) (normalizedUnitCoordinate_pos hx)
  have hceil := nat_ceil_two_mul_sub_one_div_two hpos
  rw [hscale] at hchild
  have hchild_val :
      (dyadicCoordinateIndex (level + 1) x hx).val =
        Nat.ceil (2 * (((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x)) - 1 := by
    omega
  have hparent_val :
      (dyadicCoordinateIndex level x hx).val =
        Nat.ceil (((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x) - 1 := by
    omega
  rw [hchild_val, hparent_val]
  exact hceil

/-- Assign all coordinates of a cube point to their dyadic cells. -/
def dyadicCubeLocate (dimension level : ℕ) (x : HalfOpenUnitCube dimension) :
    dyadicCubeIndex dimension level := fun coordinate ↦
  dyadicCoordinateIndex level (x.1 coordinate) (x.2 coordinate)

def dyadicCubeParent (dimension level : ℕ) :
    dyadicCubeIndex dimension (level + 1) → dyadicCubeIndex dimension level :=
  fun index coordinate ↦ dyadicParentCoordinate level (index coordinate)

def dyadicCubeRoot (dimension : ℕ) : dyadicCubeIndex dimension 0 :=
  fun _ ↦ ⟨0, by norm_num⟩

theorem dyadicCubeLocate_zero (dimension : ℕ) (x : HalfOpenUnitCube dimension) :
    dyadicCubeLocate dimension 0 x = dyadicCubeRoot dimension := by
  funext coordinate
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

theorem dyadicCubeParent_locate (dimension level : ℕ)
    (x : HalfOpenUnitCube dimension) :
    dyadicCubeParent dimension level (dyadicCubeLocate dimension (level + 1) x) =
      dyadicCubeLocate dimension level x := by
  funext coordinate
  exact dyadicParentCoordinate_coordinateIndex level (x.1 coordinate) (x.2 coordinate)

theorem measurable_dyadicCoordinateNumber (dimension level : ℕ)
    (coordinate : Fin dimension) : Measurable (fun x : HalfOpenUnitCube dimension ↦
      dyadicCoordinateNumber level (x.1 coordinate)) := by
  unfold dyadicCoordinateNumber
  apply Measurable.sub_const
  apply Nat.measurable_ceil.comp
  have hcoordinate : Measurable (fun x : HalfOpenUnitCube dimension ↦ x.1 coordinate) := by
    fun_prop
  exact measurable_const.mul (measurable_normalizedUnitCoordinate.comp hcoordinate)

/-- Every fiber of the dyadic locator is measurable. -/
theorem measurableSet_dyadicCubeCell (dimension level : ℕ)
    (index : dyadicCubeIndex dimension level) :
    MeasurableSet {x | dyadicCubeLocate dimension level x = index} := by
  have hcoordinate : ∀ coordinate : Fin dimension, MeasurableSet
      {x : HalfOpenUnitCube dimension |
        dyadicCoordinateIndex level (x.1 coordinate) (x.2 coordinate) =
          index coordinate} := by
    intro coordinate
    have hraw : MeasurableSet {x : HalfOpenUnitCube dimension |
        dyadicCoordinateNumber level (x.1 coordinate) = (index coordinate).val} :=
      measurableSet_eq_fun (measurable_dyadicCoordinateNumber dimension level coordinate)
        measurable_const
    convert hraw using 1
    ext x
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h
  rw [show {x | dyadicCubeLocate dimension level x = index} =
      ⋂ coordinate : Fin dimension,
        {x | dyadicCoordinateIndex level (x.1 coordinate) (x.2 coordinate) =
          index coordinate} by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h coordinate
      exact congrFun h coordinate
    · intro h
      funext coordinate
      exact h coordinate]
  exact MeasurableSet.iInter hcoordinate

/-- The midpoint of a one-dimensional dyadic cell. -/
def dyadicCoordinateAnchor (level : ℕ) (index : dyadicCellIndex level) : ℝ :=
  -1 + ((2 * index.val + 1 : ℕ) : ℝ) / (2 ^ level : ℕ)

theorem dyadicCoordinateAnchor_mem (level : ℕ) (index : dyadicCellIndex level) :
    dyadicCoordinateAnchor level index ∈ halfOpenUnitInterval := by
  have hscale_pos_nat : 0 < 2 ^ level := by positivity
  have hscale_pos : 0 < ((2 ^ level : ℕ) : ℝ) := by exact_mod_cast hscale_pos_nat
  have hindex : index.val < 2 ^ level := index.isLt
  constructor
  · unfold dyadicCoordinateAnchor
    have hnum_pos : 0 < ((2 * index.val + 1 : ℕ) : ℝ) := by positivity
    have hdiv_pos : 0 < ((2 * index.val + 1 : ℕ) : ℝ) /
        ((2 ^ level : ℕ) : ℝ) := div_pos hnum_pos hscale_pos
    linarith
  · unfold dyadicCoordinateAnchor
    have hnum : ((2 * index.val + 1 : ℕ) : ℝ) ≤
        2 * ((2 ^ level : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * index.val + 1 ≤ 2 * (2 ^ level) by omega)
    have hdiv : ((2 * index.val + 1 : ℕ) : ℝ) /
        ((2 ^ level : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hscale_pos]
      exact hnum
    linarith

/-- The coordinatewise midpoint anchor of a dyadic cube. -/
def dyadicCubeAnchor (dimension level : ℕ)
    (index : dyadicCubeIndex dimension level) : HalfOpenUnitCube dimension :=
  ⟨WithLp.toLp 2 (fun coordinate ↦ dyadicCoordinateAnchor level (index coordinate)),
    fun coordinate ↦ dyadicCoordinateAnchor_mem level (index coordinate)⟩

theorem dyadicCoordinateIndex_bracket
    (level : ℕ) (x : ℝ) (hx : x ∈ halfOpenUnitInterval) :
    ((dyadicCoordinateIndex level x hx).val : ℝ) <
        ((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x ∧
      ((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x ≤
        ((dyadicCoordinateIndex level x hx).val : ℝ) + 1 := by
  have hval := dyadicCoordinateIndex_val_add_one level x hx
  let position : ℝ := ((2 ^ level : ℕ) : ℝ) * normalizedUnitCoordinate x
  have hpos : 0 < position :=
    mul_pos (by positivity) (normalizedUnitCoordinate_pos hx)
  constructor
  · apply Nat.lt_ceil.mp
    dsimp [position]
    omega
  · have hceil := Nat.le_ceil position
    rw [← hval] at hceil
    exact_mod_cast hceil

theorem abs_sub_dyadicCoordinateAnchor_le
    (level : ℕ) (x : ℝ) (hx : x ∈ halfOpenUnitInterval) :
    |x - dyadicCoordinateAnchor level (dyadicCoordinateIndex level x hx)| ≤
      1 / ((2 ^ level : ℕ) : ℝ) := by
  let scale : ℝ := ((2 ^ level : ℕ) : ℝ)
  let index : ℝ := ((dyadicCoordinateIndex level x hx).val : ℝ)
  have hscale_pos : 0 < scale := by dsimp [scale]; positivity
  have hbracket := dyadicCoordinateIndex_bracket level x hx
  have hxformula : x = 2 * normalizedUnitCoordinate x - 1 := by
    unfold normalizedUnitCoordinate
    ring
  have hanchor : dyadicCoordinateAnchor level (dyadicCoordinateIndex level x hx) =
      -1 + (2 * index + 1) / scale := by
    unfold dyadicCoordinateAnchor
    dsimp [index, scale]
    norm_num [Nat.cast_add, Nat.cast_mul]
  change |x - dyadicCoordinateAnchor level (dyadicCoordinateIndex level x hx)| ≤
    1 / scale
  rw [abs_le]
  constructor
  · rw [hanchor, hxformula]
    have hrewrite :
        2 * normalizedUnitCoordinate x - 1 - (-1 + (2 * index + 1) / scale) =
          2 * normalizedUnitCoordinate x - (2 * index + 1) / scale := by ring
    rw [hrewrite]
    have hleft : -(1 / scale) = (-1) / scale := by ring
    rw [hleft, div_le_iff₀ hscale_pos]
    have hmul :
        (2 * normalizedUnitCoordinate x - (2 * index + 1) / scale) * scale =
          2 * (scale * normalizedUnitCoordinate x) - (2 * index + 1) := by
      field_simp
    rw [hmul]
    dsimp [scale, index] at hbracket ⊢
    linarith [hbracket.1]
  · rw [hanchor, hxformula]
    have hrewrite :
        2 * normalizedUnitCoordinate x - 1 - (-1 + (2 * index + 1) / scale) =
          2 * normalizedUnitCoordinate x - (2 * index + 1) / scale := by ring
    rw [hrewrite, le_div_iff₀ hscale_pos]
    have hmul :
        (2 * normalizedUnitCoordinate x - (2 * index + 1) / scale) * scale =
          2 * (scale * normalizedUnitCoordinate x) - (2 * index + 1) := by
      field_simp
    rw [hmul]
    dsimp [scale, index] at hbracket ⊢
    linarith [hbracket.2]

theorem abs_dyadicCoordinateAnchor_succ_sub_parent_le
    (level : ℕ) (index : dyadicCellIndex (level + 1)) :
    |dyadicCoordinateAnchor (level + 1) index -
        dyadicCoordinateAnchor level (dyadicParentCoordinate level index)| ≤
      1 / ((2 ^ (level + 1) : ℕ) : ℝ) := by
  let child : ℕ := index.val
  let parent : ℕ := index.val / 2
  let denominator : ℝ := ((2 ^ (level + 1) : ℕ) : ℝ)
  have hdenominator_pos : 0 < denominator := by dsimp [denominator]; positivity
  have hmod := Nat.mod_add_div index.val 2
  have hmod_lt : index.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have hparent_lower : 2 * parent ≤ child := by
    dsimp [parent, child]
    omega
  have hparent_upper : child ≤ 2 * parent + 1 := by
    dsimp [parent, child]
    omega
  have hnum_lower : (-1 : ℝ) ≤
      2 * (child : ℝ) + 1 - 2 * (2 * (parent : ℝ) + 1) := by
    have hparent_lower_real : (2 * (parent : ℝ)) ≤ (child : ℝ) := by
      exact_mod_cast hparent_lower
    linarith
  have hnum_upper :
      2 * (child : ℝ) + 1 - 2 * (2 * (parent : ℝ) + 1) ≤ (1 : ℝ) := by
    have hparent_upper_real : (child : ℝ) ≤ 2 * (parent : ℝ) + 1 := by
      exact_mod_cast hparent_upper
    linarith
  have hdifference :
      dyadicCoordinateAnchor (level + 1) index -
          dyadicCoordinateAnchor level (dyadicParentCoordinate level index) =
        (2 * (child : ℝ) + 1 - 2 * (2 * (parent : ℝ) + 1)) /
          denominator := by
    unfold dyadicCoordinateAnchor dyadicParentCoordinate
    dsimp [child, parent, denominator]
    norm_num [pow_succ, Nat.cast_add, Nat.cast_mul]
    field_simp
  rw [hdifference]
  change |(2 * (child : ℝ) + 1 - 2 * (2 * (parent : ℝ) + 1)) /
      denominator| ≤ 1 / denominator
  rw [abs_le]
  constructor
  · have hneg : -(1 / denominator) = (-1) / denominator := by ring
    rw [hneg, div_le_iff₀ hdenominator_pos]
    rw [div_mul_cancel₀ _ hdenominator_pos.ne']
    exact hnum_lower
  · rw [div_le_iff₀ hdenominator_pos]
    rw [div_mul_cancel₀ _ hdenominator_pos.ne']
    exact hnum_upper

/-- Euclidean point-to-center radius `sqrt dimension / 2^level`. -/
def dyadicCubeRadius (dimension level : ℕ) : ℝ :=
  Real.sqrt dimension / ((2 ^ level : ℕ) : ℝ)

theorem dyadicCubeRadius_nonneg (dimension level : ℕ) :
    0 ≤ dyadicCubeRadius dimension level := by
  unfold dyadicCubeRadius
  positivity

theorem dist_dyadicCubeAnchor_le (dimension level : ℕ)
    (x : HalfOpenUnitCube dimension) :
    dist x (dyadicCubeAnchor dimension level (dyadicCubeLocate dimension level x)) ≤
      dyadicCubeRadius dimension level := by
  let radiusCoordinate : ℝ := 1 / ((2 ^ level : ℕ) : ℝ)
  have hradiusCoordinate_nonneg : 0 ≤ radiusCoordinate := by
    dsimp [radiusCoordinate]
    positivity
  have hcoordinate : ∀ coordinate : Fin dimension,
      dist (x.1 coordinate)
          ((dyadicCubeAnchor dimension level (dyadicCubeLocate dimension level x)).1 coordinate) ≤
        radiusCoordinate := by
    intro coordinate
    rw [Real.dist_eq]
    change |x.1 coordinate -
      dyadicCoordinateAnchor level
        (dyadicCoordinateIndex level (x.1 coordinate) (x.2 coordinate))| ≤
      radiusCoordinate
    exact abs_sub_dyadicCoordinateAnchor_le level (x.1 coordinate) (x.2 coordinate)
  have hcoordinate_sq : ∀ coordinate : Fin dimension,
      dist (x.1 coordinate)
          ((dyadicCubeAnchor dimension level (dyadicCubeLocate dimension level x)).1 coordinate) ^ 2 ≤
        radiusCoordinate ^ 2 := by
    intro coordinate
    have hdist_nonneg : 0 ≤ dist (x.1 coordinate)
        ((dyadicCubeAnchor dimension level
          (dyadicCubeLocate dimension level x)).1 coordinate) := dist_nonneg
    nlinarith [hcoordinate coordinate]
  have hsum :
      (∑ coordinate : Fin dimension,
          dist (x.1 coordinate)
            ((dyadicCubeAnchor dimension level
              (dyadicCubeLocate dimension level x)).1 coordinate) ^ 2) ≤
        (dimension : ℝ) * radiusCoordinate ^ 2 := by
    calc
      _ ≤ ∑ _coordinate : Fin dimension, radiusCoordinate ^ 2 := by
        exact Finset.sum_le_sum fun coordinate _ ↦ hcoordinate_sq coordinate
      _ = (dimension : ℝ) * radiusCoordinate ^ 2 := by simp
  change dist x.1
      (dyadicCubeAnchor dimension level (dyadicCubeLocate dimension level x)).1 ≤ _
  rw [EuclideanSpace.dist_eq]
  calc
    Real.sqrt (∑ coordinate : Fin dimension,
        dist (x.1 coordinate)
          ((dyadicCubeAnchor dimension level
            (dyadicCubeLocate dimension level x)).1 coordinate) ^ 2) ≤
        Real.sqrt ((dimension : ℝ) * radiusCoordinate ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt dimension * radiusCoordinate := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hradiusCoordinate_nonneg]
    _ = dyadicCubeRadius dimension level := by
      unfold dyadicCubeRadius
      dsimp [radiusCoordinate]
      ring

/-- Euclidean child-center/parent-center radius `sqrt dimension / 2^(level+1)`. -/
def dyadicCubeStepRadius (dimension level : ℕ) : ℝ :=
  Real.sqrt dimension / ((2 ^ (level + 1) : ℕ) : ℝ)

theorem dyadicCubeStepRadius_nonneg (dimension level : ℕ) :
    0 ≤ dyadicCubeStepRadius dimension level := by
  unfold dyadicCubeStepRadius
  positivity

theorem dist_dyadicCubeAnchor_parent_le (dimension level : ℕ)
    (index : dyadicCubeIndex dimension (level + 1)) :
    dist (dyadicCubeAnchor dimension (level + 1) index)
        (dyadicCubeAnchor dimension level (dyadicCubeParent dimension level index)) ≤
      dyadicCubeStepRadius dimension level := by
  let radiusCoordinate : ℝ := 1 / ((2 ^ (level + 1) : ℕ) : ℝ)
  have hradiusCoordinate_nonneg : 0 ≤ radiusCoordinate := by
    dsimp [radiusCoordinate]
    positivity
  have hcoordinate : ∀ coordinate : Fin dimension,
      dist ((dyadicCubeAnchor dimension (level + 1) index).1 coordinate)
          ((dyadicCubeAnchor dimension level
            (dyadicCubeParent dimension level index)).1 coordinate) ≤
        radiusCoordinate := by
    intro coordinate
    rw [Real.dist_eq]
    change |dyadicCoordinateAnchor (level + 1) (index coordinate) -
        dyadicCoordinateAnchor level
          (dyadicParentCoordinate level (index coordinate))| ≤ radiusCoordinate
    exact abs_dyadicCoordinateAnchor_succ_sub_parent_le level (index coordinate)
  have hcoordinate_sq : ∀ coordinate : Fin dimension,
      dist ((dyadicCubeAnchor dimension (level + 1) index).1 coordinate)
          ((dyadicCubeAnchor dimension level
            (dyadicCubeParent dimension level index)).1 coordinate) ^ 2 ≤
        radiusCoordinate ^ 2 := by
    intro coordinate
    have hdist_nonneg : 0 ≤
        dist ((dyadicCubeAnchor dimension (level + 1) index).1 coordinate)
          ((dyadicCubeAnchor dimension level
            (dyadicCubeParent dimension level index)).1 coordinate) := dist_nonneg
    nlinarith [hcoordinate coordinate]
  have hsum :
      (∑ coordinate : Fin dimension,
          dist ((dyadicCubeAnchor dimension (level + 1) index).1 coordinate)
            ((dyadicCubeAnchor dimension level
              (dyadicCubeParent dimension level index)).1 coordinate) ^ 2) ≤
        (dimension : ℝ) * radiusCoordinate ^ 2 := by
    calc
      _ ≤ ∑ _coordinate : Fin dimension, radiusCoordinate ^ 2 := by
        exact Finset.sum_le_sum fun coordinate _ ↦ hcoordinate_sq coordinate
      _ = (dimension : ℝ) * radiusCoordinate ^ 2 := by simp
  change dist (dyadicCubeAnchor dimension (level + 1) index).1
      (dyadicCubeAnchor dimension level
        (dyadicCubeParent dimension level index)).1 ≤ _
  rw [EuclideanSpace.dist_eq]
  calc
    Real.sqrt (∑ coordinate : Fin dimension,
        dist ((dyadicCubeAnchor dimension (level + 1) index).1 coordinate)
          ((dyadicCubeAnchor dimension level
            (dyadicCubeParent dimension level index)).1 coordinate) ^ 2) ≤
        Real.sqrt ((dimension : ℝ) * radiusCoordinate ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt dimension * radiusCoordinate := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hradiusCoordinate_nonneg]
    _ = dyadicCubeStepRadius dimension level := by
      unfold dyadicCubeStepRadius
      dsimp [radiusCoordinate]
      ring

/--
The source dyadic cube family packaged as a reusable finite quantization
hierarchy.  Parent coherence, measurable cells, and both Euclidean radius
bounds are proof fields rather than downstream assumptions.
-/
noncomputable def dyadicCubeHierarchy (dimension : ℕ) :
    FiniteQuantizationHierarchy (HalfOpenUnitCube dimension)
      (dyadicCubeIndex dimension) where
  locate := dyadicCubeLocate dimension
  anchor := dyadicCubeAnchor dimension
  parent := dyadicCubeParent dimension
  root := dyadicCubeRoot dimension
  locate_zero := dyadicCubeLocate_zero dimension
  parent_locate := dyadicCubeParent_locate dimension
  measurable_cell := measurableSet_dyadicCubeCell dimension
  stepRadius := dyadicCubeStepRadius dimension
  stepRadius_nonneg := dyadicCubeStepRadius_nonneg dimension
  dist_anchor_parent_le := dist_dyadicCubeAnchor_parent_le dimension
  radius := dyadicCubeRadius dimension
  radius_nonneg := dyadicCubeRadius_nonneg dimension
  dist_anchor_le := dist_dyadicCubeAnchor_le dimension

/-- Level `level` contains exactly `2^(dimension * level)` dyadic cubes. -/
theorem card_dyadicCubeIndex (dimension level : ℕ) :
    Fintype.card (dyadicCubeIndex dimension level) = 2 ^ (dimension * level) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  calc
    (2 ^ level) ^ dimension = 2 ^ (level * dimension) := (pow_mul 2 level dimension).symm
    _ = 2 ^ (dimension * level) := by rw [Nat.mul_comm]

/--
The generic finite-hierarchy transport theorem specialized to the exact
half-open dyadic cubes.  The displayed cell sets, radii, and cardinalities are
constructed facts; only finite first moments of the two laws remain analytic
premises.  This is still deterministic and makes no empirical-concentration
claim.
-/
theorem wassersteinOne_le_dyadicCube
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (HalfOpenUnitCube dimension))
    (basepoint : HalfOpenUnitCube dimension)
    (hmu : Integrable (fun x ↦ dist x basepoint) (mu : Measure _))
    (hnu : Integrable (fun x ↦ dist x basepoint) (nu : Measure _))
    (depth : ℕ) :
    ProbabilityCoupling.wassersteinOne mu nu ≤ ENNReal.ofReal
      (2 * dyadicCubeRadius dimension depth +
        ∑ level ∈ Finset.range depth, dyadicCubeStepRadius dimension level *
          ∑ index : dyadicCubeIndex dimension (level + 1),
            |(mu : Measure _).real
                {x | dyadicCubeLocate dimension (level + 1) x = index} -
              (nu : Measure _).real
                {x | dyadicCubeLocate dimension (level + 1) x = index}|) := by
  simpa [dyadicCubeHierarchy, FiniteQuantizationHierarchy.cell] using
    (FiniteQuantizationHierarchy.wassersteinOne_le_multiscale
      (dyadicCubeHierarchy dimension) mu nu basepoint hmu hnu depth)

end
end AppliedModelingLib.Probability
