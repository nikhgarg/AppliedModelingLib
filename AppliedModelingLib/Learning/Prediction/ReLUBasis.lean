import Mathlib.Analysis.Convex.Slope
import AppliedModelingLib.Learning.Prediction.LipschitzThresholdBasis

/-!
# ReLU coordinates on the unit interval

The elementary ReLU family used in one-dimensional omniprediction
approximations.  This module also records the intercept boundary: a homogeneous
linear span of these coordinates cannot approximate a nonzero constant because
every coordinate vanishes at zero.  Approximation theorems stated with a free
affine intercept should therefore use
`IsFixedFiniteAffineApproximateBasis` before being converted to a homogeneous
basis by adjoining the constant-one coordinate.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- The left endpoint of the probability-report interval. -/
def unitIntervalZero : UnitIntervalPoint := ⟨0, by constructor <;> norm_num⟩

/-- The ReLU coordinate with a threshold in the unit interval. -/
def unitIntervalReLU (threshold : UnitIntervalPoint) : UnitIntervalPoint → ℝ :=
  fun point => max 0 (point.1 - threshold.1)

/-- The common ReLU coordinate class on `[0, 1]`. -/
def unitIntervalReLUClass : Set (UnitIntervalPoint → ℝ) :=
  Set.range unitIntervalReLU

/-- Every unit-interval ReLU coordinate vanishes at zero. -/
theorem unitIntervalReLU_zero (threshold : UnitIntervalPoint) :
    unitIntervalReLU threshold unitIntervalZero = 0 := by
  unfold unitIntervalReLU
  apply max_eq_left
  change 0 - threshold.1 ≤ 0
  linarith [threshold.2.1]

/-- A homogeneous finite ReLU basis cannot approximate the constant-one
function with error strictly below one.  This makes the affine intercept in
some cited approximate-rank results semantically material. -/
theorem constantOne_not_isFiniteApproximateBasis_unitIntervalReLU
    (epsilon coefficientNorm : ℝ) (sparsity : ℕ) (hepsilon : epsilon < 1) :
    ¬ IsFiniteApproximateBasis ({fun _ : UnitIntervalPoint => 1} : Set (UnitIntervalPoint → ℝ))
      unitIntervalReLUClass epsilon sparsity coefficientNorm := by
  intro happrox
  rcases happrox (fun _ : UnitIntervalPoint => 1) (by simp) with
    ⟨dimension, basis, coefficient, _hsparsity, hbasis, _hcoefficient, _hnorm, herror⟩
  have hcombination : finiteLinearCombination coefficient basis unitIntervalZero = 0 := by
    unfold finiteLinearCombination
    apply Finset.sum_eq_zero
    intro index _
    have hmember := hbasis index
    change basis index ∈ Set.range unitIntervalReLU at hmember
    rcases hmember with ⟨threshold, hthreshold⟩
    rw [← hthreshold, unitIntervalReLU_zero]
    ring
  have hzeroError := herror unitIntervalZero
  rw [hcombination] at hzeroError
  norm_num at hzeroError
  linarith

/-- The discrete ReLU hinge at a natural-number threshold.  This is the
integer-grid form used in the constructive part of univariate convex
approximation arguments. -/
def discreteReLU (threshold point : ℕ) : ℝ := (point - threshold : ℕ)

/-- First forward difference of a real-valued sequence. -/
def discreteFirstDifference (function : ℕ → ℝ) (index : ℕ) : ℝ :=
  function (index + 1) - function index

/-- Second forward difference of a real-valued sequence. -/
def discreteSecondDifference (function : ℕ → ℝ) (index : ℕ) : ℝ :=
  function (index + 2) - 2 * function (index + 1) + function index

/-- The first difference is its initial value plus the telescoping sum of
second differences. -/
theorem discreteFirstDifference_eq_initial_add_sum_secondDifference
    (function : ℕ → ℝ) (index : ℕ) :
    discreteFirstDifference function index =
      discreteFirstDifference function 0 +
        ∑ prior ∈ Finset.range index, discreteSecondDifference function prior := by
  induction index with
  | zero => simp
  | succ index ih =>
      rw [Finset.sum_range_succ]
      calc
        discreteFirstDifference function (index + 1) =
            discreteFirstDifference function index + discreteSecondDifference function index := by
              unfold discreteFirstDifference discreteSecondDifference
              ring
        _ = (discreteFirstDifference function 0 +
              ∑ prior ∈ Finset.range index, discreteSecondDifference function prior) +
              discreteSecondDifference function index := by rw [ih]
        _ = discreteFirstDifference function 0 +
              (∑ prior ∈ Finset.range index, discreteSecondDifference function prior +
                discreteSecondDifference function index) := by ring

/-- Discrete Taylor expansion: every real-valued sequence is the sum of its
intercept, initial slope, and ReLU hinges weighted by its second differences.
For a discrete convex sequence those hinge weights are nonnegative, which is
the coefficient-control starting point in the convex ReLU-basis construction.
-/
theorem discreteTaylorExpansion (function : ℕ → ℝ) (point : ℕ) :
    function point = function 0 + point * discreteFirstDifference function 0 +
      ∑ knot ∈ Finset.range point,
        discreteSecondDifference function knot * discreteReLU (knot + 1) point := by
  induction point with
  | zero => simp [discreteReLU]
  | succ point ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one, discreteReLU]
      have hreLUDifference (knot : ℕ) (hknot : knot < point) :
          ((point + 1 - (knot + 1) : ℕ) : ℝ) =
            ((point - (knot + 1) : ℕ) : ℝ) + 1 := by
        norm_cast
        omega
      rw [show function (point + 1) = function point +
          discreteFirstDifference function point by
            unfold discreteFirstDifference
            ring]
      rw [ih]
      rw [discreteFirstDifference_eq_initial_add_sum_secondDifference function point]
      simp only [discreteReLU, Nat.sub_self, Nat.cast_zero, mul_zero, add_zero]
      have hsum :
          (∑ knot ∈ Finset.range point,
            discreteSecondDifference function knot * ↑(point + 1 - (knot + 1))) =
            (∑ knot ∈ Finset.range point,
              discreteSecondDifference function knot * ↑(point - (knot + 1))) +
              ∑ knot ∈ Finset.range point, discreteSecondDifference function knot := by
        calc
          (∑ knot ∈ Finset.range point,
              discreteSecondDifference function knot * ↑(point + 1 - (knot + 1))) =
              ∑ knot ∈ Finset.range point,
                (discreteSecondDifference function knot * ↑(point - (knot + 1)) +
                  discreteSecondDifference function knot) := by
                apply Finset.sum_congr rfl
                intro knot hknot
                rw [hreLUDifference knot (Finset.mem_range.mp hknot)]
                ring
          _ = (∑ knot ∈ Finset.range point,
                discreteSecondDifference function knot * ↑(point - (knot + 1))) +
                ∑ knot ∈ Finset.range point, discreteSecondDifference function knot := by
                rw [Finset.sum_add_distrib]
      rw [hsum]
      ring

/-- A discrete convex sequence has nonnegative second differences. -/
def IsDiscreteConvexSequence (function : ℕ → ℝ) : Prop :=
  ∀ index, 0 ≤ discreteSecondDifference function index

/-- Unit discrete slopes, the lattice form of one-Lipschitzness after scaling
the unit interval to an integer grid. -/
def HasUnitDiscreteSlopes (function : ℕ → ℝ) : Prop :=
  ∀ index, |discreteFirstDifference function index| ≤ 1

/-- Unit discrete slopes bound the telescoping sum of second differences by
two.  Convexity upgrades this signed bound to a total-curvature bound below. -/
theorem sum_discreteSecondDifference_le_two_of_unitSlopes
    (function : ℕ → ℝ) (count : ℕ)
    (hslopes : HasUnitDiscreteSlopes function) :
    (∑ index ∈ Finset.range count, discreteSecondDifference function index) ≤ 2 := by
  have htelescoping := discreteFirstDifference_eq_initial_add_sum_secondDifference
    function count
  have hlast : discreteFirstDifference function count ≤ 1 :=
    le_trans (le_abs_self _) (hslopes count)
  have hfirst : -(1 : ℝ) ≤ discreteFirstDifference function 0 :=
    neg_le_of_abs_le (hslopes 0)
  linarith

/-- The nonconstant coefficient mass in the discrete Taylor/ReLU expansion of
a convex unit-slope sequence is at most three: at most one for the initial
slope and at most two for total positive curvature. -/
theorem discreteTaylor_nonconstantCoefficientMass_le_three
    (function : ℕ → ℝ) (count : ℕ)
    (hconvex : IsDiscreteConvexSequence function)
    (hslopes : HasUnitDiscreteSlopes function) :
    |discreteFirstDifference function 0| +
      (∑ index ∈ Finset.range count, |discreteSecondDifference function index|) ≤ 3 := by
  have hcurvature := sum_discreteSecondDifference_le_two_of_unitSlopes
    function count hslopes
  have habs :
      (∑ index ∈ Finset.range count, |discreteSecondDifference function index|) =
        ∑ index ∈ Finset.range count, discreteSecondDifference function index := by
    apply Finset.sum_congr rfl
    intro index hindex
    exact abs_of_nonneg (hconvex index)
  rw [habs]
  linarith [hslopes 0]

/-- The finite family of integer-grid ReLU hinges, including the zero
threshold. -/
def finiteDiscreteReLUBasis (count : ℕ) :
    Fin (count + 1) → Fin (count + 1) → ℝ :=
  Fin.cons (fun point => discreteReLU 0 point.1)
    (fun hinge point => discreteReLU (hinge.1 + 1) point.1)

/-- Taylor coefficients for a finite grid.  The final hinge has zero
coefficient because it vanishes at every grid point; setting it explicitly to
zero avoids an artificial boundary coefficient. -/
def finiteDiscreteTaylorCoefficient (function : ℕ → ℝ) (count : ℕ) :
    Fin (count + 1) → ℝ :=
  Fin.cons (discreteFirstDifference function 0)
    (fun hinge => if hinge.1 + 1 = count then 0 else discreteSecondDifference function hinge.1)

/-- On a finite grid, the nonzero Taylor hinges are exactly the prefix of the
infinite discrete Taylor expansion.  Every later hinge vanishes at the
evaluated grid point. -/
theorem finiteDiscreteTaylor_hinge_sum_eq (function : ℕ → ℝ) (count : ℕ)
    (point : Fin (count + 1)) :
    (∑ hinge : Fin count,
      (if hinge.1 + 1 = count then 0 else discreteSecondDifference function hinge.1) *
        discreteReLU (hinge.1 + 1) point.1) =
      ∑ knot ∈ Finset.range point.1,
        discreteSecondDifference function knot * discreteReLU (knot + 1) point.1 := by
  let term : ℕ → ℝ := fun hinge =>
    (if hinge + 1 = count then 0 else discreteSecondDifference function hinge) *
      discreteReLU (hinge + 1) point.1
  change (∑ hinge : Fin count, term hinge.1) = _
  rw [Fin.sum_univ_eq_sum_range term count]
  have hpoint : point.1 ≤ count := by omega
  have hsubset : Finset.range point.1 ⊆ Finset.range count := by
    intro index hindex
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hindex) hpoint)
  have hright :
      (∑ knot ∈ Finset.range point.1,
        discreteSecondDifference function knot * discreteReLU (knot + 1) point.1) =
        ∑ knot ∈ Finset.range point.1, term knot := by
    apply Finset.sum_congr rfl
    intro knot hknot
    by_cases hlast : knot + 1 = count
    · have hpointEq : point.1 = count := by
        have hknotLt := Finset.mem_range.mp hknot
        omega
      simp [term, hlast, hpointEq, discreteReLU]
    · simp [term, hlast]
  rw [hright]
  exact (Finset.sum_subset hsubset (by
    intro index hindex hnotMember
    have hpointLe : point.1 ≤ index := Nat.le_of_not_gt (by
      simpa only [Finset.mem_range] using hnotMember)
    by_cases hlast : index + 1 = count
    · simp [term, hlast]
    · have hrelu : discreteReLU (index + 1) point.1 = 0 := by
        unfold discreteReLU
        norm_cast
        exact Nat.sub_eq_zero_of_le (le_trans hpointLe (Nat.le_succ index))
      simp [term, hlast, hrelu])).symm

/-- Exact finite-grid form of the discrete Taylor/ReLU expansion. -/
theorem finiteDiscreteTaylorExpansion (function : ℕ → ℝ) (count : ℕ)
    (point : Fin (count + 1)) :
    function point.1 = function 0 +
      finiteLinearCombination (finiteDiscreteTaylorCoefficient function count)
        (finiteDiscreteReLUBasis count) point := by
  unfold finiteLinearCombination finiteDiscreteTaylorCoefficient finiteDiscreteReLUBasis
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [show discreteReLU 0 point.1 = point.1 by simp [discreteReLU]]
  rw [finiteDiscreteTaylor_hinge_sum_eq]
  convert discreteTaylorExpansion function point.1 using 1 <;> ring

/-- A normalized finite grid of ReLU coordinates.  The initial ramp and each
hinge are divided by the grid size, so the coefficient of a sampled
one-Lipschitz function is measured in unit-interval rather than lattice
units.  Each hinge is duplicated to enforce the source's individual
coefficient constraint. -/
noncomputable def finiteNormalizedReLUDuplicatedBasis (count : ℕ) :
    Fin ((count + count) + 1) → Fin (count + 1) → ℝ :=
  Fin.cons
    (fun (point : Fin (count + 1)) => discreteReLU 0 point.1 / (count : ℝ))
    (Fin.addCases (motive := fun _ => Fin (count + 1) → ℝ)
      (fun (hinge : Fin count) (point : Fin (count + 1)) =>
        discreteReLU (hinge.1 + 1) point.1 / (count : ℝ))
      (fun (hinge : Fin count) (point : Fin (count + 1)) =>
        discreteReLU (hinge.1 + 1) point.1 / (count : ℝ)))

/-- Coefficients for the normalized duplicated grid basis.  A discrete
curvature jump can have scaled magnitude two, so splitting it equally across
the two identical hinge coordinates keeps every individual coefficient in
`[-1,1]`. -/
noncomputable def finiteNormalizedReLUDuplicatedTaylorCoefficient (function : ℕ → ℝ) (count : ℕ) :
    Fin ((count + count) + 1) → ℝ :=
  Fin.cons ((count : ℝ) * discreteFirstDifference function 0)
    (Fin.addCases (motive := fun _ => ℝ)
      (fun (hinge : Fin count) => (count : ℝ) *
        (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) / 2)
      (fun (hinge : Fin count) => (count : ℝ) *
        (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) / 2))

/-- Exact normalized and duplicated ReLU representation on a positive finite
grid, retaining the affine intercept separately. -/
theorem finiteNormalizedReLUDuplicatedTaylorExpansion (function : ℕ → ℝ) (count : ℕ)
    (hcount : 0 < count) (point : Fin (count + 1)) :
    function point.1 = function 0 +
      finiteLinearCombination (finiteNormalizedReLUDuplicatedTaylorCoefficient function count)
        (finiteNormalizedReLUDuplicatedBasis count) point := by
  have hraw := finiteDiscreteTaylorExpansion function count point
  unfold finiteLinearCombination finiteNormalizedReLUDuplicatedTaylorCoefficient
    finiteNormalizedReLUDuplicatedBasis
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  have hcountReal : (count : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcount
  have hduplicate :
      (∑ hinge : Fin count, (count : ℝ) *
          (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) / 2 *
          (discreteReLU (hinge.1 + 1) point.1 / (count : ℝ))) +
        (∑ hinge : Fin count, (count : ℝ) *
          (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) / 2 *
          (discreteReLU (hinge.1 + 1) point.1 / (count : ℝ))) =
        ∑ hinge : Fin count,
          (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) *
            discreteReLU (hinge.1 + 1) point.1 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro hinge _
    field_simp
    ring
  have hraw' : function point.1 = function 0 +
      (point.1 : ℝ) * discreteFirstDifference function 0 +
      ∑ hinge : Fin count,
        (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) *
          discreteReLU (hinge.1 + 1) point.1 := by
    unfold finiteLinearCombination finiteDiscreteTaylorCoefficient finiteDiscreteReLUBasis at hraw
    rw [Fin.sum_univ_succ] at hraw
    simp only [Fin.cons_zero, Fin.cons_succ] at hraw
    rw [show discreteReLU 0 point.1 = point.1 by simp [discreteReLU]] at hraw
    convert hraw using 1 <;> ring
  rw [hduplicate]
  rw [show discreteReLU 0 point.1 = point.1 by simp [discreteReLU]]
  rw [show (count : ℝ) * discreteFirstDifference function 0 *
      ((point.1 : ℝ) / (count : ℝ)) =
        (point.1 : ℝ) * discreteFirstDifference function 0 by field_simp]
  convert hraw' using 1 <;> ring

/-- The unit-slope condition after mapping a unit interval to a grid of size
`count`. -/
def HasScaledUnitDiscreteSlopes (function : ℕ → ℝ) (count : ℕ) : Prop :=
  ∀ index, |(count : ℝ) * discreteFirstDifference function index| ≤ 1

/-- Scaling a convex unit-interval grid function preserves the discrete
Taylor bound: its initial slope and total curvature have mass at most three. -/
theorem scaled_discreteTaylor_nonconstantCoefficientMass_le_three
    (function : ℕ → ℝ) (count : ℕ)
    (hconvex : IsDiscreteConvexSequence function)
    (hslopes : HasScaledUnitDiscreteSlopes function count) :
    |(count : ℝ) * discreteFirstDifference function 0| +
      (∑ index ∈ Finset.range count,
        |(count : ℝ) * discreteSecondDifference function index|) ≤ 3 := by
  let scaled : ℕ → ℝ := fun index => (count : ℝ) * function index
  have hconvexScaled : IsDiscreteConvexSequence scaled := by
    intro index
    rw [show discreteSecondDifference scaled index =
      (count : ℝ) * discreteSecondDifference function index by
        unfold scaled discreteSecondDifference
        ring]
    exact mul_nonneg (Nat.cast_nonneg count) (hconvex index)
  have hslopesScaled : HasUnitDiscreteSlopes scaled := by
    intro index
    rw [show discreteFirstDifference scaled index =
      (count : ℝ) * discreteFirstDifference function index by
        unfold scaled discreteFirstDifference
        ring]
    exact hslopes index
  have hmass :=
    discreteTaylor_nonconstantCoefficientMass_le_three scaled count hconvexScaled hslopesScaled
  have hfirst : discreteFirstDifference scaled 0 =
      (count : ℝ) * discreteFirstDifference function 0 := by
    unfold scaled discreteFirstDifference
    ring
  have hsecond (index : ℕ) : discreteSecondDifference scaled index =
      (count : ℝ) * discreteSecondDifference function index := by
    unfold scaled discreteSecondDifference
    ring
  rw [hfirst] at hmass
  simp_rw [hsecond] at hmass
  exact hmass

/-- Every coefficient in the duplicated normalized grid representation
obeys the paper's individual `[-1,1]` restriction. -/
theorem finiteNormalizedReLUDuplicatedTaylorCoefficient_abs_le_one
    (function : ℕ → ℝ) (count : ℕ)
    (hslopes : HasScaledUnitDiscreteSlopes function count)
    (coordinate : Fin ((count + count) + 1)) :
    |finiteNormalizedReLUDuplicatedTaylorCoefficient function count coordinate| ≤ 1 := by
  have hhinge (hinge : Fin count) :
      |(count : ℝ) *
        (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) / 2| ≤ 1 := by
    rw [abs_div]
    have hjump :
        |(count : ℝ) * discreteSecondDifference function hinge.1| ≤ 2 := by
      rw [show (count : ℝ) * discreteSecondDifference function hinge.1 =
        (count : ℝ) * discreteFirstDifference function (hinge.1 + 1) -
          (count : ℝ) * discreteFirstDifference function hinge.1 by
            unfold discreteFirstDifference discreteSecondDifference
            ring]
      calc
        |(count : ℝ) * discreteFirstDifference function (hinge.1 + 1) -
            (count : ℝ) * discreteFirstDifference function hinge.1| ≤
            |(count : ℝ) * discreteFirstDifference function (hinge.1 + 1)| +
              |(count : ℝ) * discreteFirstDifference function hinge.1| := by
            simpa only [sub_zero, zero_sub, abs_neg] using (_root_.abs_sub_le
              ((count : ℝ) * discreteFirstDifference function (hinge.1 + 1)) 0
              ((count : ℝ) * discreteFirstDifference function hinge.1))
        _ ≤ 1 + 1 := add_le_add (hslopes _) (hslopes _)
        _ = 2 := by norm_num
    by_cases hlast : hinge.1 + 1 = count
    · simp [hlast]
    · simp only [hlast, ite_false]
      nlinarith [abs_nonneg ((count : ℝ) * discreteSecondDifference function hinge.1)]
  unfold finiteNormalizedReLUDuplicatedTaylorCoefficient
  refine Fin.cases ?_ ?_ coordinate
  · simpa using hslopes 0
  · intro coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro hinge
      rw [Fin.cons_succ, Fin.addCases_left]
      exact hhinge hinge
    · intro hinge
      rw [Fin.cons_succ, Fin.addCases_right]
      exact hhinge hinge

/-- Convexity and scaled unit slopes give an `ℓ₁` coefficient norm at most
three for the duplicated normalized ReLU grid basis. -/
theorem sum_abs_finiteNormalizedReLUDuplicatedTaylorCoefficient_le_three
    (function : ℕ → ℝ) (count : ℕ)
    (hconvex : IsDiscreteConvexSequence function)
    (hslopes : HasScaledUnitDiscreteSlopes function count) :
    (∑ coordinate, |finiteNormalizedReLUDuplicatedTaylorCoefficient function count coordinate|) ≤ 3 := by
  have hmass := scaled_discreteTaylor_nonconstantCoefficientMass_le_three
    function count hconvex hslopes
  unfold finiteNormalizedReLUDuplicatedTaylorCoefficient
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  let zeroed : Fin count → ℝ := fun hinge =>
    (count : ℝ) *
      (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1)
  have hduplicate :
      (∑ hinge : Fin count, |zeroed hinge / 2|) +
        (∑ hinge : Fin count, |zeroed hinge / 2|) =
        ∑ hinge : Fin count, |zeroed hinge| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro hinge _
    rw [abs_div]
    norm_num
  rw [show (∑ hinge : Fin count,
      |(count : ℝ) *
        (if hinge.1 + 1 = count then (0 : ℝ) else discreteSecondDifference function hinge.1) / 2|) =
      ∑ hinge : Fin count, |zeroed hinge / 2| by rfl]
  rw [hduplicate]
  have hzeroedMass :
      (∑ hinge : Fin count, |zeroed hinge|) ≤
        ∑ index ∈ Finset.range count,
          |(count : ℝ) * discreteSecondDifference function index| := by
    let term : ℕ → ℝ := fun index =>
      if hindex : index < count then |zeroed ⟨index, hindex⟩| else 0
    have hleft : (∑ hinge : Fin count, |zeroed hinge|) =
        ∑ hinge : Fin count, term hinge.1 := by
      apply Finset.sum_congr rfl
      intro hinge _
      simp [term, hinge.isLt]
    rw [hleft]
    rw [Fin.sum_univ_eq_sum_range term count]
    apply Finset.sum_le_sum
    intro index hindex
    let hinge : Fin count := ⟨index, Finset.mem_range.mp hindex⟩
    change term index ≤ |(count : ℝ) * discreteSecondDifference function index|
    simp only [term, dif_pos (Finset.mem_range.mp hindex)]
    by_cases hlast : index + 1 = count
    · simp [zeroed, hlast, mul_nonneg (Nat.cast_nonneg count)
        (abs_nonneg (discreteSecondDifference function index))]
    · simp only [zeroed, hlast, ite_false]
      exact le_rfl
  calc
    |(count : ℝ) * discreteFirstDifference function 0| +
        (∑ hinge : Fin count, |zeroed hinge|) ≤
        |(count : ℝ) * discreteFirstDifference function 0| +
          ∑ index ∈ Finset.range count,
            |(count : ℝ) * discreteSecondDifference function index| :=
      add_le_add_right hzeroedMass _
    _ ≤ 3 := hmass

/-- Finite-grid functions that have a convex, scaled unit-slope discrete
extension.  The extension presentation lets the exact grid theorem state its
natural assumptions without asserting anything beyond the sampled grid. -/
def finiteGridConvexUnitSlopeClass (count : ℕ) : Set (Fin (count + 1) → ℝ) :=
  { values | ∃ extension : ℕ → ℝ,
      values = (fun point => extension point.1) ∧
        |extension 0| ≤ 1 ∧
        IsDiscreteConvexSequence extension ∧
        HasScaledUnitDiscreteSlopes extension count }

/-- The source approximate-dimension setting permits a fully free affine
intercept.  This companion grid class therefore retains exactly the convexity
and scaled unit-slope hypotheses, without a normalization at zero. -/
def finiteGridConvexUnitSlopeFreeInterceptClass (count : ℕ) :
    Set (Fin (count + 1) → ℝ) :=
  { values | ∃ extension : ℕ → ℝ,
      values = (fun point => extension point.1) ∧
        IsDiscreteConvexSequence extension ∧
        HasScaledUnitDiscreteSlopes extension count }

/-- The normalized duplicated ReLU grid basis is an exact affine basis for
convex unit-slope grid data.  Its listed coordinates have coefficient norm at
most three; the separately recorded intercept has magnitude at most one. -/
theorem finiteNormalizedReLUDuplicated_isFixedFiniteAffineApproximateBasis
    (count : ℕ) (hcount : 0 < count) :
    IsFixedFiniteAffineApproximateBasis (finiteGridConvexUnitSlopeClass count)
      (finiteNormalizedReLUDuplicatedBasis count) 0 1 3 := by
  intro values hvalues
  rcases hvalues with ⟨extension, hvalues, hintercept, hconvex, hslopes⟩
  refine ⟨extension 0, finiteNormalizedReLUDuplicatedTaylorCoefficient extension count,
    hintercept, ?_, ?_, ?_⟩
  · exact finiteNormalizedReLUDuplicatedTaylorCoefficient_abs_le_one
      extension count hslopes
  · exact sum_abs_finiteNormalizedReLUDuplicatedTaylorCoefficient_le_three
      extension count hconvex hslopes
  · intro point
    rw [hvalues]
    change |extension point.1 -
      (extension 0 + finiteLinearCombination
        (finiteNormalizedReLUDuplicatedTaylorCoefficient extension count)
        (finiteNormalizedReLUDuplicatedBasis count) point)| ≤ 0
    rw [finiteNormalizedReLUDuplicatedTaylorExpansion extension count hcount point]
    simp

/-- The same Taylor expansion for the source-style class with an unrestricted
affine intercept.  Only the nonconstant Taylor coefficients carry the
uniform `ℓ₁` budget. -/
theorem finiteNormalizedReLUDuplicated_isFixedFiniteAffineL1ApproximateBasis
    (count : ℕ) (hcount : 0 < count) :
    IsFixedFiniteAffineL1ApproximateBasis
      (finiteGridConvexUnitSlopeFreeInterceptClass count)
      (finiteNormalizedReLUDuplicatedBasis count) 0 3 := by
  intro values hvalues
  rcases hvalues with ⟨extension, hvalues, hconvex, hslopes⟩
  refine ⟨extension 0, finiteNormalizedReLUDuplicatedTaylorCoefficient extension count, ?_, ?_⟩
  · exact sum_abs_finiteNormalizedReLUDuplicatedTaylorCoefficient_le_three
      extension count hconvex hslopes
  · intro point
    rw [hvalues]
    change |extension point.1 -
      (extension 0 + finiteLinearCombination
        (finiteNormalizedReLUDuplicatedTaylorCoefficient extension count)
        (finiteNormalizedReLUDuplicatedBasis count) point)| ≤ 0
    rw [finiteNormalizedReLUDuplicatedTaylorExpansion extension count hcount point]
    simp

/-- Values of a real function sampled on the uniform grid of `[0,1]`.  This
real-valued presentation is convenient for the convex-secant lemma below;
the later report-level bridge identifies these samples with
`uniformGridPoint`. -/
noncomputable def uniformGridSample (function : ℝ → ℝ) (count index : ℕ) : ℝ :=
  function ((index : ℝ) / (count : ℝ))

/-- Convexity on the report interval makes every admissible triple of
uniform-grid samples discretely convex.  The index condition is explicit:
convexity is used only at points in `[0,1]`, not outside the model domain. -/
theorem uniformGridSample_discreteSecondDifference_nonneg_of_convex
    (function : ℝ → ℝ) (count index : ℕ) (hcount : 0 < count)
    (hindex : index + 2 ≤ count)
    (hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) function) :
    0 ≤ discreteSecondDifference (uniformGridSample function count) index := by
  let x : ℝ := (index : ℝ) / (count : ℝ)
  let y : ℝ := ((index + 1 : ℕ) : ℝ) / (count : ℝ)
  let z : ℝ := ((index + 2 : ℕ) : ℝ) / (count : ℝ)
  have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg index) (le_of_lt hcountReal)
    · apply (div_le_one₀ hcountReal).2
      exact_mod_cast le_trans (Nat.le_add_right index 2) hindex
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg (index + 1)) (le_of_lt hcountReal)
    · apply (div_le_one₀ hcountReal).2
      exact_mod_cast (show index + 1 ≤ count by omega)
  have hz : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg (index + 2)) (le_of_lt hcountReal)
    · exact (div_le_one₀ hcountReal).2 (by exact_mod_cast hindex)
  have hxy : x < y := by
    apply (div_lt_div_iff_of_pos_right hcountReal).2
    push_cast
    linarith
  have hyz : y < z := by
    apply (div_lt_div_iff_of_pos_right hcountReal).2
    push_cast
    linarith
  have hslope := hconvex.slope_mono_adjacent hx hz hxy hyz
  have hyx : y - x = 1 / (count : ℝ) := by
    dsimp [x, y]
    push_cast
    ring
  have hzy : z - y = 1 / (count : ℝ) := by
    dsimp [y, z]
    push_cast
    ring
  rw [hyx, hzy] at hslope
  have hdenominator : (0 : ℝ) < 1 / (count : ℝ) := by positivity
  have hdifference := (div_le_div_iff_of_pos_right hdenominator).mp hslope
  unfold discreteSecondDifference uniformGridSample
  change 0 ≤ function z - 2 * function y + function x
  linarith

/-- A one-Lipschitz function on the report interval has unit scaled first
differences on every adjacent uniform-grid pair. -/
theorem uniformGridSample_scaledFirstDifference_abs_le_one_of_lipschitz
    (function : ℝ → ℝ) (count index : ℕ) (hcount : 0 < count)
    (hindex : index + 1 ≤ count)
    (hLipschitz : LipschitzOnWith 1 function (Set.Icc (0 : ℝ) 1)) :
    |(count : ℝ) * discreteFirstDifference (uniformGridSample function count) index| ≤ 1 := by
  let x : ℝ := (index : ℝ) / (count : ℝ)
  let y : ℝ := ((index + 1 : ℕ) : ℝ) / (count : ℝ)
  have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg index) (le_of_lt hcountReal)
    · apply (div_le_one₀ hcountReal).2
      exact_mod_cast le_trans (Nat.le_add_right index 1) hindex
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg (index + 1)) (le_of_lt hcountReal)
    · exact (div_le_one₀ hcountReal).2 (by exact_mod_cast hindex)
  have hdistance := LipschitzOnWith.dist_le_mul hLipschitz x hx y hy
  have hyx : y - x = 1 / (count : ℝ) := by
    dsimp [x, y]
    push_cast
    ring
  unfold discreteFirstDifference uniformGridSample
  change |(count : ℝ) * (function y - function x)| ≤ 1
  have hdistance' : |function y - function x| ≤ 1 / (count : ℝ) := by
    calc
      |function y - function x| = dist (function x) (function y) := by
        rw [Real.dist_eq, abs_sub_comm]
      _ ≤ 1 * dist x y := by simpa using hdistance
      _ = 1 / (count : ℝ) := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (le_of_lt (by rw [hyx]; positivity))]
        rw [hyx]
        ring
  calc
    |(count : ℝ) * (function y - function x)| =
        (count : ℝ) * |function y - function x| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg count)]
    _ ≤ (count : ℝ) * (1 / (count : ℝ)) :=
      mul_le_mul_of_nonneg_left hdistance' (le_of_lt hcountReal)
    _ = 1 := by field_simp

/-- The adjacent slope of finite grid data. -/
def finiteGridSlope {count : ℕ} (values : Fin (count + 1) → ℝ)
    (index : Fin count) : ℝ :=
  values index.succ - values index.castSucc

/-- The final adjacent slope of a positive finite grid. -/
def finiteGridLastSlope {count : ℕ} (values : Fin (count + 1) → ℝ)
    (hcount : 0 < count) : ℝ :=
  finiteGridSlope values ⟨count - 1, by omega⟩

/-- Extend finite-grid slopes by the last slope after the report interval. -/
def finiteGridTailSlope {count : ℕ} (values : Fin (count + 1) → ℝ)
    (hcount : 0 < count) (index : ℕ) : ℝ :=
  if hindex : index < count then finiteGridSlope values ⟨index, hindex⟩
  else finiteGridLastSlope values hcount

/-- The affine-tail extension of finite grid values.  It agrees with the grid
on its original domain and continues linearly with the final adjacent slope. -/
def finiteGridAffineTailExtension {count : ℕ} (values : Fin (count + 1) → ℝ)
    (hcount : 0 < count) (index : ℕ) : ℝ :=
  values 0 + ∑ prior ∈ Finset.range index, finiteGridTailSlope values hcount prior

/-- Adjacent finite-grid slopes are nondecreasing wherever both neighboring
slopes occur in the original grid. -/
def HasMonotoneFiniteGridSlopes {count : ℕ} (values : Fin (count + 1) → ℝ) : Prop :=
  ∀ index (hindex : index + 2 ≤ count),
    finiteGridSlope values ⟨index, by omega⟩ ≤
      finiteGridSlope values ⟨index + 1, by omega⟩

theorem discreteFirstDifference_finiteGridAffineTailExtension
    {count : ℕ} (values : Fin (count + 1) → ℝ) (hcount : 0 < count) (index : ℕ) :
    discreteFirstDifference (finiteGridAffineTailExtension values hcount) index =
      finiteGridTailSlope values hcount index := by
  unfold discreteFirstDifference finiteGridAffineTailExtension
  rw [Finset.sum_range_succ]
  ring

theorem finiteGridAffineTailExtension_eq_values
    {count : ℕ} (values : Fin (count + 1) → ℝ) (hcount : 0 < count)
    (index : ℕ) (hindex : index ≤ count) :
    finiteGridAffineTailExtension values hcount index =
      values ⟨index, Nat.lt_succ_of_le hindex⟩ := by
  induction index with
  | zero => simp [finiteGridAffineTailExtension]
  | succ index ih =>
      have hprevious : index ≤ count := by omega
      have hstrict : index < count := by omega
      rw [finiteGridAffineTailExtension, Finset.sum_range_succ]
      rw [show values 0 + (∑ x ∈ Finset.range index, finiteGridTailSlope values hcount x +
          finiteGridTailSlope values hcount index) =
        (values 0 + ∑ x ∈ Finset.range index, finiteGridTailSlope values hcount x) +
          finiteGridTailSlope values hcount index by ring]
      change finiteGridAffineTailExtension values hcount index +
        finiteGridTailSlope values hcount index = values ⟨index + 1, Nat.lt_succ_of_le hindex⟩
      rw [ih hprevious]
      simp only [finiteGridTailSlope, dif_pos hstrict, finiteGridSlope]
      have hsucc : (⟨index, hstrict⟩ : Fin count).succ =
          ⟨index + 1, Nat.lt_succ_of_le hindex⟩ := Fin.ext rfl
      have hcast : (⟨index, hstrict⟩ : Fin count).castSucc =
          ⟨index, Nat.lt_succ_of_le hprevious⟩ := Fin.ext rfl
      rw [hsucc, hcast]
      ring

/-- A finite grid with nondecreasing adjacent slopes has a discretely convex
affine-tail extension. -/
theorem isDiscreteConvexSequence_finiteGridAffineTailExtension
    {count : ℕ} (values : Fin (count + 1) → ℝ) (hcount : 0 < count)
    (hmonotone : HasMonotoneFiniteGridSlopes values) :
    IsDiscreteConvexSequence (finiteGridAffineTailExtension values hcount) := by
  intro index
  rw [show discreteSecondDifference (finiteGridAffineTailExtension values hcount) index =
      discreteFirstDifference (finiteGridAffineTailExtension values hcount) (index + 1) -
        discreteFirstDifference (finiteGridAffineTailExtension values hcount) index by
        unfold discreteSecondDifference discreteFirstDifference
        have htwo : index + 2 = 2 + index := by omega
        have hone : index + 1 = 1 + index := by omega
        rw [htwo, hone]
        ring]
  rw [discreteFirstDifference_finiteGridAffineTailExtension,
    discreteFirstDifference_finiteGridAffineTailExtension]
  by_cases hnext : index + 1 < count
  · have hcurrent : index < count := by omega
    simp only [finiteGridTailSlope, dif_pos hnext, dif_pos hcurrent]
    apply sub_nonneg.mpr
    exact hmonotone index (by omega)
  · by_cases hcurrent : index < count
    · have hterminal : index + 1 = count := by omega
      simp only [finiteGridTailSlope, dif_neg hnext, dif_pos hcurrent]
      unfold finiteGridLastSlope
      have hindex : index = count - 1 := by omega
      subst index
      simp
    · simp only [finiteGridTailSlope, dif_neg hnext, dif_neg hcurrent]
      simp

/-- Unit scaled slopes on the original grid persist through the affine tail. -/
theorem hasScaledUnitDiscreteSlopes_finiteGridAffineTailExtension
    {count : ℕ} (values : Fin (count + 1) → ℝ) (hcount : 0 < count)
    (hslopes : ∀ index : Fin count, |(count : ℝ) * finiteGridSlope values index| ≤ 1) :
    HasScaledUnitDiscreteSlopes (finiteGridAffineTailExtension values hcount) count := by
  intro index
  rw [discreteFirstDifference_finiteGridAffineTailExtension]
  by_cases hindex : index < count
  · simp only [finiteGridTailSlope, dif_pos hindex]
    exact hslopes ⟨index, hindex⟩
  · simp only [finiteGridTailSlope, dif_neg hindex, finiteGridLastSlope]
    exact hslopes ⟨count - 1, by omega⟩

/-- Convex uniform-grid samples have nondecreasing finite-grid slopes. -/
theorem uniformGridSample_hasMonotoneFiniteGridSlopes_of_convex
    (function : ℝ → ℝ) (count : ℕ) (hcount : 0 < count)
    (hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) function) :
    HasMonotoneFiniteGridSlopes
      (fun point : Fin (count + 1) => uniformGridSample function count point.1) := by
  intro index hindex
  change uniformGridSample function count (index + 1) - uniformGridSample function count index ≤
    uniformGridSample function count (index + 2) - uniformGridSample function count (index + 1)
  have hsecond := uniformGridSample_discreteSecondDifference_nonneg_of_convex
    function count index hcount hindex hconvex
  unfold discreteSecondDifference at hsecond
  linarith

/-- One-Lipschitz uniform-grid samples have scaled finite-grid slopes bounded
by one. -/
theorem uniformGridSample_scaled_finiteGridSlope_abs_le_one_of_lipschitz
    (function : ℝ → ℝ) (count : ℕ) (hcount : 0 < count) (index : Fin count)
    (hLipschitz : LipschitzOnWith 1 function (Set.Icc (0 : ℝ) 1)) :
    |(count : ℝ) * finiteGridSlope
      (fun point : Fin (count + 1) => uniformGridSample function count point.1) index| ≤ 1 := by
  change |(count : ℝ) * discreteFirstDifference (uniformGridSample function count) index.1| ≤ 1
  apply uniformGridSample_scaledFirstDifference_abs_le_one_of_lipschitz
    function count index.1 hcount
  · omega
  · exact hLipschitz

/-- Uniform samples of a convex one-Lipschitz function with bounded initial
value belong to the finite convex unit-slope grid class. -/
theorem uniformGridSample_mem_finiteGridConvexUnitSlopeClass_of_convex_lipschitz
    (function : ℝ → ℝ) (count : ℕ) (hcount : 0 < count)
    (hzero : |function 0| ≤ 1)
    (hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) function)
    (hLipschitz : LipschitzOnWith 1 function (Set.Icc (0 : ℝ) 1)) :
    (fun point : Fin (count + 1) => uniformGridSample function count point.1) ∈
      finiteGridConvexUnitSlopeClass count := by
  let values : Fin (count + 1) → ℝ :=
    fun point => uniformGridSample function count point.1
  have hmonotone : HasMonotoneFiniteGridSlopes values := by
    exact uniformGridSample_hasMonotoneFiniteGridSlopes_of_convex
      function count hcount hconvex
  have hslopes : ∀ index : Fin count, |(count : ℝ) * finiteGridSlope values index| ≤ 1 := by
    intro index
    exact uniformGridSample_scaled_finiteGridSlope_abs_le_one_of_lipschitz
      function count hcount index hLipschitz
  refine ⟨finiteGridAffineTailExtension values hcount, ?_, ?_, ?_, ?_⟩
  · funext point
    exact (finiteGridAffineTailExtension_eq_values values hcount point.1 (by omega)).symm
  · simpa [finiteGridAffineTailExtension, values, uniformGridSample] using hzero
  · exact isDiscreteConvexSequence_finiteGridAffineTailExtension values hcount hmonotone
  · exact hasScaledUnitDiscreteSlopes_finiteGridAffineTailExtension values hcount hslopes

/-- Without a normalization condition at zero, convex one-Lipschitz samples
still have the exact source-style discrete convex extension. -/
theorem uniformGridSample_mem_finiteGridConvexUnitSlopeFreeInterceptClass_of_convex_lipschitz
    (function : ℝ → ℝ) (count : ℕ) (hcount : 0 < count)
    (hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) function)
    (hLipschitz : LipschitzOnWith 1 function (Set.Icc (0 : ℝ) 1)) :
    (fun point : Fin (count + 1) => uniformGridSample function count point.1) ∈
      finiteGridConvexUnitSlopeFreeInterceptClass count := by
  let values : Fin (count + 1) → ℝ :=
    fun point => uniformGridSample function count point.1
  have hmonotone : HasMonotoneFiniteGridSlopes values := by
    exact uniformGridSample_hasMonotoneFiniteGridSlopes_of_convex
      function count hcount hconvex
  have hslopes : ∀ index : Fin count, |(count : ℝ) * finiteGridSlope values index| ≤ 1 := by
    intro index
    exact uniformGridSample_scaled_finiteGridSlope_abs_le_one_of_lipschitz
      function count hcount index hLipschitz
  refine ⟨finiteGridAffineTailExtension values hcount, ?_, ?_, ?_⟩
  · funext point
    exact (finiteGridAffineTailExtension_eq_values values hcount point.1 (by omega)).symm
  · exact isDiscreteConvexSequence_finiteGridAffineTailExtension values hcount hmonotone
  · exact hasScaledUnitDiscreteSlopes_finiteGridAffineTailExtension values hcount hslopes

/-- At uniform-grid points, the positive-part of a difference is the scaled
integer-grid ReLU. -/
theorem max_uniformGrid_difference_eq_discreteReLU_div
    (count threshold point : ℕ) (hcount : 0 < count) :
    max 0 ((point : ℝ) / (count : ℝ) - (threshold : ℝ) / (count : ℝ)) =
      discreteReLU threshold point / (count : ℝ) := by
  by_cases hle : point ≤ threshold
  · have hsub : point - threshold = 0 := Nat.sub_eq_zero_of_le hle
    rw [show (point : ℝ) / (count : ℝ) - (threshold : ℝ) / (count : ℝ) =
      ((point : ℝ) - (threshold : ℝ)) / (count : ℝ) by ring]
    have hleft : ((point : ℝ) - (threshold : ℝ)) / (count : ℝ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact sub_nonpos.mpr (by exact_mod_cast hle)
      · positivity
    rw [max_eq_left hleft]
    simp [discreteReLU, hsub]
  · have hlt : threshold < point := Nat.lt_of_not_ge hle
    have hle' : threshold ≤ point := Nat.le_of_lt hlt
    rw [show (point : ℝ) / (count : ℝ) - (threshold : ℝ) / (count : ℝ) =
      ((point : ℝ) - (threshold : ℝ)) / (count : ℝ) by ring]
    rw [← Nat.cast_sub hle']
    simp only [discreteReLU]
    rw [max_eq_right (by positivity)]

/-- The continuous ReLU lift of the normalized duplicated grid basis. -/
noncomputable def finiteNormalizedReLUDuplicatedUnitIntervalBasis
    (count : ℕ) (hcount : 0 < count) :
    Fin ((count + count) + 1) → UnitIntervalPoint → ℝ :=
  Fin.cons (fun point => point.1)
    (Fin.addCases (motive := fun _ => UnitIntervalPoint → ℝ)
      (fun hinge => unitIntervalReLU (uniformGridPoint count hcount hinge.succ))
      (fun hinge => unitIntervalReLU (uniformGridPoint count hcount hinge.succ)))

/-- The continuous lifted coordinates agree with the normalized discrete
coordinates at every grid point. -/
theorem finiteNormalizedReLUDuplicatedUnitIntervalBasis_apply_uniformGridPoint
    (count : ℕ) (hcount : 0 < count) (coordinate : Fin ((count + count) + 1))
    (point : Fin (count + 1)) :
    finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate
      (uniformGridPoint count hcount point) =
    finiteNormalizedReLUDuplicatedBasis count coordinate point := by
  unfold finiteNormalizedReLUDuplicatedUnitIntervalBasis
    finiteNormalizedReLUDuplicatedBasis
  refine Fin.cases ?_ ?_ coordinate
  · simp only [Fin.cons_zero]
    unfold discreteReLU uniformGridPoint
    dsimp
  · intro coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro hinge
      simp only [Fin.cons_succ, Fin.addCases_left]
      unfold unitIntervalReLU uniformGridPoint
      dsimp
      exact max_uniformGrid_difference_eq_discreteReLU_div
        count (hinge.1 + 1) point.1 hcount
    · intro hinge
      simp only [Fin.cons_succ, Fin.addCases_right]
      unfold unitIntervalReLU uniformGridPoint
      dsimp
      exact max_uniformGrid_difference_eq_discreteReLU_div
        count (hinge.1 + 1) point.1 hcount

/-- Every continuous lifted grid coordinate is a unit-interval ReLU. -/
theorem finiteNormalizedReLUDuplicatedUnitIntervalBasis_mem_unitIntervalReLUClass
    (count : ℕ) (hcount : 0 < count) (coordinate : Fin ((count + count) + 1)) :
    finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate ∈
      unitIntervalReLUClass := by
  unfold finiteNormalizedReLUDuplicatedUnitIntervalBasis unitIntervalReLUClass
  refine Fin.cases ?_ ?_ coordinate
  · refine ⟨unitIntervalZero, ?_⟩
    funext point
    simp only [Fin.cons_zero]
    change max 0 (point.1 - 0) = point.1
    rw [max_eq_right (sub_nonneg.mpr point.2.1)]
    ring
  · intro coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro hinge
      simp only [Fin.cons_succ, Fin.addCases_left]
      exact ⟨uniformGridPoint count hcount hinge.succ, rfl⟩
    · intro hinge
      simp only [Fin.cons_succ, Fin.addCases_right]
      exact ⟨uniformGridPoint count hcount hinge.succ, rfl⟩

/-- A ReLU coordinate is one-Lipschitz on the unit interval. -/
theorem unitIntervalReLU_abs_sub_le
    (threshold point other : UnitIntervalPoint) :
    |unitIntervalReLU threshold point - unitIntervalReLU threshold other| ≤
      |point.1 - other.1| := by
  unfold unitIntervalReLU
  calc
    |max 0 (point.1 - threshold.1) - max 0 (other.1 - threshold.1)| ≤
        |(point.1 - threshold.1) - (other.1 - threshold.1)| :=
      by simpa only [max_comm] using
        (abs_max_sub_max_le_abs (point.1 - threshold.1) (other.1 - threshold.1) 0)
    _ = |point.1 - other.1| := by ring_nf

/-- Every coordinate of the continuous lifted grid basis is one-Lipschitz. -/
theorem finiteNormalizedReLUDuplicatedUnitIntervalBasis_abs_sub_le
    (count : ℕ) (hcount : 0 < count) (coordinate : Fin ((count + count) + 1))
    (point other : UnitIntervalPoint) :
    |finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate point -
      finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate other| ≤
      |point.1 - other.1| := by
  unfold finiteNormalizedReLUDuplicatedUnitIntervalBasis
  refine Fin.cases ?_ ?_ coordinate
  · simp only [Fin.cons_zero]
    exact le_of_eq (by ring)
  · intro coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro hinge
      simp only [Fin.cons_succ, Fin.addCases_left]
      exact unitIntervalReLU_abs_sub_le _ _ _
    · intro hinge
      simp only [Fin.cons_succ, Fin.addCases_right]
      exact unitIntervalReLU_abs_sub_le _ _ _

/-- The variation of a finite linear combination of lifted ReLU coordinates
is bounded by its coefficient `ℓ₁` norm times the report distance. -/
theorem finiteLinearCombination_liftedReLUBasis_abs_sub_le
    (count : ℕ) (hcount : 0 < count)
    (coefficient : Fin ((count + count) + 1) → ℝ)
    (point other : UnitIntervalPoint) :
    |finiteLinearCombination coefficient
      (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point -
      finiteLinearCombination coefficient
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) other| ≤
      (∑ coordinate, |coefficient coordinate|) * |point.1 - other.1| := by
  unfold finiteLinearCombination
  rw [← Finset.sum_sub_distrib]
  calc
    |(∑ coordinate, (coefficient coordinate *
        finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate point -
          coefficient coordinate *
            finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate other))| ≤
        ∑ coordinate, |(coefficient coordinate *
          finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate point -
            coefficient coordinate *
              finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate other)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ coordinate, |coefficient coordinate| *
        |finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate point -
          finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate other| := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [show coefficient coordinate *
          finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate point -
            coefficient coordinate *
              finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate other =
            coefficient coordinate *
              (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate point -
                finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount coordinate other) by ring]
      rw [abs_mul]
    _ ≤ ∑ coordinate, |coefficient coordinate| * |point.1 - other.1| := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact mul_le_mul_of_nonneg_left
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis_abs_sub_le
          count hcount coordinate point other)
        (abs_nonneg _)
    _ = (∑ coordinate, |coefficient coordinate|) * |point.1 - other.1| := by
      rw [Finset.sum_mul]

/-- A linear combination of lifted ReLUs agrees with its normalized discrete
counterpart at every uniform-grid point. -/
theorem finiteLinearCombination_liftedReLUBasis_apply_uniformGridPoint
    (count : ℕ) (hcount : 0 < count)
    (coefficient : Fin ((count + count) + 1) → ℝ) (point : Fin (count + 1)) :
    finiteLinearCombination coefficient
      (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount)
      (uniformGridPoint count hcount point) =
    finiteLinearCombination coefficient (finiteNormalizedReLUDuplicatedBasis count) point := by
  unfold finiteLinearCombination
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [finiteNormalizedReLUDuplicatedUnitIntervalBasis_apply_uniformGridPoint]

/-- The midpoint of two valid probability reports. -/
noncomputable def unitIntervalMidpoint
    (left right : UnitIntervalPoint) : UnitIntervalPoint :=
  ⟨(left.1 + right.1) / 2, by
    constructor <;> nlinarith [left.2.1, left.2.2, right.2.1, right.2.2]⟩

/-- A ReLU whose threshold lies outside the open interval from `left` to
`right` is affine at their midpoint. -/
theorem unitIntervalReLU_midpoint_eq_average_of_outside
    (threshold left right : UnitIntervalPoint)
    (horder : left.1 ≤ right.1)
    (houtside : threshold.1 ≤ left.1 ∨ right.1 ≤ threshold.1) :
    unitIntervalReLU threshold (unitIntervalMidpoint left right) =
      (unitIntervalReLU threshold left + unitIntervalReLU threshold right) / 2 := by
  rcases houtside with hleft | hright
  · have hleftMid : threshold.1 ≤ (unitIntervalMidpoint left right).1 := by
      dsimp [unitIntervalMidpoint]
      linarith
    have hleftRight : threshold.1 ≤ right.1 := by
      linarith
    unfold unitIntervalReLU
    rw [max_eq_right (sub_nonneg.mpr hleftMid),
      max_eq_right (sub_nonneg.mpr hleft),
      max_eq_right (sub_nonneg.mpr hleftRight)]
    dsimp [unitIntervalMidpoint]
    ring
  · have hleftRight : left.1 ≤ threshold.1 := by
      linarith
    have hmidRight : (unitIntervalMidpoint left right).1 ≤ threshold.1 := by
      dsimp [unitIntervalMidpoint]
      linarith
    unfold unitIntervalReLU
    rw [max_eq_left (sub_nonpos.mpr hmidRight),
      max_eq_left (sub_nonpos.mpr hleftRight),
      max_eq_left (sub_nonpos.mpr hright)]
    ring

/-- A finite combination of ReLUs whose thresholds avoid an open interval is
affine at the interval midpoint. -/
theorem finiteLinearCombination_midpoint_eq_average_of_outside
    {n : ℕ} (basis : Fin n → UnitIntervalPoint → ℝ) (coefficient : Fin n → ℝ)
    (left right : UnitIntervalPoint) (horder : left.1 ≤ right.1)
    (hbasis : ∀ index, basis index ∈ unitIntervalReLUClass)
    (houtside : ∀ index threshold, basis index = unitIntervalReLU threshold →
      threshold.1 ≤ left.1 ∨ right.1 ≤ threshold.1) :
    finiteLinearCombination coefficient basis (unitIntervalMidpoint left right) =
      (finiteLinearCombination coefficient basis left +
        finiteLinearCombination coefficient basis right) / 2 := by
  have hcoordinate : ∀ index,
      basis index (unitIntervalMidpoint left right) =
        (basis index left + basis index right) / 2 := by
    intro index
    rcases hbasis index with ⟨threshold, hthreshold⟩
    rw [← hthreshold]
    exact unitIntervalReLU_midpoint_eq_average_of_outside threshold left right horder
      (houtside index threshold hthreshold.symm)
  unfold finiteLinearCombination
  calc
    ∑ index, coefficient index * basis index (unitIntervalMidpoint left right) =
        ∑ index, coefficient index * ((basis index left + basis index right) / 2) := by
          apply Finset.sum_congr rfl
          intro index _
          rw [hcoordinate]
    _ = ((∑ index, coefficient index * basis index left) +
        ∑ index, coefficient index * basis index right) / 2 := by
          calc
            ∑ index, coefficient index * ((basis index left + basis index right) / 2) =
                ∑ index, (coefficient index * basis index left / 2 +
                  coefficient index * basis index right / 2) := by
                  apply Finset.sum_congr rfl
                  intro index _
                  ring
            _ = ((∑ index, coefficient index * basis index left) +
                ∑ index, coefficient index * basis index right) / 2 := by
                  rw [Finset.sum_add_distrib]
                  rw [← Finset.sum_div, ← Finset.sum_div]
                  ring

/-- Adding a free intercept preserves the midpoint-affinity conclusion for a
threshold-free interval. -/
theorem affineFiniteLinearCombination_midpoint_eq_average_of_outside
    {n : ℕ} (intercept : ℝ) (basis : Fin n → UnitIntervalPoint → ℝ)
    (coefficient : Fin n → ℝ) (left right : UnitIntervalPoint)
    (horder : left.1 ≤ right.1)
    (hbasis : ∀ index, basis index ∈ unitIntervalReLUClass)
    (houtside : ∀ index threshold, basis index = unitIntervalReLU threshold →
      threshold.1 ≤ left.1 ∨ right.1 ≤ threshold.1) :
    intercept + finiteLinearCombination coefficient basis (unitIntervalMidpoint left right) =
      ((intercept + finiteLinearCombination coefficient basis left) +
        (intercept + finiteLinearCombination coefficient basis right)) / 2 := by
  rw [finiteLinearCombination_midpoint_eq_average_of_outside basis coefficient left right
    horder hbasis houtside]
  ring

/-- A ReLU hinge at the midpoint of an interval cannot be uniformly
approximated too well by an affine combination of ReLUs whose thresholds all
avoid that interval.  The conclusion is independent of all coefficient
bounds and still holds with a free affine intercept. -/
theorem affineReLU_midpoint_error_lower
    {n : ℕ} (intercept : ℝ) (basis : Fin n → UnitIntervalPoint → ℝ)
    (coefficient : Fin n → ℝ) (left right : UnitIntervalPoint)
    (hstrict : left.1 < right.1)
    (hbasis : ∀ index, basis index ∈ unitIntervalReLUClass)
    (houtside : ∀ index threshold, basis index = unitIntervalReLU threshold →
      threshold.1 ≤ left.1 ∨ right.1 ≤ threshold.1)
    (epsilon : ℝ)
    (happrox : ∀ point,
      |unitIntervalReLU (unitIntervalMidpoint left right) point -
        (intercept + finiteLinearCombination coefficient basis point)| ≤ epsilon) :
    right.1 - left.1 ≤ 8 * epsilon := by
  let middle := unitIntervalMidpoint left right
  let approximation : UnitIntervalPoint → ℝ :=
    fun point => intercept + finiteLinearCombination coefficient basis point
  have hmean : approximation middle = (approximation left + approximation right) / 2 := by
    dsimp [approximation, middle]
    exact affineFiniteLinearCombination_midpoint_eq_average_of_outside
      intercept basis coefficient left right (le_of_lt hstrict) hbasis houtside
  have htargetLeft : unitIntervalReLU middle left = 0 := by
    unfold unitIntervalReLU
    rw [max_eq_left]
    dsimp [middle, unitIntervalMidpoint]
    linarith
  have htargetMiddle : unitIntervalReLU middle middle = 0 := by
    simp [unitIntervalReLU]
  have htargetRight : unitIntervalReLU middle right = (right.1 - left.1) / 2 := by
    unfold unitIntervalReLU
    rw [max_eq_right]
    · dsimp [middle, unitIntervalMidpoint]
      ring
    · dsimp [middle, unitIntervalMidpoint]
      linarith
  have hleftError := happrox left
  have hmiddleError := happrox middle
  have hrightError := happrox right
  rw [htargetLeft] at hleftError
  rw [htargetMiddle] at hmiddleError
  rw [htargetRight] at hrightError
  change |0 - approximation left| ≤ epsilon at hleftError
  change |0 - approximation middle| ≤ epsilon at hmiddleError
  change |(right.1 - left.1) / 2 - approximation right| ≤ epsilon at hrightError
  rcases abs_le.mp hleftError with ⟨hleftLower, hleftUpper⟩
  rcases abs_le.mp hmiddleError with ⟨hmiddleLower, hmiddleUpper⟩
  rcases abs_le.mp hrightError with ⟨hrightLower, hrightUpper⟩
  linarith

/-- The right endpoint of the probability-report interval. -/
def unitIntervalOne : UnitIntervalPoint := ⟨1, by constructor <;> norm_num⟩

/-- Unit-interval ReLU coordinates have distinct thresholds. -/
theorem unitIntervalReLU_injective : Function.Injective unitIntervalReLU := by
  intro threshold other heq
  have honeThreshold : unitIntervalReLU threshold unitIntervalOne = 1 - threshold.1 := by
    unfold unitIntervalReLU unitIntervalOne
    rw [max_eq_right (by linarith [threshold.2.2])]
  have honeOther : unitIntervalReLU other unitIntervalOne = 1 - other.1 := by
    unfold unitIntervalReLU unitIntervalOne
    rw [max_eq_right (by linarith [other.2.2])]
  have hvalue := congrFun heq unitIntervalOne
  rw [honeThreshold, honeOther] at hvalue
  apply Subtype.ext
  linarith

private noncomputable def finiteReLULowerGridLeft
    (count : ℕ) (index : Fin (count + 1)) : UnitIntervalPoint :=
  uniformGridPoint (count + 1) (Nat.succ_pos count) index.castSucc

private noncomputable def finiteReLULowerGridRight
    (count : ℕ) (index : Fin (count + 1)) : UnitIntervalPoint :=
  uniformGridPoint (count + 1) (Nat.succ_pos count) index.succ

private theorem finiteReLULowerGridLeft_lt_right
    (count : ℕ) (index : Fin (count + 1)) :
    (finiteReLULowerGridLeft count index).1 <
      (finiteReLULowerGridRight count index).1 := by
  unfold finiteReLULowerGridLeft finiteReLULowerGridRight uniformGridPoint
  dsimp
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  push_cast
  nlinarith

private theorem finiteReLULowerGrid_width
    (count : ℕ) (index : Fin (count + 1)) :
    (finiteReLULowerGridRight count index).1 -
        (finiteReLULowerGridLeft count index).1 =
      1 / ((count + 1 : ℕ) : ℝ) := by
  unfold finiteReLULowerGridLeft finiteReLULowerGridRight uniformGridPoint
  dsimp
  have hnonzero : ((count + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- A finite affine basis whose listed coordinates are only ReLU hinges has
linear, rather than sublinear, inverse-error cardinality.  More precisely,
if it uniformly approximates every possible ReLU hinge with error
`epsilon`—even with unrestricted coefficients and a free intercept—then it
has at least the resolution required by `1 / (n + 1) ≤ 8 * epsilon`.

This rules out a `\widetilde O(epsilon⁻²ᐟ³)` *ReLU-only* basis.  The
near-optimal convex approximate-rank construction must use additional
multiscale coordinates. -/
theorem finiteAffineReLUBasis_card_lower
    {n : ℕ} (basis : Fin n → UnitIntervalPoint → ℝ)
    (hbasis : ∀ index, basis index ∈ unitIntervalReLUClass)
    (epsilon : ℝ)
    (happrox : ∀ target : UnitIntervalPoint,
      ∃ (intercept : ℝ) (coefficient : Fin n → ℝ),
      ∀ point, |unitIntervalReLU target point -
        (intercept + finiteLinearCombination coefficient basis point)| ≤ epsilon) :
    1 / ((n + 1 : ℕ) : ℝ) ≤ 8 * epsilon := by
  classical
  choose threshold hthreshold using hbasis
  have hchosenBasis : ∀ index, basis index ∈ unitIntervalReLUClass := by
    intro index
    exact ⟨threshold index, hthreshold index⟩
  by_contra hbound
  have hsmall : 8 * epsilon < 1 / ((n + 1 : ℕ) : ℝ) := lt_of_not_ge hbound
  have hinterior : ∀ index : Fin (n + 1), ∃ coordinate : Fin n,
      (finiteReLULowerGridLeft n index).1 < (threshold coordinate).1 ∧
        (threshold coordinate).1 < (finiteReLULowerGridRight n index).1 := by
    intro index
    by_contra hmissing
    push Not at hmissing
    rcases happrox (unitIntervalMidpoint
      (finiteReLULowerGridLeft n index) (finiteReLULowerGridRight n index)) with
      ⟨intercept, coefficient, hrepresentation⟩
    have houtside : ∀ coordinate sourceThreshold,
        basis coordinate = unitIntervalReLU sourceThreshold →
          sourceThreshold.1 ≤ (finiteReLULowerGridLeft n index).1 ∨
            (finiteReLULowerGridRight n index).1 ≤ sourceThreshold.1 := by
      intro coordinate sourceThreshold hsource
      have hsame : threshold coordinate = sourceThreshold :=
        unitIntervalReLU_injective ((hthreshold coordinate).trans hsource)
      subst sourceThreshold
      by_cases hleft : (threshold coordinate).1 ≤ (finiteReLULowerGridLeft n index).1
      · exact Or.inl hleft
      · exact Or.inr (hmissing coordinate (lt_of_not_ge hleft))
    have hgap := affineReLU_midpoint_error_lower intercept basis coefficient
      (finiteReLULowerGridLeft n index) (finiteReLULowerGridRight n index)
      (finiteReLULowerGridLeft_lt_right n index) hchosenBasis houtside epsilon hrepresentation
    rw [finiteReLULowerGrid_width n index] at hgap
    linarith
  choose witness hwitness using hinterior
  have hinjective : Function.Injective witness := by
    intro first second hequal
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hfirst | hsecond
    · have hsuccessor : first.1 + 1 ≤ second.1 := by omega
      have hseparation : (finiteReLULowerGridRight n first).1 ≤
          (finiteReLULowerGridLeft n second).1 := by
        unfold finiteReLULowerGridLeft finiteReLULowerGridRight uniformGridPoint
        dsimp
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        push_cast
        have hsuccessorReal : (first.1 : ℝ) + 1 ≤ (second.1 : ℝ) := by
          exact_mod_cast hsuccessor
        nlinarith
      have hfirstWitness := hwitness first
      have hsecondWitness := hwitness second
      rw [← hequal] at hsecondWitness
      linarith
    · have hsuccessor : second.1 + 1 ≤ first.1 := by omega
      have hseparation : (finiteReLULowerGridRight n second).1 ≤
          (finiteReLULowerGridLeft n first).1 := by
        unfold finiteReLULowerGridLeft finiteReLULowerGridRight uniformGridPoint
        dsimp
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        push_cast
        have hsuccessorReal : (second.1 : ℝ) + 1 ≤ (first.1 : ℝ) := by
          exact_mod_cast hsuccessor
        nlinarith
      have hfirstWitness := hwitness first
      have hsecondWitness := hwitness second
      rw [← hequal] at hsecondWitness
      linarith
  have hcard := Fintype.card_le_of_injective witness hinjective
  simp only [Fintype.card_fin] at hcard
  omega

/-- Bounded convex one-Lipschitz functions on the unit interval, represented
as restrictions of real functions so convexity has its standard affine-domain
meaning. -/
def unitIntervalBoundedConvexOneLipschitzClass : Set (UnitIntervalPoint → ℝ) :=
  { target | ∃ function : ℝ → ℝ,
      target = (fun point => function point.1) ∧
        (∀ point ∈ Set.Icc (0 : ℝ) 1, |function point| ≤ 1) ∧
        ConvexOn ℝ (Set.Icc (0 : ℝ) 1) function ∧
        LipschitzOnWith 1 function (Set.Icc (0 : ℝ) 1) }

/-- Source-style convex one-Lipschitz functions on the unit interval.  The
affine approximation interface keeps the value at zero free, exactly as the
cited approximate-basis definition does. -/
def unitIntervalConvexOneLipschitzClass : Set (UnitIntervalPoint → ℝ) :=
  { target | ∃ function : ℝ → ℝ,
      target = (fun point => function point.1) ∧
        ConvexOn ℝ (Set.Icc (0 : ℝ) 1) function ∧
        LipschitzOnWith 1 function (Set.Icc (0 : ℝ) 1) }

/-- Lift a bounded coordinate family on a finite uniform grid to a
piecewise-constant coordinate family on the unit interval by rounding reports
down to their grid cell. -/
noncomputable def finiteGridFloorLift
    {count dimension : ℕ} (hcount : 0 < count)
    (basis : Fin dimension → Fin (count + 1) → ℝ) :
    Fin dimension → UnitIntervalPoint → ℝ :=
  fun coordinate point => basis coordinate (uniformGridFloor count point)

/-- Floor lifting preserves the coordinate range. -/
theorem abs_finiteGridFloorLift_le_one
    {count dimension : ℕ} (hcount : 0 < count)
    (basis : Fin dimension → Fin (count + 1) → ℝ)
    (hbounded : ∀ coordinate point, |basis coordinate point| ≤ 1)
    (coordinate : Fin dimension) (point : UnitIntervalPoint) :
    |finiteGridFloorLift hcount basis coordinate point| ≤ 1 := by
  exact hbounded coordinate (uniformGridFloor count point)

/-- A linear combination of floor-lifted coordinates evaluates exactly as its
finite-grid counterpart at the rounded grid index. -/
theorem finiteLinearCombination_finiteGridFloorLift
    {count dimension : ℕ} (hcount : 0 < count)
    (basis : Fin dimension → Fin (count + 1) → ℝ)
    (coefficient : Fin dimension → ℝ) (point : UnitIntervalPoint) :
    finiteLinearCombination coefficient (finiteGridFloorLift hcount basis) point =
      finiteLinearCombination coefficient basis (uniformGridFloor count point) := by
  rfl

/-- A common affine approximation of the uniform-grid samples of convex
one-Lipschitz functions lifts to the unit interval with exactly one additional
grid width of error.  The lifted coordinates need not themselves be ReLUs;
the statement is for the source's unrestricted approximate-basis notion. -/
theorem isFixedFiniteAffineUniformApproximateBasis_unitIntervalConvexOneLipschitzClass_of_grid
    {count dimension : ℕ} (hcount : 0 < count)
    (basis : Fin dimension → Fin (count + 1) → ℝ) (epsilon : ℝ)
    (happrox : IsFixedFiniteAffineUniformApproximateBasis
      (finiteGridConvexUnitSlopeFreeInterceptClass count) basis epsilon) :
    IsFixedFiniteAffineUniformApproximateBasis
      unitIntervalConvexOneLipschitzClass (finiteGridFloorLift hcount basis)
      (epsilon + 1 / (count : ℝ)) := by
  rcases happrox with ⟨hbounded, hspan⟩
  refine ⟨fun coordinate point =>
    abs_finiteGridFloorLift_le_one hcount basis hbounded coordinate point, ?_⟩
  rintro target ⟨function, rfl, hconvex, hLipschitz⟩
  let values : Fin (count + 1) → ℝ :=
    fun index => uniformGridSample function count index.1
  have hvalues : values ∈ finiteGridConvexUnitSlopeFreeInterceptClass count := by
    exact uniformGridSample_mem_finiteGridConvexUnitSlopeFreeInterceptClass_of_convex_lipschitz
      function count hcount hconvex hLipschitz
  rcases hspan values hvalues with ⟨intercept, coefficient, hgridError⟩
  refine ⟨intercept, coefficient, ?_⟩
  intro point
  let index := uniformGridFloor count point
  let rounded := uniformGridPoint count hcount index
  have hrounding : |point.1 - rounded.1| ≤ 1 / (count : ℝ) := by
    simpa [rounded, index] using
      (abs_sub_uniformGridPoint_floor_le_inverse count hcount point)
  have hfunctionRound : |function point.1 - function rounded.1| ≤ 1 / (count : ℝ) := by
    have hdistance := hLipschitz.dist_le_mul point.1 point.2 rounded.1 rounded.2
    calc
      |function point.1 - function rounded.1| =
          dist (function point.1) (function rounded.1) := by
            rw [Real.dist_eq, abs_sub_comm]
      _ ≤ 1 * dist point.1 rounded.1 := by simpa using hdistance
      _ = |point.1 - rounded.1| := by rw [Real.dist_eq, one_mul]
      _ ≤ 1 / (count : ℝ) := hrounding
  have hgridErrorAt :
      |function rounded.1 -
        (intercept + finiteLinearCombination coefficient
          (finiteGridFloorLift hcount basis) point)| ≤ epsilon := by
    rw [finiteLinearCombination_finiteGridFloorLift]
    simpa [values, rounded, index, uniformGridSample, uniformGridPoint] using hgridError index
  calc
    |function point.1 -
        (intercept + finiteLinearCombination coefficient
          (finiteGridFloorLift hcount basis) point)| ≤
        |function point.1 - function rounded.1| +
          |function rounded.1 -
            (intercept + finiteLinearCombination coefficient
              (finiteGridFloorLift hcount basis) point)| :=
      abs_sub_le _ _ _
    _ ≤ 1 / (count : ℝ) + epsilon := add_le_add hfunctionRound hgridErrorAt
    _ = epsilon + 1 / (count : ℝ) := by ring

/-- Each outcome coordinate of a bounded, convex, one-Lipschitz binary loss
belongs to the scalar class used by the direct ReLU construction. -/
theorem unitIntervalLossCoordinate_mem_unitIntervalBoundedConvexOneLipschitzClass
    (loss : BinaryLoss) (hbounded : IsUnitBoundedBinaryLoss loss)
    (hconvex : IsUnitIntervalConvexBinaryLoss loss)
    (hLipschitz : IsUnitIntervalLipschitzBinaryLoss loss) (outcome : Bool) :
    (fun point : UnitIntervalPoint => loss point.1 outcome) ∈
      unitIntervalBoundedConvexOneLipschitzClass := by
  refine ⟨fun report => loss report outcome, rfl, ?_, hconvex outcome, ?_⟩
  · intro point hpoint
    rcases hbounded hpoint outcome with ⟨hlower, hupper⟩
    exact abs_le.mpr ⟨by linarith, hupper⟩
  · intro point hpoint other hother
    simpa only using
      (LipschitzWith.edist_le_mul (hLipschitz outcome)
        ⟨point, hpoint⟩ ⟨other, hother⟩)

/-- Taking the difference of the two outcome coordinates realizes every
discrete derivative as a member of the convex-loss difference class. -/
theorem unitIntervalDiscreteDerivativeClass_subset_functionDifferenceClass
    (losses : Set BinaryLoss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (hconvex : ∀ loss ∈ losses, IsUnitIntervalConvexBinaryLoss loss)
    (hLipschitz : ∀ loss ∈ losses, IsUnitIntervalLipschitzBinaryLoss loss) :
    unitIntervalDiscreteDerivativeClass losses ⊆
      functionDifferenceClass unitIntervalBoundedConvexOneLipschitzClass := by
  rintro derivative ⟨loss, hloss, rfl⟩
  refine ⟨fun point => loss point.1 true, ?_, fun point => loss point.1 false, ?_, ?_⟩
  · exact unitIntervalLossCoordinate_mem_unitIntervalBoundedConvexOneLipschitzClass
      loss (hbounded loss hloss) (hconvex loss hloss) (hLipschitz loss hloss) true
  · exact unitIntervalLossCoordinate_mem_unitIntervalBoundedConvexOneLipschitzClass
      loss (hbounded loss hloss) (hconvex loss hloss) (hLipschitz loss hloss) false
  · rfl

/-- A direct uniform-grid construction gives an affine ReLU basis for bounded
convex one-Lipschitz functions.  Its size is linear in the reciprocal error;
the sharper approximate-rank construction is a separate result. -/
theorem finiteNormalizedReLUDuplicatedUnitInterval_isFixedFiniteAffineApproximateBasis
    (count : ℕ) (hcount : 0 < count) :
    IsFixedFiniteAffineApproximateBasis unitIntervalBoundedConvexOneLipschitzClass
      (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount)
      (4 / (count : ℝ)) 1 3 := by
  intro target htarget
  rcases htarget with ⟨function, htarget, hbounded, hconvex, hLipschitz⟩
  subst target
  let values : Fin (count + 1) → ℝ :=
    fun point => uniformGridSample function count point.1
  have hzero : |function 0| ≤ 1 := hbounded 0 (by norm_num)
  have hvalues : values ∈ finiteGridConvexUnitSlopeClass count := by
    exact uniformGridSample_mem_finiteGridConvexUnitSlopeClass_of_convex_lipschitz
      function count hcount hzero hconvex hLipschitz
  have hgrid := finiteNormalizedReLUDuplicated_isFixedFiniteAffineApproximateBasis
    count hcount values hvalues
  rcases hgrid with ⟨intercept, coefficient, hintercept, hcoefficient, hnorm, herror⟩
  refine ⟨intercept, coefficient, hintercept, hcoefficient, hnorm, ?_⟩
  intro point
  let index := uniformGridFloor count point
  let rounded := uniformGridPoint count hcount index
  have hrounding : |point.1 - rounded.1| ≤ 1 / (count : ℝ) := by
    simpa [rounded, index] using
      (abs_sub_uniformGridPoint_floor_le_inverse count hcount point)
  have hfunctionRound : |function point.1 - function rounded.1| ≤ 1 / (count : ℝ) := by
    have hdistance := LipschitzOnWith.dist_le_mul hLipschitz point.1 point.2 rounded.1 rounded.2
    calc
      |function point.1 - function rounded.1| = dist (function point.1) (function rounded.1) := by
        rw [Real.dist_eq, abs_sub_comm]
      _ ≤ 1 * dist point.1 rounded.1 := by simpa using hdistance
      _ = |point.1 - rounded.1| := by rw [Real.dist_eq, one_mul]
      _ ≤ 1 / (count : ℝ) := hrounding
  have hgridDiscrete : values index = intercept +
      finiteLinearCombination coefficient (finiteNormalizedReLUDuplicatedBasis count) index := by
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    exact le_antisymm (herror index) (abs_nonneg _)
  have hgridExact : function rounded.1 = intercept +
      finiteLinearCombination coefficient
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded := by
    calc
      function rounded.1 = values index := by
        simp [values, rounded, index, uniformGridSample, uniformGridPoint]
      _ = intercept + finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedBasis count) index := hgridDiscrete
      _ = intercept + finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded := by
        rw [finiteLinearCombination_liftedReLUBasis_apply_uniformGridPoint]
  have hcombinationRound :
      |finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point -
        finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded| ≤
        3 / (count : ℝ) := by
    calc
      |finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point -
        finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded| ≤
        (∑ coordinate, |coefficient coordinate|) * |point.1 - rounded.1| :=
          finiteLinearCombination_liftedReLUBasis_abs_sub_le count hcount coefficient point rounded
      _ ≤ 3 * (1 / (count : ℝ)) := by
        exact mul_le_mul hnorm hrounding (abs_nonneg _) (by norm_num)
      _ = 3 / (count : ℝ) := by ring
  calc
    |function point.1 - (intercept + finiteLinearCombination coefficient
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point)| =
      |(function point.1 - function rounded.1) +
        (finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded -
          finiteLinearCombination coefficient
            (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point)| := by
        rw [hgridExact]
        congr 1
        ring
    _ ≤ |function point.1 - function rounded.1| +
        |finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded -
          finiteLinearCombination coefficient
            (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point| :=
      abs_add_le _ _
    _ = |function point.1 - function rounded.1| +
        |finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point -
          finiteLinearCombination coefficient
            (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded| := by
      rw [show |finiteLinearCombination coefficient
          (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded -
          finiteLinearCombination coefficient
            (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point| =
          |finiteLinearCombination coefficient
            (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) point -
            finiteLinearCombination coefficient
              (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount) rounded| by
          exact abs_sub_comm _ _]
    _ ≤ 1 / (count : ℝ) + 3 / (count : ℝ) :=
      add_le_add hfunctionRound hcombinationRound
    _ = 4 / (count : ℝ) := by ring

/-- The difference class has an affine ReLU basis with doubled intercept and
nonconstant coefficient norms.  The two tagged copies preserve the individual
coefficient bound, while proper calibration can control the larger intercept. -/
theorem finiteNormalizedReLUDuplicatedUnitInterval_functionDifference_isFixedFiniteAffineApproximateBasis
    (count : ℕ) (hcount : 0 < count) :
    IsFixedFiniteAffineApproximateBasis
      (functionDifferenceClass unitIntervalBoundedConvexOneLipschitzClass)
      (Fin.addCases (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount)
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount))
      (8 / (count : ℝ)) 2 6 := by
  have hresult :=
    functionDifferenceClass_isFixedFiniteAffineApproximateBasis_of_commonCoordinates
      unitIntervalBoundedConvexOneLipschitzClass
      (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount)
      (4 / (count : ℝ)) 1 3
      (finiteNormalizedReLUDuplicatedUnitInterval_isFixedFiniteAffineApproximateBasis count hcount)
  convert hresult using 1 <;> ring

/-- Two tagged copies of the direct affine ReLU basis approximate differences
of bounded convex one-Lipschitz functions.  The constant coordinate is
explicit because a homogeneous ReLU span cannot represent it. -/
theorem finiteNormalizedReLUDuplicatedUnitInterval_functionDifference_isFiniteApproximateBasis
    (count : ℕ) (hcount : 0 < count) :
    IsFiniteApproximateBasis
      (functionDifferenceClass unitIntervalBoundedConvexOneLipschitzClass)
      (Set.range (Fin.cons (fun _ : UnitIntervalPoint => 1)
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount)))
      (8 / (count : ℝ))
      ((((count + count) + 1) + 1) + (((count + count) + 1) + 1)) 8 := by
  have haffine := finiteNormalizedReLUDuplicatedUnitInterval_isFixedFiniteAffineApproximateBasis
    count hcount
  have hhomogeneous : IsFixedFiniteApproximateBasis unitIntervalBoundedConvexOneLipschitzClass
      (Fin.cons (fun _ : UnitIntervalPoint => 1)
        (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount))
      (4 / (count : ℝ)) 4 := by
    convert isFixedFiniteApproximateBasis_of_affine unitIntervalBoundedConvexOneLipschitzClass
      (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount)
      (4 / (count : ℝ)) 1 3 (by norm_num) haffine using 1 <;> ring
  have hdifference := functionDifferenceClass_isFiniteApproximateBasis_of_commonCoordinates
    unitIntervalBoundedConvexOneLipschitzClass
    (Fin.cons (fun _ : UnitIntervalPoint => 1)
      (finiteNormalizedReLUDuplicatedUnitIntervalBasis count hcount))
    (4 / (count : ℝ)) 4 hhomogeneous
  convert hdifference using 1 <;> ring

end AppliedModelingLib.Learning.Prediction
