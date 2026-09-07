/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
Authors: Daniel Lyng

This file adapts the finite-coupling-polytope development from
https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Optimization/OptimalTransport/DualityFinite.lean
to AppliedModelingLib's finite-PMF transport setting.  The upstream revision is
Apache-2.0.  The adaptation generalizes the two finite index types and keeps
only the compactness/convexity primitives required for constrained robust
optimization; no upstream repository is imported as a dependency.
-/

import AppliedModelingLib.Foundations.Probability.FiniteTransport
import AppliedModelingLib.Foundations.Optimization.ScalarStrongDuality
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-!
# Finite real transport matrices

A finite coupling may be viewed as a nonnegative real matrix whose row and
column sums are its two marginals.  This module gives a compact convex
polytope for such matrices and the continuous linear objectives used by
transport and finite distributionally robust optimization.

## External formalization credit

The compact-polytope construction is a Lean/Mathlib 4.30 compatibility
adaptation of Daniel Lyng's Apache-2.0 Econlib source
[`Econlib/Optimization/OptimalTransport/DualityFinite.lean`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Optimization/OptimalTransport/DualityFinite.lean),
revision
[`003655ccf010cdf44c4f67d6675167b54ce0e9df`](https://github.com/danlyng/Econlib/commit/003655ccf010cdf44c4f67d6675167b54ce0e9df),
especially lines 60--142. Econlib is Apache-2.0 licensed.  The original
copyright notice and this modification notice are retained; the checked
upstream span contains no `sorry` or additional axioms.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteTransportMatrix

variable {Source Target : Type*}
variable [Fintype Source] [DecidableEq Source] [Fintype Target] [DecidableEq Target]

/-- Nonnegative real coupling matrices with prescribed row and column masses. -/
def couplingMatrices (source : Source → ℝ) (target : Target → ℝ) :
    Set (Matrix Source Target ℝ) :=
  {matrix | (∀ first second, 0 ≤ matrix first second)
      ∧ (∀ first, ∑ second, matrix first second = source first)
      ∧ (∀ second, ∑ first, matrix first second = target second)}

/-- The finite coupling-matrix polytope is closed. -/
theorem couplingMatrices_isClosed (source : Source → ℝ) (target : Target → ℝ) :
    IsClosed (couplingMatrices source target) := by
  change IsClosed {matrix : Matrix Source Target ℝ |
      (∀ first second, 0 ≤ matrix first second)
        ∧ (∀ first, ∑ second, matrix first second = source first)
        ∧ (∀ second, ∑ first, matrix first second = target second)}
  have hnonneg : IsClosed {matrix : Matrix Source Target ℝ |
      ∀ first second, 0 ≤ matrix first second} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun first =>
        isClosed_iInter (fun second =>
          isClosed_le continuous_const (continuous_apply_apply first second)))
  have hrow : IsClosed {matrix : Matrix Source Target ℝ |
      ∀ first, ∑ second, matrix first second = source first} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun first =>
        isClosed_eq
          (continuous_finset_sum _ fun second _ => continuous_apply_apply first second)
          continuous_const)
  have hcolumn : IsClosed {matrix : Matrix Source Target ℝ |
      ∀ second, ∑ first, matrix first second = target second} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun second =>
        isClosed_eq
          (continuous_finset_sum _ fun first _ => continuous_apply_apply first second)
          continuous_const)
  simpa [and_assoc] using hnonneg.inter (hrow.inter hcolumn)

/-- Every entry of a finite coupling matrix is bounded by a common row-mass bound. -/
theorem couplingMatrices_entry_bounded (source : Source → ℝ) (target : Target → ℝ) :
    ∃ bound : ℝ, ∀ matrix ∈ couplingMatrices source target, ∀ first second,
      |matrix first second| ≤ bound := by
  refine ⟨∑ first, |source first|, ?_⟩
  intro matrix hmatrix first second
  rcases hmatrix with ⟨hnonneg, hrow, _hcolumn⟩
  have hentry_le_row : matrix first second ≤ ∑ third, matrix first third :=
    Finset.single_le_sum (fun third _ => hnonneg first third) (Finset.mem_univ second)
  have hentry_le_source : matrix first second ≤ source first := by
    simpa [hrow first] using hentry_le_row
  have hsource_le_sum : |source first| ≤ ∑ third, |source third| :=
    Finset.single_le_sum (fun third _ => abs_nonneg (source third)) (Finset.mem_univ first)
  calc
    |matrix first second| = matrix first second := abs_of_nonneg (hnonneg first second)
    _ ≤ source first := hentry_le_source
    _ ≤ |source first| := le_abs_self (source first)
    _ ≤ ∑ third, |source third| := hsource_le_sum

/-- The finite coupling-matrix polytope is compact. -/
theorem couplingMatrices_isCompact (source : Source → ℝ) (target : Target → ℝ) :
    IsCompact (couplingMatrices source target) := by
  obtain ⟨bound, hbound⟩ := couplingMatrices_entry_bounded source target
  have hbox : IsCompact ((Set.Icc (-bound) bound).matrix :
      Set (Matrix Source Target ℝ)) :=
    (isCompact_Icc : IsCompact (Set.Icc (-bound) bound)).matrix
  exact hbox.of_isClosed_subset (couplingMatrices_isClosed source target) (by
    intro matrix hmatrix
    rw [Set.mem_matrix]
    intro first second
    exact abs_le.mp (hbound matrix hmatrix first second))

/-- Product weights are a coupling matrix for probability vectors. -/
theorem couplingMatrices_nonempty (source : Source → ℝ) (target : Target → ℝ)
    (hsource_nonneg : ∀ first, 0 ≤ source first) (hsource_sum : ∑ first, source first = 1)
    (htarget_nonneg : ∀ second, 0 ≤ target second) (htarget_sum : ∑ second, target second = 1) :
    (couplingMatrices source target).Nonempty := by
  refine ⟨fun first second => source first * target second, ?_⟩
  constructor
  · intro first second
    exact mul_nonneg (hsource_nonneg first) (htarget_nonneg second)
  constructor
  · intro first
    calc
      ∑ second, source first * target second = source first * ∑ second, target second := by
        rw [Finset.mul_sum]
      _ = source first := by rw [htarget_sum, mul_one]
  · intro second
    calc
      ∑ first, source first * target second = (∑ first, source first) * target second := by
        rw [Finset.sum_mul]
      _ = target second := by rw [hsource_sum, one_mul]

/-- Nonnegative real kernel matrices with a prescribed nominal (column) marginal. -/
def kernelMatrices (target : Target → ℝ) : Set (Matrix Source Target ℝ) :=
  {matrix | (∀ first second, 0 ≤ matrix first second) ∧
    ∀ second, ∑ first, matrix first second = target second}

/-- The fixed-nominal finite kernel polytope is closed. -/
theorem kernelMatrices_isClosed (target : Target → ℝ) :
    IsClosed (kernelMatrices (Source := Source) target) := by
  change IsClosed {matrix : Matrix Source Target ℝ |
      (∀ first second, 0 ≤ matrix first second) ∧
        ∀ second, ∑ first, matrix first second = target second}
  have hnonneg : IsClosed {matrix : Matrix Source Target ℝ |
      ∀ first second, 0 ≤ matrix first second} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun first =>
        isClosed_iInter (fun second =>
          isClosed_le continuous_const (continuous_apply_apply first second)))
  have hcolumn : IsClosed {matrix : Matrix Source Target ℝ |
      ∀ second, ∑ first, matrix first second = target second} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun second =>
        isClosed_eq
          (continuous_finset_sum _ fun first _ => continuous_apply_apply first second)
          continuous_const)
  exact hnonneg.inter hcolumn

/-- Every entry of a finite kernel matrix is bounded by a common nominal-mass bound. -/
theorem kernelMatrices_entry_bounded (target : Target → ℝ) :
    ∃ bound : ℝ, ∀ matrix ∈ kernelMatrices (Source := Source) target, ∀ first second,
      |matrix first second| ≤ bound := by
  refine ⟨∑ second, |target second|, ?_⟩
  intro matrix hmatrix first second
  rcases hmatrix with ⟨hnonneg, hcolumn⟩
  have hentry_le_column : matrix first second ≤ ∑ third, matrix third second :=
    Finset.single_le_sum (fun third _ => hnonneg third second) (Finset.mem_univ first)
  have hentry_le_target : matrix first second ≤ target second := by
    simpa [hcolumn second] using hentry_le_column
  have htarget_le_sum : |target second| ≤ ∑ third, |target third| :=
    Finset.single_le_sum (fun third _ => abs_nonneg (target third)) (Finset.mem_univ second)
  calc
    |matrix first second| = matrix first second := abs_of_nonneg (hnonneg first second)
    _ ≤ target second := hentry_le_target
    _ ≤ |target second| := le_abs_self (target second)
    _ ≤ ∑ third, |target third| := htarget_le_sum

/-- The fixed-nominal finite kernel polytope is compact. -/
theorem kernelMatrices_isCompact (target : Target → ℝ) :
    IsCompact (kernelMatrices (Source := Source) target) := by
  obtain ⟨bound, hbound⟩ := kernelMatrices_entry_bounded (Source := Source) target
  have hbox : IsCompact ((Set.Icc (-bound) bound).matrix :
      Set (Matrix Source Target ℝ)) :=
    (isCompact_Icc : IsCompact (Set.Icc (-bound) bound)).matrix
  exact hbox.of_isClosed_subset (kernelMatrices_isClosed (Source := Source) target) (by
    intro matrix hmatrix
    rw [Set.mem_matrix]
    intro first second
    exact abs_le.mp (hbound matrix hmatrix first second))

/-- A fixed-nominal finite kernel polytope is convex. -/
theorem kernelMatrices_convex (target : Target → ℝ) :
    Convex ℝ (kernelMatrices (Source := Source) target) := by
  intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
  rcases hfirst with ⟨hfirst_nonneg, hfirst_column⟩
  rcases hsecond with ⟨hsecond_nonneg, hsecond_column⟩
  refine ⟨?_, ?_⟩
  · intro sourceIndex targetIndex
    change 0 ≤ weightFirst * first sourceIndex targetIndex +
      weightSecond * second sourceIndex targetIndex
    exact add_nonneg
      (mul_nonneg hweightFirst (hfirst_nonneg sourceIndex targetIndex))
      (mul_nonneg hweightSecond (hsecond_nonneg sourceIndex targetIndex))
  · intro targetIndex
    change (∑ sourceIndex : Source,
      (weightFirst * first sourceIndex targetIndex + weightSecond * second sourceIndex targetIndex)) =
        target targetIndex
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hfirst_column targetIndex, hsecond_column targetIndex]
    calc
      weightFirst * target targetIndex + weightSecond * target targetIndex =
          (weightFirst + weightSecond) * target targetIndex := by ring
      _ = target targetIndex := by rw [hweights, one_mul]

/-- Finite coupling matrices form a convex polytope. -/
theorem couplingMatrices_convex (source : Source → ℝ) (target : Target → ℝ) :
    Convex ℝ (couplingMatrices source target) := by
  intro first hfirst second hsecond weightFirst weightSecond hweightFirst hweightSecond hweights
  rcases hfirst with ⟨hfirst_nonneg, hfirst_row, hfirst_column⟩
  rcases hsecond with ⟨hsecond_nonneg, hsecond_row, hsecond_column⟩
  refine ⟨?_, ?_, ?_⟩
  · intro sourceIndex targetIndex
    change 0 ≤ weightFirst * first sourceIndex targetIndex +
      weightSecond * second sourceIndex targetIndex
    exact add_nonneg
      (mul_nonneg hweightFirst (hfirst_nonneg sourceIndex targetIndex))
      (mul_nonneg hweightSecond (hsecond_nonneg sourceIndex targetIndex))
  · intro sourceIndex
    change (∑ targetIndex : Target,
      (weightFirst * first sourceIndex targetIndex + weightSecond * second sourceIndex targetIndex)) =
        source sourceIndex
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hfirst_row sourceIndex, hsecond_row sourceIndex]
    calc
      weightFirst * source sourceIndex + weightSecond * source sourceIndex =
          (weightFirst + weightSecond) * source sourceIndex := by ring
      _ = source sourceIndex := by rw [hweights, one_mul]
  · intro targetIndex
    change (∑ sourceIndex : Source,
      (weightFirst * first sourceIndex targetIndex + weightSecond * second sourceIndex targetIndex)) =
        target targetIndex
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hfirst_column targetIndex, hsecond_column targetIndex]
    calc
      weightFirst * target targetIndex + weightSecond * target targetIndex =
          (weightFirst + weightSecond) * target targetIndex := by ring
      _ = target targetIndex := by rw [hweights, one_mul]

/-- The finite matrix expectation of a payoff under real coupling weights. -/
def matrixExpectation (matrix : Matrix Source Target ℝ) (payoff : Source → Target → ℝ) : ℝ :=
  ∑ sourceIndex, ∑ targetIndex, matrix sourceIndex targetIndex * payoff sourceIndex targetIndex

/-- A finite matrix-expectation functional is continuous. -/
theorem continuous_matrixExpectation (payoff : Source → Target → ℝ) :
    Continuous (fun matrix : Matrix Source Target ℝ => matrixExpectation matrix payoff) := by
  unfold matrixExpectation
  apply continuous_finset_sum _ fun sourceIndex _ => ?_
  apply continuous_finset_sum _ fun targetIndex _ => ?_
  exact (continuous_apply_apply sourceIndex targetIndex).mul continuous_const

/-- Matrix expectation respects affine combinations of coupling matrices. -/
theorem matrixExpectation_combo (first second : Matrix Source Target ℝ)
    (weightFirst weightSecond : ℝ) (payoff : Source → Target → ℝ) :
    matrixExpectation (weightFirst • first + weightSecond • second) payoff =
      weightFirst * matrixExpectation first payoff +
        weightSecond * matrixExpectation second payoff := by
  unfold matrixExpectation
  change (∑ sourceIndex, ∑ targetIndex,
    (weightFirst * first sourceIndex targetIndex + weightSecond * second sourceIndex targetIndex) *
      payoff sourceIndex targetIndex) = _
  calc
    ∑ sourceIndex, ∑ targetIndex,
        (weightFirst * first sourceIndex targetIndex + weightSecond * second sourceIndex targetIndex) *
          payoff sourceIndex targetIndex =
      ∑ sourceIndex, ∑ targetIndex,
        (weightFirst * first sourceIndex targetIndex * payoff sourceIndex targetIndex +
          weightSecond * second sourceIndex targetIndex * payoff sourceIndex targetIndex) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        apply Finset.sum_congr rfl
        intro targetIndex _
        ring
    _ = ∑ sourceIndex,
        (weightFirst * ∑ targetIndex, first sourceIndex targetIndex * payoff sourceIndex targetIndex +
          weightSecond * ∑ targetIndex, second sourceIndex targetIndex * payoff sourceIndex targetIndex) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        calc
          ∑ targetIndex,
              (weightFirst * first sourceIndex targetIndex * payoff sourceIndex targetIndex +
                weightSecond * second sourceIndex targetIndex * payoff sourceIndex targetIndex) =
            (∑ targetIndex,
              weightFirst * (first sourceIndex targetIndex * payoff sourceIndex targetIndex)) +
              ∑ targetIndex,
                weightSecond * (second sourceIndex targetIndex * payoff sourceIndex targetIndex) := by
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    apply Finset.sum_congr rfl <;>
                    intro targetIndex _ <;>
                    ring
          _ = weightFirst * ∑ targetIndex,
              first sourceIndex targetIndex * payoff sourceIndex targetIndex +
              weightSecond * ∑ targetIndex,
                second sourceIndex targetIndex * payoff sourceIndex targetIndex := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = weightFirst * ∑ sourceIndex, ∑ targetIndex,
          first sourceIndex targetIndex * payoff sourceIndex targetIndex +
        weightSecond * ∑ sourceIndex, ∑ targetIndex,
          second sourceIndex targetIndex * payoff sourceIndex targetIndex := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Matrix expectation distributes over a payoff minus a scalar multiple of another payoff. -/
theorem matrixExpectation_sub_mul (matrix : Matrix Source Target ℝ)
    (first second : Source → Target → ℝ) (multiplier : ℝ) :
    matrixExpectation matrix (fun sourceIndex targetIndex =>
      first sourceIndex targetIndex - multiplier * second sourceIndex targetIndex) =
      matrixExpectation matrix first - multiplier * matrixExpectation matrix second := by
  unfold matrixExpectation
  calc
    ∑ sourceIndex, ∑ targetIndex,
        matrix sourceIndex targetIndex *
          (first sourceIndex targetIndex - multiplier * second sourceIndex targetIndex) =
      ∑ sourceIndex, ∑ targetIndex,
        (matrix sourceIndex targetIndex * first sourceIndex targetIndex -
          multiplier * (matrix sourceIndex targetIndex * second sourceIndex targetIndex)) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        apply Finset.sum_congr rfl
        intro targetIndex _
        ring
    _ = ∑ sourceIndex,
        ((∑ targetIndex, matrix sourceIndex targetIndex * first sourceIndex targetIndex) -
          multiplier * ∑ targetIndex,
            matrix sourceIndex targetIndex * second sourceIndex targetIndex) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        rw [Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]
    _ = (∑ sourceIndex, ∑ targetIndex, matrix sourceIndex targetIndex * first sourceIndex targetIndex) -
        multiplier * ∑ sourceIndex, ∑ targetIndex,
          matrix sourceIndex targetIndex * second sourceIndex targetIndex := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Matrix expectation is convex on any convex set of real transport matrices. -/
theorem convexOn_matrixExpectation_of_convex (domain : Set (Matrix Source Target ℝ))
    (hdomain : Convex ℝ domain) (payoff : Source → Target → ℝ) :
    ConvexOn ℝ domain (fun matrix => matrixExpectation matrix payoff) := by
  refine ⟨hdomain, ?_⟩
  intro first _ second _ weightFirst weightSecond _ _ _
  change matrixExpectation (weightFirst • first + weightSecond • second) payoff ≤
    weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff
  rw [matrixExpectation_combo]

/-- Matrix expectation is concave on any convex set of real transport matrices. -/
theorem concaveOn_matrixExpectation_of_convex (domain : Set (Matrix Source Target ℝ))
    (hdomain : Convex ℝ domain) (payoff : Source → Target → ℝ) :
    ConcaveOn ℝ domain (fun matrix => matrixExpectation matrix payoff) := by
  refine ⟨hdomain, ?_⟩
  intro first _ second _ weightFirst weightSecond _ _ _
  change weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff ≤
    matrixExpectation (weightFirst • first + weightSecond • second) payoff
  rw [matrixExpectation_combo]

/-- A matrix expectation minus a constant is convex on any convex matrix domain. -/
theorem convexOn_matrixExpectation_sub_const_of_convex (domain : Set (Matrix Source Target ℝ))
    (hdomain : Convex ℝ domain) (payoff : Source → Target → ℝ) (constant : ℝ) :
    ConvexOn ℝ domain (fun matrix => matrixExpectation matrix payoff - constant) := by
  refine ⟨hdomain, ?_⟩
  intro first _ second _ weightFirst weightSecond _ _ hweights
  change matrixExpectation (weightFirst • first + weightSecond • second) payoff - constant ≤
    weightFirst * (matrixExpectation first payoff - constant) +
      weightSecond * (matrixExpectation second payoff - constant)
  rw [matrixExpectation_combo]
  calc
    weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff -
        constant =
      weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff -
        (weightFirst + weightSecond) * constant := by rw [hweights, one_mul]
    _ = weightFirst * (matrixExpectation first payoff - constant) +
        weightSecond * (matrixExpectation second payoff - constant) := by ring
    _ ≤ weightFirst * (matrixExpectation first payoff - constant) +
        weightSecond * (matrixExpectation second payoff - constant) := le_rfl

/-- A matrix expectation minus a constant is continuous. -/
theorem continuous_matrixExpectation_sub_const (payoff : Source → Target → ℝ) (constant : ℝ) :
    Continuous (fun matrix : Matrix Source Target ℝ => matrixExpectation matrix payoff - constant) :=
  (continuous_matrixExpectation payoff).sub continuous_const

/-- Real atom masses of the first marginal are the row sums of a finite joint PMF. -/
theorem pmfMapFst_toReal_eq_sum {Source Target : Type*}
    [Fintype Source] [DecidableEq Source] [Fintype Target] [DecidableEq Target]
    (law : PMF (Source × Target)) (first : Source) :
    (law.map Prod.fst first).toReal = ∑ second : Target, (law (first, second)).toReal := by
  have hmap : law.map Prod.fst first = ∑ second : Target, law (first, second) := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single first]
    · simp
    · intro sourceIndex _ hsourceIndex
      apply Finset.sum_eq_zero
      intro targetIndex _
      simp [Ne.symm hsourceIndex]
    · simp
  rw [hmap, ENNReal.toReal_sum]
  intro second _
  exact law.apply_ne_top _

/-- Real atom masses of the second marginal are the column sums of a finite joint PMF. -/
theorem pmfMapSnd_toReal_eq_sum {Source Target : Type*}
    [Fintype Source] [DecidableEq Source] [Fintype Target] [DecidableEq Target]
    (law : PMF (Source × Target)) (second : Target) :
    (law.map Prod.snd second).toReal = ∑ first : Source, (law (first, second)).toReal := by
  have hmap : law.map Prod.snd second = ∑ first : Source, law (first, second) := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
    rw [Finset.sum_eq_single second]
    · simp
    · intro targetIndex _ htargetIndex
      apply Finset.sum_eq_zero
      intro sourceIndex _
      simp [Ne.symm htargetIndex]
    · simp
  rw [hmap, ENNReal.toReal_sum]
  intro first _
  exact law.apply_ne_top _

/-- The real matrix of atom masses associated with a finite PMF coupling. -/
noncomputable def matrixOfFiniteCoupling
    {source : PMF Source} {target : PMF Target}
    (coupling : FiniteCoupling source target) : Matrix Source Target ℝ :=
  fun sourceIndex targetIndex => (coupling.law (sourceIndex, targetIndex)).toReal

/-- A finite PMF coupling gives a matrix in the fixed-nominal kernel polytope. -/
theorem matrixOfFiniteCoupling_mem_kernelMatrices
    {source : PMF Source} {target : PMF Target}
    (coupling : FiniteCoupling source target) :
    matrixOfFiniteCoupling coupling ∈
      kernelMatrices (Source := Source) (fun targetIndex => (target targetIndex).toReal) := by
  refine ⟨?_, ?_⟩
  · intro sourceIndex targetIndex
    exact ENNReal.toReal_nonneg
  · intro targetIndex
    unfold matrixOfFiniteCoupling
    rw [← pmfMapSnd_toReal_eq_sum coupling.law targetIndex, coupling.snd_marginal]

/-- A finite PMF coupling gives a matrix with both prescribed real marginals. -/
theorem matrixOfFiniteCoupling_mem_couplingMatrices
    {source : PMF Source} {target : PMF Target}
    (coupling : FiniteCoupling source target) :
    matrixOfFiniteCoupling coupling ∈
      couplingMatrices (fun sourceIndex => (source sourceIndex).toReal)
        (fun targetIndex => (target targetIndex).toReal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sourceIndex targetIndex
    exact ENNReal.toReal_nonneg
  · intro sourceIndex
    unfold matrixOfFiniteCoupling
    rw [← pmfMapFst_toReal_eq_sum coupling.law sourceIndex, coupling.fst_marginal]
  · intro targetIndex
    unfold matrixOfFiniteCoupling
    rw [← pmfMapSnd_toReal_eq_sum coupling.law targetIndex, coupling.snd_marginal]

/-- Matrix expectation of a finite coupling is its PMF expectation. -/
theorem matrixExpectation_matrixOfFiniteCoupling
    {source : PMF Source} {target : PMF Target}
    (coupling : FiniteCoupling source target) (payoff : Source → Target → ℝ) :
    matrixExpectation (matrixOfFiniteCoupling coupling) payoff =
      pmfExp coupling.law (fun pair => payoff pair.1 pair.2) := by
  unfold matrixExpectation matrixOfFiniteCoupling pmfExp
  rw [Fintype.sum_prod_type]

/-- Convert a real fixed-nominal kernel matrix into its finite joint PMF. -/
noncomputable def lawOfKernelMatrix (nominal : PMF Target) (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ kernelMatrices (Source := Source)
      (fun targetIndex => (nominal targetIndex).toReal)) : PMF (Source × Target) :=
  PMF.ofFintype (fun pair => ENNReal.ofReal (matrix pair.1 pair.2)) (by
    rcases hmatrix with ⟨hnonneg, hcolumn⟩
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      ∑ targetIndex, ∑ sourceIndex, ENNReal.ofReal (matrix sourceIndex targetIndex) =
        ∑ targetIndex, ENNReal.ofReal (∑ sourceIndex, matrix sourceIndex targetIndex) := by
          apply Finset.sum_congr rfl
          intro targetIndex _
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro sourceIndex _
          exact hnonneg sourceIndex targetIndex
      _ = ∑ targetIndex, nominal targetIndex := by
          apply Finset.sum_congr rfl
          intro targetIndex _
          rw [hcolumn targetIndex, ENNReal.ofReal_toReal (nominal.apply_ne_top _)]
      _ = 1 := by
          simpa only [tsum_fintype] using nominal.tsum_coe)

/-- The joint PMF made from a kernel matrix has the prescribed second marginal. -/
theorem lawOfKernelMatrix_snd_marginal (nominal : PMF Target) (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ kernelMatrices (Source := Source)
      (fun targetIndex => (nominal targetIndex).toReal)) :
    (lawOfKernelMatrix nominal matrix hmatrix).map Prod.snd = nominal := by
  apply PMF.ext
  intro targetIndex
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single targetIndex]
  · simp only [lawOfKernelMatrix, PMF.ofFintype_apply, if_true]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun sourceIndex _ => hmatrix.1 sourceIndex targetIndex),
      hmatrix.2 targetIndex]
    exact ENNReal.ofReal_toReal (nominal.apply_ne_top _)
  · intro outerTarget _ houterTarget
    apply Finset.sum_eq_zero
    intro sourceIndex _
    simp only [lawOfKernelMatrix, PMF.ofFintype_apply]
    rw [if_neg]
    exact fun h => houterTarget h.symm
  · simp

/-- The joint PMF of a coupling matrix has its prescribed first marginal. -/
theorem lawOfCouplingMatrix_fst_marginal (source : PMF Source) (nominal : PMF Target)
    (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ couplingMatrices (fun sourceIndex => (source sourceIndex).toReal)
      (fun targetIndex => (nominal targetIndex).toReal)) :
    (lawOfKernelMatrix nominal matrix ⟨hmatrix.1, hmatrix.2.2⟩).map Prod.fst = source := by
  apply PMF.ext
  intro sourceIndex
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single sourceIndex]
  · simp only [lawOfKernelMatrix, PMF.ofFintype_apply, if_true]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun targetIndex _ => hmatrix.1 sourceIndex targetIndex),
      hmatrix.2.1 sourceIndex]
    exact ENNReal.ofReal_toReal (source.apply_ne_top _)
  · intro outerSource _ houterSource
    apply Finset.sum_eq_zero
    intro targetIndex _
    simp only [lawOfKernelMatrix, PMF.ofFintype_apply]
    rw [if_neg]
    exact fun h => houterSource h.symm
  · simp

/-- Convert a real finite coupling matrix into its corresponding PMF coupling. -/
noncomputable def finiteCouplingOfCouplingMatrix (source : PMF Source) (nominal : PMF Target)
    (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ couplingMatrices (fun sourceIndex => (source sourceIndex).toReal)
      (fun targetIndex => (nominal targetIndex).toReal)) : FiniteCoupling source nominal where
  law := lawOfKernelMatrix nominal matrix ⟨hmatrix.1, hmatrix.2.2⟩
  fst_marginal := lawOfCouplingMatrix_fst_marginal source nominal matrix hmatrix
  snd_marginal := lawOfKernelMatrix_snd_marginal nominal matrix ⟨hmatrix.1, hmatrix.2.2⟩

/-- Recovering the real matrix from its induced finite coupling is exact. -/
theorem matrixOfFiniteCoupling_finiteCouplingOfCouplingMatrix (source : PMF Source)
    (nominal : PMF Target) (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ couplingMatrices (fun sourceIndex => (source sourceIndex).toReal)
      (fun targetIndex => (nominal targetIndex).toReal)) :
    matrixOfFiniteCoupling (finiteCouplingOfCouplingMatrix source nominal matrix hmatrix) = matrix := by
  ext sourceIndex targetIndex
  simp only [matrixOfFiniteCoupling, finiteCouplingOfCouplingMatrix, lawOfKernelMatrix,
    PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hmatrix.1 sourceIndex targetIndex)

/-- The PMF coupling induced by a real matrix has exactly that matrix's expected payoff. -/
theorem finiteCouplingOfCouplingMatrix_expectedCost (source : PMF Source) (nominal : PMF Target)
    (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ couplingMatrices (fun sourceIndex => (source sourceIndex).toReal)
      (fun targetIndex => (nominal targetIndex).toReal)) (payoff : Source → Target → ℝ) :
    (finiteCouplingOfCouplingMatrix source nominal matrix hmatrix).expectedCost payoff =
      matrixExpectation matrix payoff := by
  unfold FiniteCoupling.expectedCost
  rw [← matrixExpectation_matrixOfFiniteCoupling,
    matrixOfFiniteCoupling_finiteCouplingOfCouplingMatrix source nominal matrix hmatrix]

/--
Finite transport infima are attained.  The proof realizes couplings as a
compact real matrix polytope and returns its continuous cost minimizer to a
finite PMF coupling.
-/
theorem exists_expectedCost_eq_finiteTransportCost
    (source : PMF Source) (nominal : PMF Target) (cost : Source → Target → ℝ)
    (hcost : ∀ sourceIndex targetIndex, 0 ≤ cost sourceIndex targetIndex) :
    ∃ coupling : FiniteCoupling source nominal,
      coupling.expectedCost cost = FiniteCoupling.finiteTransportCost source nominal cost := by
  have hsource_nonneg : ∀ sourceIndex, 0 ≤ (source sourceIndex).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hsource_sum : ∑ sourceIndex, (source sourceIndex).toReal = 1 := pmfToRealSum source
  have hnominal_nonneg : ∀ targetIndex, 0 ≤ (nominal targetIndex).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hnominal_sum : ∑ targetIndex, (nominal targetIndex).toReal = 1 := pmfToRealSum nominal
  obtain ⟨minimizer, hminimizer_mem, hminimizer⟩ :=
    (couplingMatrices_isCompact (fun sourceIndex => (source sourceIndex).toReal)
      (fun targetIndex => (nominal targetIndex).toReal)).exists_isMinOn
      (couplingMatrices_nonempty _ _ hsource_nonneg hsource_sum hnominal_nonneg hnominal_sum)
      (continuous_matrixExpectation cost).continuousOn
  let optimalCoupling : FiniteCoupling source nominal :=
    finiteCouplingOfCouplingMatrix source nominal minimizer hminimizer_mem
  refine ⟨optimalCoupling, le_antisymm ?_ ?_⟩
  · unfold FiniteCoupling.finiteTransportCost
    refine le_csInf (FiniteCoupling.transportCostSet_nonempty source nominal cost) ?_
    rintro value ⟨coupling, rfl⟩
    have hmin_le := hminimizer (matrixOfFiniteCoupling_mem_couplingMatrices coupling)
    change matrixExpectation minimizer cost ≤
      matrixExpectation (matrixOfFiniteCoupling coupling) cost at hmin_le
    calc
      optimalCoupling.expectedCost cost = matrixExpectation minimizer cost :=
        finiteCouplingOfCouplingMatrix_expectedCost source nominal minimizer hminimizer_mem cost
      _ ≤ matrixExpectation (matrixOfFiniteCoupling coupling) cost := hmin_le
      _ = coupling.expectedCost cost := matrixExpectation_matrixOfFiniteCoupling coupling cost
  · exact FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost optimalCoupling

/-- The finite coupling induced by a fixed-nominal real kernel matrix. -/
noncomputable def finiteCouplingOfKernelMatrix (nominal : PMF Target)
    (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ kernelMatrices (Source := Source)
      (fun targetIndex => (nominal targetIndex).toReal)) :
    FiniteCoupling ((lawOfKernelMatrix nominal matrix hmatrix).map Prod.fst) nominal where
  law := lawOfKernelMatrix nominal matrix hmatrix
  fst_marginal := rfl
  snd_marginal := lawOfKernelMatrix_snd_marginal nominal matrix hmatrix

/-- The real matrix recovered from its induced finite coupling is unchanged. -/
theorem matrixOfFiniteCoupling_finiteCouplingOfKernelMatrix (nominal : PMF Target)
    (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ kernelMatrices (Source := Source)
      (fun targetIndex => (nominal targetIndex).toReal)) :
    matrixOfFiniteCoupling (finiteCouplingOfKernelMatrix nominal matrix hmatrix) = matrix := by
  ext sourceIndex targetIndex
  simp only [matrixOfFiniteCoupling, finiteCouplingOfKernelMatrix, lawOfKernelMatrix,
    PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hmatrix.1 sourceIndex targetIndex)

/-- The induced finite coupling has exactly the matrix's expected payoff. -/
theorem finiteCouplingOfKernelMatrix_expectedCost (nominal : PMF Target)
    (matrix : Matrix Source Target ℝ)
    (hmatrix : matrix ∈ kernelMatrices (Source := Source)
      (fun targetIndex => (nominal targetIndex).toReal)) (payoff : Source → Target → ℝ) :
    (finiteCouplingOfKernelMatrix nominal matrix hmatrix).expectedCost payoff =
      matrixExpectation matrix payoff := by
  unfold FiniteCoupling.expectedCost
  rw [← matrixExpectation_matrixOfFiniteCoupling,
    matrixOfFiniteCoupling_finiteCouplingOfKernelMatrix nominal matrix hmatrix]

/-- The finite constrained kernel value: maximize payoff subject to a transport budget. -/
noncomputable def constrainedKernelValue (target : Target → ℝ)
    (payoff cost : Source → Target → ℝ) (radius : ℝ) : ℝ :=
  sSup ((fun matrix => matrixExpectation matrix payoff) ''
    {matrix | matrix ∈ kernelMatrices (Source := Source) target ∧
      matrixExpectation matrix cost ≤ radius})

/-- The scalar Lagrange dual for a finite constrained kernel problem. -/
noncomputable def constrainedKernelDualValue (target : Target → ℝ)
    (payoff cost : Source → Target → ℝ) (radius : ℝ) : ℝ :=
  Optimization.scalarDualValue (kernelMatrices (Source := Source) target)
    (fun matrix => matrixExpectation matrix payoff)
    (fun matrix => matrixExpectation matrix cost - radius)

/--
Strong duality for a finite kernel problem with one transport-budget constraint.
An explicit strictly budget-feasible kernel is the exact finite Slater
condition, so no hidden transport-attainment premise is used.
-/
theorem constrainedKernelValue_eq_dualValue (target : Target → ℝ)
    (payoff cost : Source → Target → ℝ) (radius : ℝ)
    (hstrict : ∃ matrix ∈ kernelMatrices (Source := Source) target,
      matrixExpectation matrix cost < radius) :
    constrainedKernelValue target payoff cost radius =
      constrainedKernelDualValue target payoff cost radius := by
  obtain ⟨strictMatrix, hstrictMatrix, hstrictCost⟩ := hstrict
  have hstrong := Optimization.scalarStrongDuality_of_isScalarSlater
    (X := kernelMatrices (Source := Source) target)
    (f := fun matrix => matrixExpectation matrix payoff)
    (g := fun matrix => matrixExpectation matrix cost - radius)
    (kernelMatrices_isCompact (Source := Source) target)
    (continuous_matrixExpectation payoff).continuousOn
    (concaveOn_matrixExpectation_of_convex _
      (kernelMatrices_convex (Source := Source) target) payoff)
    (continuous_matrixExpectation_sub_const cost radius).continuousOn
    (convexOn_matrixExpectation_sub_const_of_convex _
      (kernelMatrices_convex (Source := Source) target) cost radius)
    ⟨kernelMatrices_convex (Source := Source) target,
      convexOn_matrixExpectation_sub_const_of_convex _
        (kernelMatrices_convex (Source := Source) target) cost radius,
      ⟨strictMatrix, hstrictMatrix, sub_neg.mpr hstrictCost⟩⟩
  unfold constrainedKernelValue constrainedKernelDualValue
  simpa only [Optimization.scalarPrimalValue, Optimization.scalarFeasible, sub_nonpos] using hstrong

/-- Matrix expectation is both convex and concave on every coupling polytope. -/
theorem convexOn_matrixExpectation (source : Source → ℝ) (target : Target → ℝ)
    (payoff : Source → Target → ℝ) :
    ConvexOn ℝ (couplingMatrices source target) (fun matrix => matrixExpectation matrix payoff) := by
  refine ⟨couplingMatrices_convex source target, ?_⟩
  intro first _ second _ weightFirst weightSecond _ _ _
  change matrixExpectation (weightFirst • first + weightSecond • second) payoff ≤
    weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff
  rw [matrixExpectation_combo]

/-- Matrix expectation is both convex and concave on every coupling polytope. -/
theorem concaveOn_matrixExpectation (source : Source → ℝ) (target : Target → ℝ)
    (payoff : Source → Target → ℝ) :
    ConcaveOn ℝ (couplingMatrices source target) (fun matrix => matrixExpectation matrix payoff) := by
  refine ⟨couplingMatrices_convex source target, ?_⟩
  intro first _ second _ weightFirst weightSecond _ _ _
  change weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff ≤
    matrixExpectation (weightFirst • first + weightSecond • second) payoff
  rw [matrixExpectation_combo]

/-- A finite matrix expectation minus a constant is convex on a coupling polytope. -/
theorem convexOn_matrixExpectation_sub_const (source : Source → ℝ) (target : Target → ℝ)
    (payoff : Source → Target → ℝ) (constant : ℝ) :
    ConvexOn ℝ (couplingMatrices source target)
      (fun matrix => matrixExpectation matrix payoff - constant) := by
  refine ⟨couplingMatrices_convex source target, ?_⟩
  intro first _ second _ weightFirst weightSecond _ _ hweights
  change matrixExpectation (weightFirst • first + weightSecond • second) payoff - constant ≤
    weightFirst * (matrixExpectation first payoff - constant) +
      weightSecond * (matrixExpectation second payoff - constant)
  rw [matrixExpectation_combo]
  calc
    weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff -
        constant =
      weightFirst * matrixExpectation first payoff + weightSecond * matrixExpectation second payoff -
        (weightFirst + weightSecond) * constant := by rw [hweights, one_mul]
    _ = weightFirst * (matrixExpectation first payoff - constant) +
        weightSecond * (matrixExpectation second payoff - constant) := by ring
    _ ≤ weightFirst * (matrixExpectation first payoff - constant) +
        weightSecond * (matrixExpectation second payoff - constant) := le_rfl

end FiniteTransportMatrix
end AppliedModelingLib
