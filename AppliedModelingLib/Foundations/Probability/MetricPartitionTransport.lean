import AppliedModelingLib.Foundations.Probability.MeasureTransport
import Vlasov.OT.Coupling

/-!
# Finite metric hierarchies and Wasserstein transport

This module turns the cell-mass discrepancies of a nested finite quantization
hierarchy into a deterministic Wasserstein-1 bound.  It is paper-independent:
Euclidean dyadic partitions, compact grids, and other finite nested
quantizations can instantiate the same interface.

## External Lean provenance and license audit

The primal/dual bridge directly imports the Apache-2.0 project
[Hydrodynamical/Vlasov_Meanfield_Formalization](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization/tree/b2eda09e58ceebad6cf23b8a7a6839001d4e7c15)
at immutable commit `b2eda09e58ceebad6cf23b8a7a6839001d4e7c15`.
The declarations used are `Vlasov.IsCoupling`,
`Vlasov.wasserstein1_coupling`, `Vlasov.wasserstein1_eq_iSup_lipschitz`,
`Vlasov.wasserstein1_eq_coupling`, and
`Vlasov.wassersteinCost_coupling_comm`, and
`Vlasov.wassersteinCost_coupling_triangle`, from
[`Vlasov/Vlasov/OT/Wasserstein.lean`](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization/blob/b2eda09e58ceebad6cf23b8a7a6839001d4e7c15/Vlasov/Vlasov/OT/Wasserstein.lean)
and
[`Vlasov/Vlasov/OT/Coupling.lean`](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization/blob/b2eda09e58ceebad6cf23b8a7a6839001d4e7c15/Vlasov/Vlasov/OT/Coupling.lean).
No upstream code is copied or modified.  The dependency was compiled unchanged
under this repository's Lean toolchain; the files contain no `sorry`,
`admit`, or `axiom`, their key declarations report only `propext`,
`Classical.choice`, and `Quot.sound`, and the upstream repository has no
`NOTICE` file.  Redistribution must retain its Apache-2.0 attribution and
license.

The central Mathlib declarations used below are `integral_finset_sum`,
`integral_sub`, and `norm_integral_le_of_norm_le_const` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
`integral_indicator_const` from
[`MeasureTheory/Integral/Bochner/Set.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean),
`integrable_finset_sum` from
[`MeasureTheory/Function/L1Space/Integrable.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean),
and `LipschitzWith.dist_le_mul` from
[`Topology/MetricSpace/Lipschitz.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/MetricSpace/Lipschitz.lean),
all at this project's pinned Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` under Apache-2.0.  No Mathlib
source is copied or modified.
-/

namespace AppliedModelingLib

open MeasureTheory
open scoped ENNReal

namespace ProbabilityCoupling

/-- A local probability coupling satisfies the upstream Vlasov marginal predicate. -/
theorem isVlasovCoupling
    {E : Type*} [MeasurableSpace E]
    {mu nu : ProbabilityMeasure E} (coupling : ProbabilityCoupling mu nu) :
    Vlasov.IsCoupling (coupling.joint : Measure (E × E))
      (mu : Measure E) (nu : Measure E) := by
  constructor
  · exact congrArg ProbabilityMeasure.toMeasure coupling.map_fst
  · exact congrArg ProbabilityMeasure.toMeasure coupling.map_snd

/--
The local primal W₁ infimum and the Vlasov primal W₁ infimum range over the
same couplings.  The two libraries package probability mass differently, so
the proof converts between a probability measure and a measure carrying an
`IsProbabilityMeasure` instance.
-/
theorem wassersteinOne_eq_vlasov_coupling
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (mu nu : ProbabilityMeasure E) :
    wassersteinOne mu nu =
      Vlasov.wasserstein1_coupling (mu : Measure E) (nu : Measure E) := by
  apply le_antisymm
  · refine le_iInf fun joint => le_iInf fun hjoint => ?_
    letI : IsProbabilityMeasure joint := by
      refine ⟨?_⟩
      have hmass : joint Set.univ = (mu : Measure E) Set.univ := by
        rw [← hjoint.1, Measure.map_apply measurable_fst MeasurableSet.univ,
          Set.preimage_univ]
      rw [hmass, measure_univ]
    let jointProbability : ProbabilityMeasure (E × E) := ⟨joint, inferInstance⟩
    let coupling : ProbabilityCoupling mu nu := {
      joint := jointProbability
      map_fst := by
        apply Subtype.ext
        exact hjoint.1
      map_snd := by
        apply Subtype.ext
        exact hjoint.2
    }
    exact wassersteinOne_le_cost coupling
  · unfold wassersteinOne transportCost
    apply le_sInf
    rintro costValue ⟨coupling, rfl⟩
    exact iInf_le_of_le (coupling.joint : Measure (E × E))
      (iInf_le_of_le (isVlasovCoupling coupling) le_rfl)

/--
Symmetry of the local primal W₁ cost. The local infimum is identified with
the credited Vlasov coupling infimum, whose cost-swap theorem supplies this
step.
-/
theorem wassersteinOne_comm
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    (mu nu : ProbabilityMeasure E) :
    wassersteinOne mu nu = wassersteinOne nu mu := by
  rw [wassersteinOne_eq_vlasov_coupling mu nu,
    wassersteinOne_eq_vlasov_coupling nu mu,
    Vlasov.wasserstein1_coupling_eq, Vlasov.wasserstein1_coupling_eq]
  exact Vlasov.wassersteinCost_coupling_comm (fun x y : E => dist x y)
    dist_comm measurable_dist (mu : Measure E) (nu : Measure E)

/--
Triangle inequality for the local primal W₁ cost on standard Borel metric
spaces. The local coupling infimum is identified with the credited Vlasov
coupling infimum, whose gluing theorem supplies the triangle step.
-/
theorem wassersteinOne_triangle
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    (mu nu rho : ProbabilityMeasure E) :
    wassersteinOne mu nu ≤ wassersteinOne mu rho + wassersteinOne rho nu := by
  rw [wassersteinOne_eq_vlasov_coupling mu nu,
    wassersteinOne_eq_vlasov_coupling mu rho,
    wassersteinOne_eq_vlasov_coupling rho nu,
    Vlasov.wasserstein1_coupling_eq, Vlasov.wasserstein1_coupling_eq,
    Vlasov.wasserstein1_coupling_eq]
  exact Vlasov.wassersteinCost_coupling_triangle (fun x y : E => dist x y)
    (fun x y z => dist_triangle x y z) measurable_dist
    (mu : Measure E) (nu : Measure E) (rho : Measure E)

end ProbabilityCoupling

namespace Probability

open scoped BigOperators

/-- A real-valued function that is constant with the prescribed value on each cell. -/
noncomputable def piecewiseCellValue
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (cell : Piece → Set E) (value : Piece → ℝ) (x : E) : ℝ :=
  ∑ piece, (cell piece).indicator (fun _ : E => value piece) x

/--
The expectation discrepancy of a finite cellwise-constant function is bounded
by its coefficients times the absolute cell-mass discrepancies.
-/
theorem abs_integral_piecewiseCellValue_sub_le
    {E Piece : Type*} [MeasurableSpace E] [Fintype Piece]
    (mu nu : ProbabilityMeasure E) (cell : Piece → Set E)
    (hcell : ∀ piece, MeasurableSet (cell piece)) (value : Piece → ℝ) :
    |(∫ x, piecewiseCellValue cell value x ∂(mu : Measure E)) -
        ∫ x, piecewiseCellValue cell value x ∂(nu : Measure E)| ≤
      ∑ piece, |value piece| * |(mu : Measure E).real (cell piece) -
        (nu : Measure E).real (cell piece)| := by
  have hintegrable_mu : ∀ piece, Integrable
      ((cell piece).indicator (fun _ : E => value piece)) (mu : Measure E) := by
    intro piece
    exact Integrable.indicator (integrable_const _) (hcell piece)
  have hintegrable_nu : ∀ piece, Integrable
      ((cell piece).indicator (fun _ : E => value piece)) (nu : Measure E) := by
    intro piece
    exact Integrable.indicator (integrable_const _) (hcell piece)
  simp only [piecewiseCellValue]
  rw [integral_finset_sum _ (fun piece _ => hintegrable_mu piece),
    integral_finset_sum _ (fun piece _ => hintegrable_nu piece)]
  simp_rw [integral_indicator_const _ (hcell _), smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ piece, ((mu : Measure E).real (cell piece) * value piece -
        (nu : Measure E).real (cell piece) * value piece)| ≤
        ∑ piece, |(mu : Measure E).real (cell piece) * value piece -
          (nu : Measure E).real (cell piece) * value piece| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro piece _
      rw [← sub_mul, abs_mul, mul_comm]

/--
A nested finite quantization of a pseudometric space.

`locate` assigns a cell at each level, `parent` makes assignments nested,
and `anchor` chooses representatives.  `stepRadius` controls successive
representatives, while `radius` controls the approximation of each point by
its current representative.  Empty cells are allowed, so the parent-anchor
bound is stated for every cell index.
-/
structure FiniteQuantizationHierarchy
    (E : Type*) [MeasurableSpace E] [PseudoMetricSpace E]
    (Cell : ℕ → Type*) [∀ level, Fintype (Cell level)] where
  locate : ∀ level, E → Cell level
  anchor : ∀ level, Cell level → E
  parent : ∀ level, Cell (level + 1) → Cell level
  root : Cell 0
  locate_zero : ∀ x, locate 0 x = root
  parent_locate : ∀ level x, parent level (locate (level + 1) x) = locate level x
  measurable_cell : ∀ level cell, MeasurableSet {x | locate level x = cell}
  stepRadius : ℕ → ℝ
  stepRadius_nonneg : ∀ level, 0 ≤ stepRadius level
  dist_anchor_parent_le : ∀ level index,
    dist (anchor (level + 1) index) (anchor level (parent level index)) ≤
      stepRadius level
  radius : ℕ → ℝ
  radius_nonneg : ∀ level, 0 ≤ radius level
  dist_anchor_le : ∀ level x, dist x (anchor level (locate level x)) ≤ radius level

namespace FiniteQuantizationHierarchy

variable {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
variable {Cell : ℕ → Type*} [∀ level, Fintype (Cell level)]

/-- The measurable fiber assigned to a cell index. -/
def cell (hierarchy : FiniteQuantizationHierarchy E Cell)
    (level : ℕ) (index : Cell level) : Set E :=
  {x | hierarchy.locate level x = index}

/-- Quantize a test function by evaluating it at the current cell's anchor. -/
def levelValue (hierarchy : FiniteQuantizationHierarchy E Cell)
    (f : E → ℝ) (level : ℕ) (x : E) : ℝ :=
  f (hierarchy.anchor level (hierarchy.locate level x))

theorem piecewiseCellValue_apply
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    {level : ℕ}
    (value : Cell level → ℝ) (x : E) :
    piecewiseCellValue (hierarchy.cell level) value x =
      value (hierarchy.locate level x) := by
  classical
  unfold piecewiseCellValue cell
  rw [Finset.sum_eq_single (hierarchy.locate level x)]
  · simp
  · intro index _ hindex
    have hx : hierarchy.locate level x ≠ index := Ne.symm hindex
    simp [hx]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem piecewiseCellValue_eq_levelValue
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (f : E → ℝ) (level : ℕ) (x : E) :
    piecewiseCellValue (hierarchy.cell level)
      (fun index => f (hierarchy.anchor level index)) x =
      hierarchy.levelValue f level x := by
  rw [piecewiseCellValue_apply]
  rfl

theorem levelValue_succ_sub_eq_piecewiseCellValue
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (f : E → ℝ) (level : ℕ) (x : E) :
    hierarchy.levelValue f (level + 1) x - hierarchy.levelValue f level x =
      piecewiseCellValue (hierarchy.cell (level + 1))
        (fun index => f (hierarchy.anchor (level + 1) index) -
          f (hierarchy.anchor level (hierarchy.parent level index))) x := by
  rw [piecewiseCellValue_apply]
  unfold levelValue
  rw [hierarchy.parent_locate]

theorem integrable_levelValue
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (mu : ProbabilityMeasure E) (f : E → ℝ) (level : ℕ) :
    Integrable (hierarchy.levelValue f level) (mu : Measure E) := by
  classical
  have heq : hierarchy.levelValue f level =
      piecewiseCellValue (hierarchy.cell level)
        (fun index ↦ f (hierarchy.anchor level index)) := by
    funext x
    exact (piecewiseCellValue_eq_levelValue hierarchy f level x).symm
  rw [heq]
  unfold piecewiseCellValue
  exact integrable_finset_sum Finset.univ fun index _ ↦
    Integrable.indicator (integrable_const _)
      (hierarchy.measurable_cell level index)

theorem abs_anchor_increment_le
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (f : E → ℝ) (hf : LipschitzWith 1 f) (level : ℕ)
    (index : Cell (level + 1)) :
    |f (hierarchy.anchor (level + 1) index) -
        f (hierarchy.anchor level (hierarchy.parent level index))| ≤
      hierarchy.stepRadius level := by
  calc
    |f (hierarchy.anchor (level + 1) index) -
        f (hierarchy.anchor level (hierarchy.parent level index))| =
        dist (f (hierarchy.anchor (level + 1) index))
          (f (hierarchy.anchor level (hierarchy.parent level index))) := by
            rw [Real.dist_eq]
    _ ≤ dist (hierarchy.anchor (level + 1) index)
          (hierarchy.anchor level (hierarchy.parent level index)) := by
      simpa using hf.dist_le_mul (hierarchy.anchor (level + 1) index)
        (hierarchy.anchor level (hierarchy.parent level index))
    _ ≤ hierarchy.stepRadius level :=
      hierarchy.dist_anchor_parent_le level index

theorem abs_levelIntegralIncrement_sub_le
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (mu nu : ProbabilityMeasure E) (f : E → ℝ)
    (hf : LipschitzWith 1 f) (level : ℕ) :
    |((∫ x, hierarchy.levelValue f (level + 1) x ∂(mu : Measure E)) -
          ∫ x, hierarchy.levelValue f level x ∂(mu : Measure E)) -
        ((∫ x, hierarchy.levelValue f (level + 1) x ∂(nu : Measure E)) -
          ∫ x, hierarchy.levelValue f level x ∂(nu : Measure E))| ≤
      hierarchy.stepRadius level *
        ∑ index : Cell (level + 1),
          |(mu : Measure E).real (hierarchy.cell (level + 1) index) -
            (nu : Measure E).real (hierarchy.cell (level + 1) index)| := by
  let increment : Cell (level + 1) → ℝ := fun index ↦
    f (hierarchy.anchor (level + 1) index) -
      f (hierarchy.anchor level (hierarchy.parent level index))
  have hmu :
      (∫ x, hierarchy.levelValue f (level + 1) x ∂(mu : Measure E)) -
          ∫ x, hierarchy.levelValue f level x ∂(mu : Measure E) =
        ∫ x, piecewiseCellValue (hierarchy.cell (level + 1)) increment x
          ∂(mu : Measure E) := by
    rw [← integral_sub (integrable_levelValue hierarchy mu f (level + 1))
      (integrable_levelValue hierarchy mu f level)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact levelValue_succ_sub_eq_piecewiseCellValue hierarchy f level x
  have hnu :
      (∫ x, hierarchy.levelValue f (level + 1) x ∂(nu : Measure E)) -
          ∫ x, hierarchy.levelValue f level x ∂(nu : Measure E) =
        ∫ x, piecewiseCellValue (hierarchy.cell (level + 1)) increment x
          ∂(nu : Measure E) := by
    rw [← integral_sub (integrable_levelValue hierarchy nu f (level + 1))
      (integrable_levelValue hierarchy nu f level)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact levelValue_succ_sub_eq_piecewiseCellValue hierarchy f level x
  rw [hmu, hnu]
  calc
    |(∫ x, piecewiseCellValue (hierarchy.cell (level + 1)) increment x
          ∂(mu : Measure E)) -
        ∫ x, piecewiseCellValue (hierarchy.cell (level + 1)) increment x
          ∂(nu : Measure E)| ≤
        ∑ index : Cell (level + 1), |increment index| *
          |(mu : Measure E).real (hierarchy.cell (level + 1) index) -
            (nu : Measure E).real (hierarchy.cell (level + 1) index)| :=
      abs_integral_piecewiseCellValue_sub_le mu nu
        (hierarchy.cell (level + 1))
        (hierarchy.measurable_cell (level + 1)) increment
    _ ≤ ∑ index : Cell (level + 1), hierarchy.stepRadius level *
          |(mu : Measure E).real (hierarchy.cell (level + 1) index) -
            (nu : Measure E).real (hierarchy.cell (level + 1) index)| := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul_of_nonneg_right
        (abs_anchor_increment_le hierarchy f hf level index) (abs_nonneg _)
    _ = hierarchy.stepRadius level *
        ∑ index : Cell (level + 1),
          |(mu : Measure E).real (hierarchy.cell (level + 1) index) -
            (nu : Measure E).real (hierarchy.cell (level + 1) index)| := by
      rw [Finset.mul_sum]

/--
Telescoping through a finite hierarchy bounds the discrepancy of the quantized
test function by weighted cell-mass discrepancies at every positive level.
-/
theorem abs_levelIntegral_sub_le
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (mu nu : ProbabilityMeasure E) (f : E → ℝ)
    (hf : LipschitzWith 1 f) (depth : ℕ) :
    |(∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
        ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)| ≤
      ∑ l ∈ Finset.range depth, hierarchy.stepRadius l *
        ∑ index : Cell (l + 1),
          |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
            (nu : Measure E).real (hierarchy.cell (l + 1) index)| := by
  induction depth with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      have hmu :
          (∫ x, hierarchy.levelValue f 0 x ∂(mu : Measure E)) =
            f (hierarchy.anchor 0 hierarchy.root) := by
        apply integral_eq_const
        filter_upwards [] with x
        simp [levelValue, hierarchy.locate_zero]
      have hnu :
          (∫ x, hierarchy.levelValue f 0 x ∂(nu : Measure E)) =
            f (hierarchy.anchor 0 hierarchy.root) := by
        apply integral_eq_const
        filter_upwards [] with x
        simp [levelValue, hierarchy.locate_zero]
      rw [hmu, hnu, sub_self, abs_zero]
  | succ depth ih =>
      calc
        |(∫ x, hierarchy.levelValue f (depth + 1) x ∂(mu : Measure E)) -
            ∫ x, hierarchy.levelValue f (depth + 1) x ∂(nu : Measure E)| =
            |((∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
                ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)) +
              (((∫ x, hierarchy.levelValue f (depth + 1) x ∂(mu : Measure E)) -
                  ∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
                ((∫ x, hierarchy.levelValue f (depth + 1) x ∂(nu : Measure E)) -
                  ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)))| := by
              congr 1
              ring
        _ ≤ |(∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
                ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)| +
              |((∫ x, hierarchy.levelValue f (depth + 1) x ∂(mu : Measure E)) -
                  ∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
                ((∫ x, hierarchy.levelValue f (depth + 1) x ∂(nu : Measure E)) -
                  ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E))| :=
            abs_add_le _ _
        _ ≤ (∑ l ∈ Finset.range depth, hierarchy.stepRadius l *
                ∑ index : Cell (l + 1),
                  |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
                    (nu : Measure E).real (hierarchy.cell (l + 1) index)|) +
              hierarchy.stepRadius depth *
                ∑ index : Cell (depth + 1),
                  |(mu : Measure E).real (hierarchy.cell (depth + 1) index) -
                    (nu : Measure E).real (hierarchy.cell (depth + 1) index)| :=
          add_le_add ih
            (abs_levelIntegralIncrement_sub_le hierarchy mu nu f hf depth)
        _ = ∑ l ∈ Finset.range (depth + 1), hierarchy.stepRadius l *
              ∑ index : Cell (l + 1),
                |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
                  (nu : Measure E).real (hierarchy.cell (l + 1) index)| := by
          rw [Finset.sum_range_succ]

theorem abs_sub_levelValue_le
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (f : E → ℝ) (hf : LipschitzWith 1 f) (level : ℕ) (x : E) :
    |f x - hierarchy.levelValue f level x| ≤ hierarchy.radius level := by
  calc
    |f x - hierarchy.levelValue f level x| =
        dist (f x) (f (hierarchy.anchor level (hierarchy.locate level x))) := by
      rw [Real.dist_eq]
      rfl
    _ ≤ dist x (hierarchy.anchor level (hierarchy.locate level x)) := by
      simpa using hf.dist_le_mul x
        (hierarchy.anchor level (hierarchy.locate level x))
    _ ≤ hierarchy.radius level := hierarchy.dist_anchor_le level x

theorem abs_integral_sub_levelIntegral_le
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (mu : ProbabilityMeasure E) (f : E → ℝ)
    (hf : LipschitzWith 1 f) (hf_integrable : Integrable f (mu : Measure E))
    (level : ℕ) :
    |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, hierarchy.levelValue f level x ∂(mu : Measure E)| ≤
      hierarchy.radius level := by
  rw [← integral_sub hf_integrable
    (integrable_levelValue hierarchy mu f level)]
  have hbound : ∀ᵐ x ∂(mu : Measure E),
      ‖f x - hierarchy.levelValue f level x‖ ≤ hierarchy.radius level := by
    filter_upwards [] with x
    simpa [Real.norm_eq_abs] using
      abs_sub_levelValue_le hierarchy f hf level x
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := (mu : Measure E)) hbound)

/--
Finite-depth deterministic multiscale estimate for a 1-Lipschitz test
function.  The term `2 * radius depth` is the approximation error under the
two probability laws; the sum is the telescoping cell-mass error.
-/
theorem abs_integral_sub_le_multiscale
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (mu nu : ProbabilityMeasure E) (f : E → ℝ)
    (hf : LipschitzWith 1 f)
    (hf_mu : Integrable f (mu : Measure E))
    (hf_nu : Integrable f (nu : Measure E)) (depth : ℕ) :
    |(∫ x, f x ∂(mu : Measure E)) - ∫ x, f x ∂(nu : Measure E)| ≤
      2 * hierarchy.radius depth +
        ∑ l ∈ Finset.range depth, hierarchy.stepRadius l *
          ∑ index : Cell (l + 1),
            |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
              (nu : Measure E).real (hierarchy.cell (l + 1) index)| := by
  have hmu := abs_integral_sub_levelIntegral_le hierarchy mu f hf hf_mu depth
  have hnu := abs_integral_sub_levelIntegral_le hierarchy nu f hf hf_nu depth
  have hlevel := abs_levelIntegral_sub_le hierarchy mu nu f hf depth
  have habs_add_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
    calc
      |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le _ _) le_rfl
  calc
    |(∫ x, f x ∂(mu : Measure E)) - ∫ x, f x ∂(nu : Measure E)| =
        |((∫ x, f x ∂(mu : Measure E)) -
            ∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) +
          ((∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
            ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)) +
          ((∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)) -
            ∫ x, f x ∂(nu : Measure E))| := by
          congr 1
          ring
    _ ≤ |(∫ x, f x ∂(mu : Measure E)) -
            ∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)| +
          |(∫ x, hierarchy.levelValue f depth x ∂(mu : Measure E)) -
            ∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)| +
          |(∫ x, hierarchy.levelValue f depth x ∂(nu : Measure E)) -
            ∫ x, f x ∂(nu : Measure E)| := by
      exact habs_add_three _ _ _
    _ ≤ hierarchy.radius depth +
          (∑ l ∈ Finset.range depth, hierarchy.stepRadius l *
            ∑ index : Cell (l + 1),
              |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
                (nu : Measure E).real (hierarchy.cell (l + 1) index)|) +
          hierarchy.radius depth := by
      exact add_le_add (add_le_add hmu hlevel) (by simpa [abs_sub_comm] using hnu)
    _ = 2 * hierarchy.radius depth +
        ∑ l ∈ Finset.range depth, hierarchy.stepRadius l *
          ∑ index : Cell (l + 1),
            |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
              (nu : Measure E).real (hierarchy.cell (l + 1) index)| := by ring

/--
A real 1-Lipschitz test function is integrable under any finite measure with a
finite first moment around `basepoint`.  This is the standard domination by
`|f basepoint| + dist x basepoint`; the same mathematical reduction appears in
the credited upstream proof of `Vlasov.wasserstein1_eq_coupling`, but no source
code is copied.
-/
theorem integrable_lipschitzWith_one_of_integrable_dist
    [BorelSpace E] {mu : Measure E} [IsFiniteMeasure mu]
    (basepoint : E) (hdist : Integrable (fun x : E ↦ dist x basepoint) mu)
    (f : E → ℝ) (hf : LipschitzWith 1 f) : Integrable f mu := by
  have hpoint : ∀ x, |f x| ≤ |f basepoint| + dist x basepoint := by
    intro x
    calc
      |f x| = |(f x - f basepoint) + f basepoint| := by ring_nf
      _ ≤ |f x - f basepoint| + |f basepoint| := abs_add_le _ _
      _ ≤ dist x basepoint + |f basepoint| := by
        have hlip := hf.dist_le_mul x basepoint
        rw [Real.dist_eq, NNReal.coe_one, one_mul] at hlip
        exact add_le_add hlip le_rfl
      _ = |f basepoint| + dist x basepoint := by ring
  have hdom : Integrable (fun x : E ↦ |f basepoint| + dist x basepoint) mu :=
    (integrable_const _).add hdist
  exact hdom.mono hf.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) dist_nonneg)]
      exact hpoint x)

/--
Finite-depth primal W₁ bound for a nested finite quantization hierarchy.

The proof applies the deterministic estimate to every 1-Lipschitz test
function, then uses the exactly credited Vlasov Kantorovich--Rubinstein theorem
and the local/upstream coupling equivalence above.  This is the reusable
transport boundary needed before specializing to Fournier--Guillin's dyadic
Euclidean hierarchy; it is not itself a concentration theorem.
-/
theorem wassersteinOne_le_multiscale
    [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]
    (hierarchy : FiniteQuantizationHierarchy E Cell)
    (mu nu : ProbabilityMeasure E) (basepoint : E)
    (hmu : Integrable (fun x : E ↦ dist x basepoint) (mu : Measure E))
    (hnu : Integrable (fun x : E ↦ dist x basepoint) (nu : Measure E))
    (depth : ℕ) :
    ProbabilityCoupling.wassersteinOne mu nu ≤ ENNReal.ofReal
      (2 * hierarchy.radius depth +
        ∑ l ∈ Finset.range depth, hierarchy.stepRadius l *
          ∑ index : Cell (l + 1),
            |(mu : Measure E).real (hierarchy.cell (l + 1) index) -
              (nu : Measure E).real (hierarchy.cell (l + 1) index)|) := by
  rw [ProbabilityCoupling.wassersteinOne_eq_vlasov_coupling]
  rw [← Vlasov.wasserstein1_eq_coupling
    (mu : Measure E) (nu : Measure E) basepoint hmu hnu]
  rw [Vlasov.wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun f ↦ iSup_le fun hf ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  exact (le_abs_self _).trans
    (abs_integral_sub_le_multiscale hierarchy mu nu f hf
      (integrable_lipschitzWith_one_of_integrable_dist basepoint hmu f hf)
      (integrable_lipschitzWith_one_of_integrable_dist basepoint hnu f hf)
      depth)

end FiniteQuantizationHierarchy

end Probability
end AppliedModelingLib
