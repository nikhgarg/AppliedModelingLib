import AppliedModelingLib.Foundations.Probability.CountableMixture
import AppliedModelingLib.Foundations.Probability.EmpiricalMeasure
import AppliedModelingLib.Foundations.Probability.EuclideanTruncation

/-!
# Euclidean dyadic shells

The shell geometry in this module is the first reusable ingredient for the
noncompact stage of Fournier--Guillin, *On the rate of convergence in
Wasserstein distance of the empirical measure* (2015), Notation 4(b) and
Section 6.  It supplies the source's half-open dyadic-cube shells as well as
an auxiliary Euclidean-norm-shell geometry used by the existing radial
collapse APIs.  The latter is not identified with the source partition. This
module deliberately does not claim the source's shell transport inequality or
concentration theorem.

No Lean source is copied or ported.  The scale map reuses the local checked
radial-collapse APIs, whose pinned Mathlib Apache-2.0 provenance is recorded
in `EuclideanTruncation.lean` and `docs/UPSTREAM_LEAN_SOURCES.md`.  The
normalized restriction below directly reuses `FiniteMeasure.restrict` from
[`MeasureTheory/Measure/FiniteMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean)
and `FiniteMeasure.normalize` from
[`MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean),
and the exact resynthesis of each restricted shell from its mass and
normalization uses `FiniteMeasure.self_eq_mass_smul_normalize` from that same
pinned Mathlib file,
while the source-cube measurability proof uses `measurableSet_Ioc` from
[`MeasureTheory/Constructions/BorelSpace/Order.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean),
`MeasurableSet.iInter` from
[`MeasureTheory/MeasurableSpace/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean),
and `Measurable.subtype_mk` from
[`MeasureTheory/MeasurableSpace/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean),
the countable shell decomposition uses `Measure.restrict_iUnion` from
[`MeasureTheory/Measure/Restrict.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Restrict.lean),
and its shell-mass normalization uses `Measure.sum_apply` from
[`MeasureTheory/Measure/MeasureSpace.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/MeasureSpace.lean),
and the global measurable extension of the shell scale directly reuses
`MeasurableEmbedding.exists_measurable_extend` from
[`MeasureTheory/MeasurableSpace/Embedding.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean),
while the scale-back Lipschitz proof uses `LipschitzWith.of_dist_le_mul` from
[`Topology/EMetricSpace/Lipschitz.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/EMetricSpace/Lipschitz.lean),
and the normalized scale-back identity uses `Measure.map_congr` and
`Measure.map_id` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
and its exhaustive-cover proof uses `tendsto_pow_atTop_atTop_of_one_lt` from
[`Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Basic.lean)
and `PiLp.norm_apply_le` / `PiLp.norm_sq_eq_of_L2` from
[`Analysis/Normed/Lp/PiLp.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Normed/Lp/PiLp.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
-/

namespace AppliedModelingLib
namespace Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The positive half-side length of the source's `scale`-th dyadic cube. -/
def euclideanDyadicCubeRadius (scale : ℕ) : ℝ :=
  ((2 ^ scale : ℕ) : ℝ)

theorem euclideanDyadicCubeRadius_pos (scale : ℕ) :
    0 < euclideanDyadicCubeRadius scale := by
  unfold euclideanDyadicCubeRadius
  positivity

/-- The source half-open dyadic cube `(-2^scale, 2^scale]^dimension`. -/
def euclideanDyadicCube (dimension scale : ℕ) : Set (EuclideanSpace ℝ (Fin dimension)) :=
  {x | ∀ coordinate, x coordinate ∈ Set.Ioc (-euclideanDyadicCubeRadius scale)
    (euclideanDyadicCubeRadius scale)}

theorem measurableSet_euclideanDyadicCube (dimension scale : ℕ) :
    MeasurableSet (euclideanDyadicCube dimension scale) := by
  rw [show euclideanDyadicCube dimension scale =
      ⋂ coordinate : Fin dimension, {x | x coordinate ∈
        Set.Ioc (-euclideanDyadicCubeRadius scale) (euclideanDyadicCubeRadius scale)} by
    ext x
    simp [euclideanDyadicCube]]
  apply MeasurableSet.iInter
  intro coordinate
  exact measurableSet_Ioc.preimage (by fun_prop)

/-- The source's half-open dyadic shell: the central cube at zero, then cube differences. -/
def euclideanDyadicCubeShell (dimension shell : ℕ) :
    Set (EuclideanSpace ℝ (Fin dimension)) :=
  match shell with
  | 0 => euclideanDyadicCube dimension 0
  | shell + 1 => euclideanDyadicCube dimension (shell + 1) \
      euclideanDyadicCube dimension shell

theorem measurableSet_euclideanDyadicCubeShell (dimension shell : ℕ) :
    MeasurableSet (euclideanDyadicCubeShell dimension shell) := by
  rcases shell with _ | shell
  · exact measurableSet_euclideanDyadicCube dimension 0
  · exact (measurableSet_euclideanDyadicCube dimension (shell + 1)).diff
      (measurableSet_euclideanDyadicCube dimension shell)

theorem euclideanDyadicCubeShell_subset_cube (dimension shell : ℕ) :
    euclideanDyadicCubeShell dimension shell ⊆ euclideanDyadicCube dimension shell := by
  rcases shell with _ | shell
  · exact Set.Subset.rfl
  · exact fun _ hx ↦ hx.1

/--
Every point in the source's `scale`-th cube has Euclidean norm at most
`sqrt dimension * 2^scale`.  The dimension factor is needed because the
source's cube norm convention and this module's Euclidean `l²` metric differ.
-/
theorem norm_le_sqrt_dim_mul_euclideanDyadicCubeRadius
    (dimension scale : ℕ) (x : EuclideanSpace ℝ (Fin dimension))
    (hx : x ∈ euclideanDyadicCube dimension scale) :
    ‖x‖ ≤ Real.sqrt dimension * euclideanDyadicCubeRadius scale := by
  have hradius : 0 ≤ euclideanDyadicCubeRadius scale :=
    (euclideanDyadicCubeRadius_pos scale).le
  have hcoordinate : ∀ coordinate : Fin dimension,
      ‖x coordinate‖ ≤ euclideanDyadicCubeRadius scale := by
    intro coordinate
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨le_of_lt (hx coordinate).1, (hx coordinate).2⟩
  have hnormSq : ‖x‖ ^ 2 ≤ (dimension : ℝ) * euclideanDyadicCubeRadius scale ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ coordinate : Fin dimension, ‖x coordinate‖ ^ 2 ≤
          ∑ _coordinate : Fin dimension, euclideanDyadicCubeRadius scale ^ 2 := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact (sq_le_sq₀ (norm_nonneg _) hradius).mpr (hcoordinate coordinate)
      _ = (dimension : ℝ) * euclideanDyadicCubeRadius scale ^ 2 := by
        simp
  have hsquare : (Real.sqrt dimension * euclideanDyadicCubeRadius scale) ^ 2 =
      (dimension : ℝ) * euclideanDyadicCubeRadius scale ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg (dimension : ℝ)) hradius)).mp
  rw [hsquare]
  exact hnormSq

theorem euclideanDyadicCubeRadius_le {lower upper : ℕ} (hle : lower ≤ upper) :
    euclideanDyadicCubeRadius lower ≤ euclideanDyadicCubeRadius upper := by
  unfold euclideanDyadicCubeRadius
  exact_mod_cast Nat.pow_le_pow_right (by omega) hle

theorem euclideanDyadicCube_mono (dimension : ℕ) {lower upper : ℕ} (hle : lower ≤ upper) :
    euclideanDyadicCube dimension lower ⊆ euclideanDyadicCube dimension upper := by
  intro x hx coordinate
  have hradius := euclideanDyadicCubeRadius_le hle
  exact ⟨lt_of_le_of_lt (neg_le_neg hradius) (hx coordinate).1,
    (hx coordinate).2.trans hradius⟩

/-- Distinct source half-open dyadic-cube shells are disjoint. -/
theorem disjoint_euclideanDyadicCubeShell (dimension first second : ℕ)
    (hne : first ≠ second) :
    Disjoint (euclideanDyadicCubeShell dimension first)
      (euclideanDyadicCubeShell dimension second) := by
  have hdisjoint_of_lt : ∀ {lower upper : ℕ}, lower < upper →
      Disjoint (euclideanDyadicCubeShell dimension lower)
        (euclideanDyadicCubeShell dimension upper) := by
    intro lower upper hlt
    rcases upper with _ | upper
    · omega
    · rw [Set.disjoint_left]
      intro x hlower hupper
      change x ∈ euclideanDyadicCube dimension (upper + 1) \
        euclideanDyadicCube dimension upper at hupper
      exact hupper.2 (euclideanDyadicCube_mono dimension (Nat.le_of_lt_succ hlt)
        (euclideanDyadicCubeShell_subset_cube dimension lower hlower))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hdisjoint_of_lt hlt
  · exact (hdisjoint_of_lt hgt).symm

theorem exists_mem_euclideanDyadicCube (dimension : ℕ)
    (x : EuclideanSpace ℝ (Fin dimension)) :
    ∃ scale, x ∈ euclideanDyadicCube dimension scale := by
  have heventually :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) one_lt_two).eventually_gt_atTop ‖x‖
  rcases Filter.eventually_atTop.1 heventually with ⟨scale, hscale⟩
  refine ⟨scale, ?_⟩
  intro coordinate
  have hcoordinate : |x coordinate| ≤ ‖x‖ := by
    calc
      |x coordinate| = ‖x coordinate‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := PiLp.norm_apply_le x coordinate
  have hradius : ‖x‖ < euclideanDyadicCubeRadius scale := by
    rw [show euclideanDyadicCubeRadius scale = (2 : ℝ) ^ scale by
      norm_num [euclideanDyadicCubeRadius]]
    exact hscale scale le_rfl
  have habs : |x coordinate| < euclideanDyadicCubeRadius scale :=
    hcoordinate.trans_lt hradius
  exact ⟨(neg_lt_neg habs).trans_le (neg_abs_le _),
    (le_abs_self _).trans (le_of_lt habs)⟩

/-- The source half-open dyadic-cube shells cover the entire Euclidean space. -/
theorem exists_mem_euclideanDyadicCubeShell (dimension : ℕ)
    (x : EuclideanSpace ℝ (Fin dimension)) :
    ∃ shell, x ∈ euclideanDyadicCubeShell dimension shell := by
  classical
  let existsCube : ∃ scale, x ∈ euclideanDyadicCube dimension scale :=
    exists_mem_euclideanDyadicCube dimension x
  rcases hfind : Nat.find existsCube with _ | shell
  · refine ⟨0, ?_⟩
    simpa [euclideanDyadicCubeShell, hfind] using Nat.find_spec existsCube
  · refine ⟨shell + 1, ?_⟩
    change x ∈ euclideanDyadicCube dimension (shell + 1) \
      euclideanDyadicCube dimension shell
    refine ⟨by simpa [hfind] using Nat.find_spec existsCube, ?_⟩
    intro hinner
    have hminimal := Nat.find_min' existsCube hinner
    rw [hfind] at hminimal
    omega

/-- The unique source cube-shell index selected for an ambient Euclidean point. -/
noncomputable def euclideanDyadicCubeShellIndex (dimension : ℕ)
    (x : EuclideanSpace ℝ (Fin dimension)) : ℕ := by
  classical
  exact Nat.find (exists_mem_euclideanDyadicCubeShell dimension x)

/-- The selected source cube-shell index contains its point. -/
theorem mem_euclideanDyadicCubeShellIndex (dimension : ℕ)
    (x : EuclideanSpace ℝ (Fin dimension)) :
    x ∈ euclideanDyadicCubeShell dimension (euclideanDyadicCubeShellIndex dimension x) :=
  by
    classical
    exact Nat.find_spec (exists_mem_euclideanDyadicCubeShell dimension x)

/-- A point in a source cube shell has that shell as its selected index. -/
theorem euclideanDyadicCubeShellIndex_eq_of_mem
    (dimension : ℕ) (x : EuclideanSpace ℝ (Fin dimension)) (shell : ℕ)
    (hx : x ∈ euclideanDyadicCubeShell dimension shell) :
    euclideanDyadicCubeShellIndex dimension x = shell := by
  by_contra hne
  exact Set.disjoint_left.1
    (disjoint_euclideanDyadicCubeShell dimension
      (euclideanDyadicCubeShellIndex dimension x) shell hne)
    (mem_euclideanDyadicCubeShellIndex dimension x) hx

/-- The finite family of source cube shells occupied by a finite empirical sample. -/
def empiricalEuclideanDyadicCubeShellSupport
    {count : ℕ} (dimension : ℕ) (sample : Fin count → EuclideanSpace ℝ (Fin dimension)) :
    Finset ℕ :=
  Finset.univ.image (euclideanDyadicCubeShellIndex dimension ∘ sample)

theorem iUnion_euclideanDyadicCubeShell (dimension : ℕ) :
    ⋃ shell, euclideanDyadicCubeShell dimension shell = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases exists_mem_euclideanDyadicCubeShell dimension x with ⟨shell, hx⟩
  exact Set.mem_iUnion.2 ⟨shell, hx⟩

/-- The exact source shell family decomposes every Euclidean probability law. -/
theorem measure_sum_restrict_euclideanDyadicCubeShell (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    Measure.sum (fun shell : ℕ =>
      (law : Measure (EuclideanSpace ℝ (Fin dimension))).restrict
        (euclideanDyadicCubeShell dimension shell)) = law := by
  have h := Measure.restrict_iUnion
    (μ := (law : Measure (EuclideanSpace ℝ (Fin dimension))))
    (fun first second hne =>
      disjoint_euclideanDyadicCubeShell dimension first second hne)
    (measurableSet_euclideanDyadicCubeShell dimension)
  rw [iUnion_euclideanDyadicCubeShell dimension, Measure.restrict_univ] at h
  exact h.symm

/-- The exact source shell masses sum to one. -/
theorem hasSum_measure_euclideanDyadicCubeShell (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    HasSum (fun shell : ℕ =>
      (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (euclideanDyadicCubeShell dimension shell)) 1 := by
  have hdecomp := measure_sum_restrict_euclideanDyadicCubeShell dimension law
  have hsum := congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
    measure Set.univ) hdecomp
  simp only [Measure.sum_apply, MeasurableSet.univ, Measure.restrict_apply,
    measure_univ] at hsum
  rw [← hsum]
  simpa only [Set.univ_inter] using
    (ENNReal.summable.hasSum (f := fun shell : ℕ =>
      (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (euclideanDyadicCubeShell dimension shell)))

/-- A noncentral source shell lies outside the preceding Euclidean-radius ball. -/
theorem euclideanDyadicCubeShell_succ_subset_norm_ge (dimension shell : ℕ) :
    euclideanDyadicCubeShell dimension (shell + 1) ⊆
      {x : EuclideanSpace ℝ (Fin dimension) |
        euclideanDyadicCubeRadius shell ≤ ‖x‖} := by
  classical
  intro x hx
  change x ∈ euclideanDyadicCube dimension (shell + 1) \
    euclideanDyadicCube dimension shell at hx
  have hnotInner := hx.2
  simp only [euclideanDyadicCube, Set.mem_setOf_eq] at hnotInner
  push Not at hnotInner
  obtain ⟨coordinate, hcoordinate⟩ := hnotInner
  rw [Set.mem_Ioc] at hcoordinate
  have hradius : 0 ≤ euclideanDyadicCubeRadius shell :=
    (euclideanDyadicCubeRadius_pos shell).le
  have habs : euclideanDyadicCubeRadius shell ≤ |x coordinate| := by
    by_cases hleft : -euclideanDyadicCubeRadius shell < x coordinate
    · have hnotupper : ¬ x coordinate ≤ euclideanDyadicCubeRadius shell :=
        fun hupper ↦ hcoordinate ⟨hleft, hupper⟩
      have hright : euclideanDyadicCubeRadius shell < x coordinate := lt_of_not_ge hnotupper
      nlinarith [le_abs_self (x coordinate)]
    · have hleft' : x coordinate ≤ -euclideanDyadicCubeRadius shell := le_of_not_gt hleft
      nlinarith [neg_abs_le (x coordinate)]
  calc
    euclideanDyadicCubeRadius shell ≤ |x coordinate| := habs
    _ = ‖x coordinate‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x‖ := PiLp.norm_apply_le x coordinate

/--
The source scaling from a half-open dyadic cube shell to `(-1, 1]^dimension`.
Unlike the radial-collapse map, this is exactly the coordinatewise scaling
used in Fournier--Guillin Notation 4(b).
-/
def euclideanDyadicCubeShellScale (dimension shell : ℕ) :
    euclideanDyadicCubeShell dimension shell → HalfOpenUnitCube dimension :=
  fun x ↦ ⟨(euclideanDyadicCubeRadius shell)⁻¹ • x.1, by
    intro coordinate
    have hx := euclideanDyadicCubeShell_subset_cube dimension shell x.2 coordinate
    change -1 < (euclideanDyadicCubeRadius shell)⁻¹ * x.1 coordinate ∧
      (euclideanDyadicCubeRadius shell)⁻¹ * x.1 coordinate ≤ 1
    rw [show (euclideanDyadicCubeRadius shell)⁻¹ * x.1 coordinate =
        x.1 coordinate / euclideanDyadicCubeRadius shell by
      rw [div_eq_mul_inv, mul_comm]]
    constructor
    · exact (lt_div_iff₀ (euclideanDyadicCubeRadius_pos shell)).2 (by simpa using hx.1)
    · exact (div_le_iff₀ (euclideanDyadicCubeRadius_pos shell)).2 (by simpa using hx.2)⟩

theorem measurable_euclideanDyadicCubeShellScale (dimension shell : ℕ) :
    Measurable (euclideanDyadicCubeShellScale dimension shell) := by
  apply Measurable.subtype_mk
  change Measurable (fun x : euclideanDyadicCubeShell dimension shell ↦
    (euclideanDyadicCubeRadius shell)⁻¹ •
      (x : EuclideanSpace ℝ (Fin dimension)))
  fun_prop

/-- Scale a point of the source compact cube into the `shell`-th ambient cube. -/
def euclideanDyadicCubeScaleBack (dimension shell : ℕ)
    (x : HalfOpenUnitCube dimension) : EuclideanSpace ℝ (Fin dimension) :=
  euclideanDyadicCubeRadius shell • x.1

theorem measurable_euclideanDyadicCubeScaleBack (dimension shell : ℕ) :
    Measurable (euclideanDyadicCubeScaleBack dimension shell) := by
  change Measurable (fun x : HalfOpenUnitCube dimension ↦
    euclideanDyadicCubeRadius shell • (x : EuclideanSpace ℝ (Fin dimension)))
  fun_prop

/-- The source cube scale-back has Lipschitz constant `2^shell`. -/
theorem lipschitzWith_euclideanDyadicCubeScaleBack (dimension shell : ℕ) :
    LipschitzWith ⟨euclideanDyadicCubeRadius shell,
      (euclideanDyadicCubeRadius_pos shell).le⟩
      (euclideanDyadicCubeScaleBack dimension shell) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (euclideanDyadicCubeRadius shell • (x : EuclideanSpace ℝ (Fin dimension)))
      (euclideanDyadicCubeRadius shell • (y : EuclideanSpace ℝ (Fin dimension))) ≤
    euclideanDyadicCubeRadius shell * dist (x : EuclideanSpace ℝ (Fin dimension)) y
  rw [dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (euclideanDyadicCubeRadius_pos shell).le, dist_eq_norm]

/--
Scaling compact laws back to the `shell`-th source cube costs at most a factor
`2^shell` in W₁. This is the compact-to-shell transport leg; it does not yet
couple the normalized shell laws themselves.
-/
theorem wassersteinOne_euclideanDyadicCubeScaleBack_le (dimension shell : ℕ)
    (mu nu : ProbabilityMeasure (HalfOpenUnitCube dimension)) :
    ProbabilityCoupling.wassersteinOne
      (mu.map (measurable_euclideanDyadicCubeScaleBack dimension shell).aemeasurable)
      (nu.map (measurable_euclideanDyadicCubeScaleBack dimension shell).aemeasurable) ≤
      ((NNReal.mk (euclideanDyadicCubeRadius shell)
        (euclideanDyadicCubeRadius_pos shell).le : NNReal) : ℝ≥0∞) *
        ProbabilityCoupling.wassersteinOne mu nu := by
  exact ProbabilityCoupling.wassersteinOne_map_le_of_lipschitz
    (euclideanDyadicCubeScaleBack dimension shell)
    (NNReal.mk (euclideanDyadicCubeRadius shell) (euclideanDyadicCubeRadius_pos shell).le)
    (lipschitzWith_euclideanDyadicCubeScaleBack dimension shell)
    (measurable_euclideanDyadicCubeScaleBack dimension shell) mu nu

/-- The origin is a canonical point of the source compact cube. -/
def halfOpenUnitCubeOrigin (dimension : ℕ) : HalfOpenUnitCube dimension :=
  ⟨0, fun _ ↦ by norm_num [halfOpenUnitInterval]⟩

theorem exists_measurable_euclideanDyadicCubeShellScaleExtension (dimension shell : ℕ) :
    ∃ extension : EuclideanSpace ℝ (Fin dimension) → HalfOpenUnitCube dimension,
      Measurable extension ∧ ∀ x : euclideanDyadicCubeShell dimension shell,
        extension x = euclideanDyadicCubeShellScale dimension shell x := by
  let embedding :=
    MeasurableEmbedding.subtype_coe (measurableSet_euclideanDyadicCubeShell dimension shell)
  obtain ⟨extension, hextension, hextends⟩ :=
    embedding.exists_measurable_extend
      (measurable_euclideanDyadicCubeShellScale dimension shell)
      (fun _ ↦ ⟨halfOpenUnitCubeOrigin dimension⟩)
  exact ⟨extension, hextension, fun x ↦ congr_fun hextends x⟩

/--
A chosen measurable extension of the source scale map. Its values outside the
shell are mathematically irrelevant to the restricted shell measure.
-/
noncomputable def euclideanDyadicCubeShellScaleExtension (dimension shell : ℕ) :
    EuclideanSpace ℝ (Fin dimension) → HalfOpenUnitCube dimension :=
  Classical.choose (exists_measurable_euclideanDyadicCubeShellScaleExtension dimension shell)

theorem measurable_euclideanDyadicCubeShellScaleExtension (dimension shell : ℕ) :
    Measurable (euclideanDyadicCubeShellScaleExtension dimension shell) :=
  (Classical.choose_spec
    (exists_measurable_euclideanDyadicCubeShellScaleExtension dimension shell)).1

theorem euclideanDyadicCubeShellScaleExtension_eq_scale (dimension shell : ℕ)
    (x : euclideanDyadicCubeShell dimension shell) :
    euclideanDyadicCubeShellScaleExtension dimension shell x =
      euclideanDyadicCubeShellScale dimension shell x :=
  (Classical.choose_spec
    (exists_measurable_euclideanDyadicCubeShellScaleExtension dimension shell)).2 x

/-- Source cube-shell scaling is exactly inverted by its coordinatewise scale-back. -/
theorem euclideanDyadicCubeScaleBack_euclideanDyadicCubeShellScale
    (dimension shell : ℕ) (x : euclideanDyadicCubeShell dimension shell) :
    euclideanDyadicCubeScaleBack dimension shell
      (euclideanDyadicCubeShellScale dimension shell x) = x.1 := by
  unfold euclideanDyadicCubeScaleBack euclideanDyadicCubeShellScale
  change euclideanDyadicCubeRadius shell •
      ((euclideanDyadicCubeRadius shell)⁻¹ • x.1) = x.1
  rw [← mul_smul, mul_inv_cancel₀ (euclideanDyadicCubeRadius_pos shell).ne', one_smul]

/--
The source-style normalized law on a half-open dyadic-cube shell. Mathlib's
normalization is total at zero shell mass; later weighted results must retain
the shell mass rather than infer a conditional-law statement in that branch.
-/
def euclideanDyadicCubeShellLaw (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)) :=
  (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)).normalize

/--
On a positive source shell, the normalized shell law is exactly the ambient
law conditioned on membership in that shell.

Library provenance: this directly uses Mathlib's `ProbabilityTheory.cond` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ConditionalProbability.lean>
and `FiniteMeasure.toMeasure_normalize_eq_of_nonzero` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean>.
These pinned Mathlib sources are Apache-2.0; no source text is copied or
ported.
-/
theorem cond_eq_euclideanDyadicCubeShellLaw_of_nonzero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hnonzero : law.toFiniteMeasure.restrict
      (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    ProbabilityTheory.cond (law : Measure (EuclideanSpace ℝ (Fin dimension)))
      (euclideanDyadicCubeShell dimension shell) =
      (euclideanDyadicCubeShellLaw dimension shell law :
        Measure (EuclideanSpace ℝ (Fin dimension))) := by
  unfold ProbabilityTheory.cond euclideanDyadicCubeShellLaw
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
    (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)) hnonzero]
  have hmass :
      (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (euclideanDyadicCubeShell dimension shell) =
      ((law.toFiniteMeasure.restrict
        (euclideanDyadicCubeShell dimension shell)).mass : ℝ≥0∞) := by
    rw [FiniteMeasure.mass]
    simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      FiniteMeasure.restrict_apply, MeasurableSet.univ, Set.univ_inter]
    exact congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
      measure (euclideanDyadicCubeShell dimension shell))
      (ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure law).symm
  rw [← Measure.coe_nnreal_smul]
  rw [hmass]
  rw [ENNReal.coe_inv
    ((FiniteMeasure.mass_nonzero_iff
      (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell))).mpr hnonzero)]
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure law]
  rfl

/--
Each source shell law, weighted by its actual shell mass, resynthesizes the
original probability law. This keeps Mathlib's total zero-mass normalization
inside a zero-weight term, matching the weighted conditional-law convention
needed by the shell-coupling construction.
-/
theorem measure_sum_shellMass_smul_euclideanDyadicCubeShellLaw (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    Measure.sum (fun shell : ℕ =>
      (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (euclideanDyadicCubeShell dimension shell) •
        (euclideanDyadicCubeShellLaw dimension shell law :
          Measure (EuclideanSpace ℝ (Fin dimension)))) = law := by
  calc
    Measure.sum (fun shell : ℕ =>
      (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (euclideanDyadicCubeShell dimension shell) •
        (euclideanDyadicCubeShellLaw dimension shell law :
          Measure (EuclideanSpace ℝ (Fin dimension)))) =
        Measure.sum (fun shell : ℕ =>
          (law : Measure (EuclideanSpace ℝ (Fin dimension))).restrict
            (euclideanDyadicCubeShell dimension shell)) := by
      congr 1
      funext shell
      have hmass : (law : Measure (EuclideanSpace ℝ (Fin dimension)))
          (euclideanDyadicCubeShell dimension shell) =
          ↑(law.toFiniteMeasure.restrict
            (euclideanDyadicCubeShell dimension shell)).mass := by
        rw [FiniteMeasure.mass]
        simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
          FiniteMeasure.restrict_apply, MeasurableSet.univ, Set.univ_inter]
        exact congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
          measure (euclideanDyadicCubeShell dimension shell))
          (ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure law).symm
      rw [hmass]
      simpa only [euclideanDyadicCubeShellLaw,
        FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        FiniteMeasure.restrict_apply, MeasurableSet.univ,
        Set.univ_inter] using
        congrArg FiniteMeasure.toMeasure
          (FiniteMeasure.self_eq_mass_smul_normalize
            (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell))).symm
    _ = law := measure_sum_restrict_euclideanDyadicCubeShell dimension law

/-- The actual mass of a source half-open dyadic-cube shell. -/
def euclideanDyadicCubeShellMass (dimension : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) (shell : ℕ) : ℝ≥0∞ :=
  (law : Measure (EuclideanSpace ℝ (Fin dimension)))
    (euclideanDyadicCubeShell dimension shell)

/--
An empirical source cube shell outside its finite occupied-shell family has
zero mass. This discharges the finite-support premise needed to take finite
local W₁ infima in the shell coupling bound.

Library provenance: this specializes the local checked empirical-support
lemma `empiricalSampleProbabilityMeasure_apply_eq_zero_of_forall_not_mem`.
The finite occupied-shell family directly uses Mathlib's `Finset.image` and
`Finset.mem_image` from
[`Data/Finset/Image.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Finset/Image.lean),
while its selected shell index uses `Nat.find`/`Nat.find_spec` from
[`Data/Nat/Find.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Nat/Find.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/
theorem euclideanDyadicCubeShellMass_empirical_eq_zero_of_not_mem_support
    {count : ℕ} [Nonempty (Fin count)] (dimension : ℕ)
    (sample : Fin count → EuclideanSpace ℝ (Fin dimension)) (shell : ℕ)
    (hnotmem : shell ∉ empiricalEuclideanDyadicCubeShellSupport dimension sample) :
    euclideanDyadicCubeShellMass dimension (empiricalSampleProbabilityMeasure sample) shell = 0 := by
  unfold euclideanDyadicCubeShellMass
  apply empiricalSampleProbabilityMeasure_apply_eq_zero_of_forall_not_mem sample
    (euclideanDyadicCubeShell dimension shell)
    (measurableSet_euclideanDyadicCubeShell dimension shell)
  intro index hsample
  apply hnotmem
  simp only [empiricalEuclideanDyadicCubeShellSupport, Finset.mem_image, Finset.mem_univ,
    Function.comp_apply, true_and]
  exact ⟨index, euclideanDyadicCubeShellIndex_eq_of_mem dimension (sample index) shell hsample⟩

/--
The common shell mass of a population law and a finite empirical law is
supported on the sample's finite occupied-shell family.
-/
theorem euclideanDyadicCubeShellCommonMass_finiteSupport_of_empirical
    {count : ℕ} [Nonempty (Fin count)] (dimension : ℕ)
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (sample : Fin count → EuclideanSpace ℝ (Fin dimension)) :
    ∀ shell ∉ empiricalEuclideanDyadicCubeShellSupport dimension sample,
      min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension (empiricalSampleProbabilityMeasure sample) shell) = 0 := by
  intro shell hnotmem
  rw [euclideanDyadicCubeShellMass_empirical_eq_zero_of_not_mem_support
    dimension sample shell hnotmem, min_zero]

/--
The actual mass of one source shell rescales its normalized shell law back to
the original restricted finite measure.  This retains the totalized
zero-mass normalization only under its zero weight.
-/
theorem euclideanDyadicCubeShellMass_smul_euclideanDyadicCubeShellLaw
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    euclideanDyadicCubeShellMass dimension law shell •
      (euclideanDyadicCubeShellLaw dimension shell law :
        Measure (EuclideanSpace ℝ (Fin dimension))) =
      law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) := by
  have hmass : euclideanDyadicCubeShellMass dimension law shell =
      ↑(law.toFiniteMeasure.restrict
        (euclideanDyadicCubeShell dimension shell)).mass := by
    rw [euclideanDyadicCubeShellMass, FiniteMeasure.mass]
    simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      FiniteMeasure.restrict_apply, MeasurableSet.univ, Set.univ_inter]
    exact congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
      measure (euclideanDyadicCubeShell dimension shell))
      (ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure law).symm
  rw [hmass]
  simpa only [euclideanDyadicCubeShellLaw,
    FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    FiniteMeasure.restrict_apply, MeasurableSet.univ,
    Set.univ_inter] using
    congrArg FiniteMeasure.toMeasure
      (FiniteMeasure.self_eq_mass_smul_normalize
        (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell))).symm

/--
On every positive-mass source shell, the normalized shell law has radial
first moment no larger than the Euclidean radius of its ambient coordinate
cube.  The `sqrt dimension` factor is explicit because the source uses cube
shells whereas this transport development uses the Euclidean metric.

Library provenance: the a.e. restriction support fact is Mathlib's
`ae_restrict_mem` from
[`MeasureTheory/Measure/Restrict.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Restrict.lean),
and `lintegral_mono_ae`/`lintegral_const` are from
[`MeasureTheory/Integral/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.  No source text is copied or
ported.
-/
theorem lintegral_edist_zero_euclideanDyadicCubeShellLaw_le_of_mass_ne_zero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmass_ne_zero : euclideanDyadicCubeShellMass dimension law shell ≠ 0) :
    ∫⁻ x, edist x 0 ∂(euclideanDyadicCubeShellLaw dimension shell law :
      Measure (EuclideanSpace ℝ (Fin dimension))) ≤
      ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell) := by
  have hmass_le_one : euclideanDyadicCubeShellMass dimension law shell ≤ 1 := by
    change (law : Measure (EuclideanSpace ℝ (Fin dimension)))
      (euclideanDyadicCubeShell dimension shell) ≤ 1
    rw [← IsProbabilityMeasure.measure_univ
      (μ := (law : Measure (EuclideanSpace ℝ (Fin dimension))))]
    exact measure_mono (Set.subset_univ _)
  have hmass_ne_top : euclideanDyadicCubeShellMass dimension law shell ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hmass_le_one ENNReal.one_lt_top)
  apply (ENNReal.mul_le_mul_iff_right hmass_ne_zero hmass_ne_top).mp
  calc
    euclideanDyadicCubeShellMass dimension law shell *
        ∫⁻ x, edist x 0 ∂(euclideanDyadicCubeShellLaw dimension shell law :
          Measure (EuclideanSpace ℝ (Fin dimension))) =
        ∫⁻ x, edist x 0 ∂(law.toFiniteMeasure.restrict
          (euclideanDyadicCubeShell dimension shell) :
            Measure (EuclideanSpace ℝ (Fin dimension))) := by
      have hmeasure := congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
        ∫⁻ x, edist x 0 ∂measure)
        (euclideanDyadicCubeShellMass_smul_euclideanDyadicCubeShellLaw dimension shell law)
      simpa only [lintegral_smul_measure, smul_eq_mul] using hmeasure
    _ ≤ ∫⁻ _x, ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell) ∂
        (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) :
          Measure (EuclideanSpace ℝ (Fin dimension))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_euclideanDyadicCubeShell dimension shell)] with x hx
      rw [edist_dist, dist_zero_right]
      exact ENNReal.ofReal_le_ofReal
        (norm_le_sqrt_dim_mul_euclideanDyadicCubeRadius dimension shell x
          (euclideanDyadicCubeShell_subset_cube dimension shell hx))
    _ = ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell) *
        euclideanDyadicCubeShellMass dimension law shell := by
      rw [lintegral_const]
      have hrestrict_mass :
          (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) :
            Measure (EuclideanSpace ℝ (Fin dimension))) Set.univ =
            euclideanDyadicCubeShellMass dimension law shell := by
        simpa only [Measure.smul_apply, smul_eq_mul,
          IsProbabilityMeasure.measure_univ, mul_one] using
          congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
            measure Set.univ)
            (euclideanDyadicCubeShellMass_smul_euclideanDyadicCubeShellLaw
              dimension shell law).symm
      rw [hrestrict_mass]
    _ = euclideanDyadicCubeShellMass dimension law shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell) := by
      rw [mul_comm]

/--
The total mass shared shellwise by two laws. This is the common-mass part of
Fournier--Guillin Lemma 5, Step 2, before the residual product coupling is
constructed.
-/
def euclideanDyadicCubeShellCommonMass (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) : ℝ≥0∞ :=
  ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell)

/-- The excess mass of the first law on a source cube shell. -/
def euclideanDyadicCubeShellExcessMass (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) (shell : ℕ) : ℝ≥0∞ :=
  euclideanDyadicCubeShellMass dimension mu shell -
    min (euclideanDyadicCubeShellMass dimension mu shell)
      (euclideanDyadicCubeShellMass dimension nu shell)

/--
The unsigned discrepancy between the two masses on one source cube shell.
This is the canonically ordered extended-nonnegative form of the source's
absolute shell-mass difference.
-/
def euclideanDyadicCubeShellMassDiscrepancy (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) (shell : ℕ) : ℝ≥0∞ :=
  max (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell) -
  min (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell)

/--
The two directed shell excesses add to the unsigned shell-mass discrepancy.
-/
theorem euclideanDyadicCubeShellExcessMass_add_eq_discrepancy (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) (shell : ℕ) :
    euclideanDyadicCubeShellExcessMass dimension mu nu shell +
      euclideanDyadicCubeShellExcessMass dimension nu mu shell =
      euclideanDyadicCubeShellMassDiscrepancy dimension mu nu shell := by
  let a := euclideanDyadicCubeShellMass dimension mu shell
  let b := euclideanDyadicCubeShellMass dimension nu shell
  change (a - min a b) + (b - min b a) = max a b - min a b
  rw [min_comm b a]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    simp
  · rw [min_eq_right hba, max_eq_left hba]
    simp

/--
The two weighted directed excess sums are exactly the weighted source-shell
mass-discrepancy sum.
-/
theorem tsum_euclideanDyadicCubeShellExcessMass_mul_radius_add
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    (∑' shell, euclideanDyadicCubeShellExcessMass dimension mu nu shell *
      ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
    (∑' shell, euclideanDyadicCubeShellExcessMass dimension nu mu shell *
      ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) =
    ∑' shell, euclideanDyadicCubeShellMassDiscrepancy dimension mu nu shell *
      ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell) := by
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro shell
  rw [← add_mul, euclideanDyadicCubeShellExcessMass_add_eq_discrepancy]

/-- The source common shell masses have their displayed countable sum. -/
theorem hasSum_euclideanDyadicCubeShellCommonMass (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    HasSum (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
      (euclideanDyadicCubeShellMass dimension nu shell))
      (euclideanDyadicCubeShellCommonMass dimension mu nu) := by
  exact ENNReal.summable.hasSum

/-- The total source common shell mass is at most one. -/
theorem euclideanDyadicCubeShellCommonMass_le_one (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    euclideanDyadicCubeShellCommonMass dimension mu nu ≤ 1 := by
  unfold euclideanDyadicCubeShellCommonMass
  refine (ENNReal.tsum_le_tsum ?_).trans_eq
    (hasSum_measure_euclideanDyadicCubeShell dimension mu).tsum_eq
  intro shell
  exact min_le_left _ _

/--
The source shellwise excess masses of the first law sum to the residual mass
`1 - commonMass`. This is mass bookkeeping only: it does not construct the
residual probability law or cross-shell transport coupling.
-/
theorem hasSum_euclideanDyadicCubeShellExcessMass (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    HasSum (euclideanDyadicCubeShellExcessMass dimension mu nu)
      (1 - euclideanDyadicCubeShellCommonMass dimension mu nu) := by
  have hcommon : euclideanDyadicCubeShellCommonMass dimension mu nu = ∑' shell,
      min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) := rfl
  have hcommon_le := euclideanDyadicCubeShellCommonMass_le_one dimension mu nu
  have hcommon_ne_top : euclideanDyadicCubeShellCommonMass dimension mu nu ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hcommon_le ENNReal.one_lt_top)
  have hmu : HasSum (euclideanDyadicCubeShellMass dimension mu) 1 := by
    simpa [euclideanDyadicCubeShellMass] using
      hasSum_measure_euclideanDyadicCubeShell dimension mu
  convert ENNReal.summable.hasSum
    (f := euclideanDyadicCubeShellExcessMass dimension mu nu) using 1
  symm
  change ∑' shell, (euclideanDyadicCubeShellMass dimension mu shell -
      min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell)) =
      1 - euclideanDyadicCubeShellCommonMass dimension mu nu
  rw [ENNReal.tsum_sub]
  · rw [hmu.tsum_eq, ← hcommon]
  · rw [← hcommon]
    exact hcommon_ne_top
  · intro shell
    exact min_le_left _ _

/--
The single residual mass and all common source shell masses form probability
weights. This specializes the reusable countable-mixture interface to the
exact Step 2 bookkeeping of the source proof.
-/
theorem hasSum_euclideanDyadicCubeShellResidualMixtureWeight (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    HasSum (residualMixtureWeight
      (1 - euclideanDyadicCubeShellCommonMass dimension mu nu)
      (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell))) 1 := by
  exact hasSum_residualMixtureWeight _ _
    (hasSum_euclideanDyadicCubeShellCommonMass dimension mu nu)
    (euclideanDyadicCubeShellCommonMass_le_one dimension mu nu)

/-- The mass not shared shellwise by two source cube-shell decompositions. -/
def euclideanDyadicCubeShellResidualMass (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) : ℝ≥0∞ :=
  1 - euclideanDyadicCubeShellCommonMass dimension mu nu

/-- Common shell mass is symmetric in the two laws. -/
theorem euclideanDyadicCubeShellCommonMass_comm (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    euclideanDyadicCubeShellCommonMass dimension mu nu =
      euclideanDyadicCubeShellCommonMass dimension nu mu := by
  unfold euclideanDyadicCubeShellCommonMass
  apply tsum_congr
  intro shell
  exact min_comm _ _

/-- Residual shell mass is symmetric in the two laws. -/
theorem euclideanDyadicCubeShellResidualMass_comm (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    euclideanDyadicCubeShellResidualMass dimension mu nu =
      euclideanDyadicCubeShellResidualMass dimension nu mu := by
  unfold euclideanDyadicCubeShellResidualMass
  rw [euclideanDyadicCubeShellCommonMass_comm dimension mu nu]

/--
Vanishing residual mass means that the two laws have identical mass on every
source cube shell.
-/
theorem euclideanDyadicCubeShellMass_eq_of_residualMass_eq_zero
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_zero : euclideanDyadicCubeShellResidualMass dimension mu nu = 0)
    (shell : ℕ) :
    euclideanDyadicCubeShellMass dimension mu shell =
      euclideanDyadicCubeShellMass dimension nu shell := by
  have hmu_excess_zero : ∀ shell,
      euclideanDyadicCubeShellExcessMass dimension mu nu shell = 0 := by
    apply ENNReal.tsum_eq_zero.mp
    rw [(hasSum_euclideanDyadicCubeShellExcessMass dimension mu nu).tsum_eq]
    simpa [euclideanDyadicCubeShellResidualMass] using hresidual_zero
  have hnu_residual_zero : euclideanDyadicCubeShellResidualMass dimension nu mu = 0 := by
    rw [← euclideanDyadicCubeShellResidualMass_comm dimension mu nu]
    exact hresidual_zero
  have hnu_excess_zero : ∀ shell,
      euclideanDyadicCubeShellExcessMass dimension nu mu shell = 0 := by
    apply ENNReal.tsum_eq_zero.mp
    rw [(hasSum_euclideanDyadicCubeShellExcessMass dimension nu mu).tsum_eq]
    simpa [euclideanDyadicCubeShellResidualMass] using hnu_residual_zero
  apply le_antisymm
  · exact (tsub_eq_zero_iff_le.mp (hmu_excess_zero shell)).trans (min_le_right _ _)
  · exact (tsub_eq_zero_iff_le.mp (hnu_excess_zero shell)).trans (min_le_right _ _)

theorem euclideanDyadicCubeShellCommonWeight_comm (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
      (euclideanDyadicCubeShellMass dimension nu shell)) =
      (fun shell => min (euclideanDyadicCubeShellMass dimension nu shell)
        (euclideanDyadicCubeShellMass dimension mu shell)) := by
  funext shell
  exact min_comm _ _

theorem euclideanDyadicCubeShellResidualMass_le_one (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    euclideanDyadicCubeShellResidualMass dimension mu nu ≤ 1 := by
  exact tsub_le_self

theorem euclideanDyadicCubeShellResidualMass_ne_top (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    euclideanDyadicCubeShellResidualMass dimension mu nu ≠ ∞ := by
  exact ne_of_lt (lt_of_le_of_lt
    (euclideanDyadicCubeShellResidualMass_le_one dimension mu nu) ENNReal.one_lt_top)

/--
When the source residual mass is positive, this is the normalized probability
law carried by the first law's shellwise excess. The zero-residual case is
intentionally not identified with an arbitrary normalized law here.
-/
noncomputable def euclideanDyadicCubeShellResidualLawOfNonzero (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)) :=
  countableMixtureProbability
    (fun shell => euclideanDyadicCubeShellExcessMass dimension mu nu shell /
      euclideanDyadicCubeShellResidualMass dimension mu nu)
    (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
    (hasSum_div_normalizeWeight _ _
      (by simpa [euclideanDyadicCubeShellResidualMass] using
        hasSum_euclideanDyadicCubeShellExcessMass dimension mu nu)
      hresidual_ne_zero
      (euclideanDyadicCubeShellResidualMass_ne_top dimension mu nu))

/--
Scaling the normalized nonzero residual law recovers precisely the first
law's countable excess-shell measure.
-/
theorem smul_euclideanDyadicCubeShellResidualLawOfNonzero (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0) :
    euclideanDyadicCubeShellResidualMass dimension mu nu •
      (euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hresidual_ne_zero :
        Measure (EuclideanSpace ℝ (Fin dimension))) =
      countableMixtureMeasure
        (euclideanDyadicCubeShellExcessMass dimension mu nu)
        (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) := by
  unfold euclideanDyadicCubeShellResidualLawOfNonzero
  exact smul_countableMixtureMeasure_div_normalizeWeight _ _ hresidual_ne_zero
    (euclideanDyadicCubeShellResidualMass_ne_top dimension mu nu) _

/--
The residual law's radial (or any nonnegative measurable-space) integral,
multiplied by its total residual mass, is exactly the weighted countable sum
of the excess-shell integrals.  This is the measure-theoretic bridge from the
source's residual product coupling to dyadic shell tail estimates.
-/
theorem residualMass_mul_lintegral_euclideanDyadicCubeShellResidualLawOfNonzero
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0)
    (f : EuclideanSpace ℝ (Fin dimension) → ℝ≥0∞) :
    euclideanDyadicCubeShellResidualMass dimension mu nu *
      ∫⁻ x, f x ∂(euclideanDyadicCubeShellResidualLawOfNonzero
        dimension mu nu hresidual_ne_zero :
          Measure (EuclideanSpace ℝ (Fin dimension))) =
      ∑' shell, euclideanDyadicCubeShellExcessMass dimension mu nu shell *
        ∫⁻ x, f x ∂(euclideanDyadicCubeShellLaw dimension shell mu :
          Measure (EuclideanSpace ℝ (Fin dimension))) := by
  have hmeasure := congrArg (fun measure : Measure (EuclideanSpace ℝ (Fin dimension)) =>
    ∫⁻ x, f x ∂measure)
    (smul_euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hresidual_ne_zero)
  change _ = _
  simpa only [lintegral_smul_measure, smul_eq_mul,
    lintegral_countableMixtureMeasure] using hmeasure

/--
The radial first moment of a positive normalized residual law, weighted by
its residual mass, is bounded by the corresponding dyadic excess-shell sum.
This is the geometric estimate for the independent residual product in the
source's shell coupling, with the explicit Euclidean `sqrt dimension` factor.
-/
theorem residualMass_mul_lintegral_edist_zero_euclideanDyadicCubeShellResidualLawOfNonzero_le
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0) :
    euclideanDyadicCubeShellResidualMass dimension mu nu *
      ∫⁻ x, edist x 0 ∂(euclideanDyadicCubeShellResidualLawOfNonzero
        dimension mu nu hresidual_ne_zero :
          Measure (EuclideanSpace ℝ (Fin dimension))) ≤
      ∑' shell, euclideanDyadicCubeShellExcessMass dimension mu nu shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell) := by
  rw [residualMass_mul_lintegral_euclideanDyadicCubeShellResidualLawOfNonzero
    dimension mu nu hresidual_ne_zero]
  apply ENNReal.tsum_le_tsum
  intro shell
  by_cases hmass : euclideanDyadicCubeShellMass dimension mu shell = 0
  · simp [euclideanDyadicCubeShellExcessMass, hmass]
  · exact mul_le_mul_right
      (lintegral_edist_zero_euclideanDyadicCubeShellLaw_le_of_mass_ne_zero
        dimension shell mu hmass) _

/--
The common-shell and first excess-shell measures add exactly to the original
first law. This is the marginal mass identity in the source's Step 2 before
the residual product coupling is introduced.
-/
theorem common_add_excess_euclideanDyadicCubeShellLaw (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    countableMixtureMeasure
      (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell))
      (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) +
    countableMixtureMeasure (euclideanDyadicCubeShellExcessMass dimension mu nu)
      (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) = mu := by
  calc
    countableMixtureMeasure
        (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell))
        (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) +
      countableMixtureMeasure (euclideanDyadicCubeShellExcessMass dimension mu nu)
        (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) =
      Measure.sum (fun shell =>
        euclideanDyadicCubeShellMass dimension mu shell •
          (euclideanDyadicCubeShellLaw dimension shell mu :
            Measure (EuclideanSpace ℝ (Fin dimension)))) := by
      ext s hs
      simp only [countableMixtureMeasure, Measure.add_apply, Measure.sum_apply _ hs,
        Measure.smul_apply, smul_eq_mul]
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro shell
      unfold euclideanDyadicCubeShellExcessMass
      rw [← add_mul]
      congr 1
      rw [add_comm]
      exact tsub_add_cancel_of_le (min_le_left _ _)
    _ = mu := measure_sum_shellMass_smul_euclideanDyadicCubeShellLaw dimension mu

/--
With positive residual mass, the common-shell mixture plus the normalized
residual law has exactly the original first marginal.
-/
theorem common_add_residual_euclideanDyadicCubeShellLawOfNonzero (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0) :
    countableMixtureMeasure
      (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell))
      (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) +
    euclideanDyadicCubeShellResidualMass dimension mu nu •
      (euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hresidual_ne_zero :
        Measure (EuclideanSpace ℝ (Fin dimension))) = mu := by
  rw [smul_euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hresidual_ne_zero]
  exact common_add_excess_euclideanDyadicCubeShellLaw dimension mu nu

/--
With positive residual mass, the residual-plus-common probability mixture has
the original first law as its marginal measure.
-/
theorem residualMixtureProbability_euclideanDyadicCubeShellLawOfNonzero_eq (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0) :
    countableMixtureProbability
      (residualMixtureWeight
        (euclideanDyadicCubeShellResidualMass dimension mu nu)
        (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell)))
      (residualMixtureLaw
        (euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hresidual_ne_zero)
        (fun shell => euclideanDyadicCubeShellLaw dimension shell mu))
      (by simpa [euclideanDyadicCubeShellResidualMass] using
        hasSum_euclideanDyadicCubeShellResidualMixtureWeight dimension mu nu) = mu := by
  apply Subtype.ext
  change countableMixtureMeasure _ _ = (mu : Measure (EuclideanSpace ℝ (Fin dimension)))
  rw [countableMixtureMeasure_residualMixtureLaw, add_comm]
  exact common_add_residual_euclideanDyadicCubeShellLawOfNonzero
    dimension mu nu hresidual_ne_zero

/--
With the common weight orientation fixed by `mu`, the corresponding
residual-plus-common mixture has `nu` as its marginal whenever `nu`'s
residual normalization is defined.
-/
theorem residualMixtureProbability_euclideanDyadicCubeShellLawOfNonzero_eq_second
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_ne_zero : euclideanDyadicCubeShellResidualMass dimension nu mu ≠ 0) :
    countableMixtureProbability
      (residualMixtureWeight
        (euclideanDyadicCubeShellResidualMass dimension mu nu)
        (fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell)))
      (residualMixtureLaw
        (euclideanDyadicCubeShellResidualLawOfNonzero dimension nu mu hresidual_ne_zero)
        (fun shell => euclideanDyadicCubeShellLaw dimension shell nu))
      (by simpa [euclideanDyadicCubeShellResidualMass] using
        hasSum_euclideanDyadicCubeShellResidualMixtureWeight dimension mu nu) = nu := by
  apply Subtype.ext
  change countableMixtureMeasure _ _ = (nu : Measure (EuclideanSpace ℝ (Fin dimension)))
  rw [countableMixtureMeasure_residualMixtureLaw]
  rw [euclideanDyadicCubeShellResidualMass_comm dimension mu nu,
    euclideanDyadicCubeShellCommonWeight_comm dimension mu nu, add_comm]
  exact common_add_residual_euclideanDyadicCubeShellLawOfNonzero
    dimension nu mu hresidual_ne_zero

/--
The source Step 2 coupling in the positive-residual case: it joins arbitrary
within-shell couplings at their common masses to the independent product of
the two normalized residual laws. Its two marginals are exactly `mu` and `nu`.
No transport-cost estimate is asserted here.
-/
noncomputable def euclideanDyadicCubeShellCouplingOfNonzeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0)
    (hnu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension nu mu ≠ 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling mu nu := by
  let commonWeight := fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell)
  let residualWeight := euclideanDyadicCubeShellResidualMass dimension mu nu
  let weight := residualMixtureWeight residualWeight commonWeight
  have hweight : HasSum weight 1 := by
    simpa [weight, residualWeight, commonWeight, euclideanDyadicCubeShellResidualMass] using
      hasSum_euclideanDyadicCubeShellResidualMixtureWeight dimension mu nu
  let residualMu := euclideanDyadicCubeShellResidualLawOfNonzero
    dimension mu nu hmu_residual_ne_zero
  let residualNu := euclideanDyadicCubeShellResidualLawOfNonzero
    dimension nu mu hnu_residual_ne_zero
  let mixture := residualMixtureCoupling commonWeight
    (euclideanDyadicCubeShellCommonMass dimension mu nu) hweight
    residualMu residualNu
    (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
    (fun shell => euclideanDyadicCubeShellLaw dimension shell nu)
    (ProbabilityCoupling.independent residualMu residualNu) localCoupling
  have hmu :
      countableMixtureProbability weight
        (residualMixtureLaw residualMu
          (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)) hweight = mu := by
    simpa [weight, residualWeight, commonWeight, residualMu,
      euclideanDyadicCubeShellResidualMass] using
      residualMixtureProbability_euclideanDyadicCubeShellLawOfNonzero_eq
        dimension mu nu hmu_residual_ne_zero
  have hnu :
      countableMixtureProbability weight
        (residualMixtureLaw residualNu
          (fun shell => euclideanDyadicCubeShellLaw dimension shell nu)) hweight = nu := by
    simpa [weight, residualWeight, commonWeight, residualNu,
      euclideanDyadicCubeShellResidualMass] using
      residualMixtureProbability_euclideanDyadicCubeShellLawOfNonzero_eq_second
        dimension mu nu hnu_residual_ne_zero
  exact hmu ▸ hnu ▸ mixture

/--
When the source residual mass vanishes, every shell mass is common. Thus the
countable mixture of local shell couplings itself has the two original laws as
marginals; no residual product component is needed.
-/
noncomputable def euclideanDyadicCubeShellCouplingOfZeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_zero : euclideanDyadicCubeShellResidualMass dimension mu nu = 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling mu nu := by
  let commonWeight := fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell)
  have hcommonMass : euclideanDyadicCubeShellCommonMass dimension mu nu = 1 := by
    apply le_antisymm (euclideanDyadicCubeShellCommonMass_le_one dimension mu nu)
    unfold euclideanDyadicCubeShellResidualMass at hresidual_zero
    exact tsub_eq_zero_iff_le.mp hresidual_zero
  have hweight : HasSum commonWeight 1 := by
    simpa [commonWeight, hcommonMass] using
      hasSum_euclideanDyadicCubeShellCommonMass dimension mu nu
  have hmu_excess_zero : ∀ shell,
      euclideanDyadicCubeShellExcessMass dimension mu nu shell = 0 := by
    apply ENNReal.tsum_eq_zero.mp
    rw [(hasSum_euclideanDyadicCubeShellExcessMass dimension mu nu).tsum_eq]
    simpa [euclideanDyadicCubeShellResidualMass] using hresidual_zero
  have hnu_residual_zero : euclideanDyadicCubeShellResidualMass dimension nu mu = 0 := by
    rw [← euclideanDyadicCubeShellResidualMass_comm dimension mu nu]
    exact hresidual_zero
  have hnu_excess_zero : ∀ shell,
      euclideanDyadicCubeShellExcessMass dimension nu mu shell = 0 := by
    apply ENNReal.tsum_eq_zero.mp
    rw [(hasSum_euclideanDyadicCubeShellExcessMass dimension nu mu).tsum_eq]
    simpa [euclideanDyadicCubeShellResidualMass] using hnu_residual_zero
  have hcommon_mu : commonWeight = fun shell =>
      euclideanDyadicCubeShellMass dimension mu shell := by
    funext shell
    apply le_antisymm (min_le_left _ _)
    exact tsub_eq_zero_iff_le.mp (hmu_excess_zero shell)
  have hcommon_nu : commonWeight = fun shell =>
      euclideanDyadicCubeShellMass dimension nu shell := by
    funext shell
    change min (euclideanDyadicCubeShellMass dimension mu shell)
      (euclideanDyadicCubeShellMass dimension nu shell) = _
    rw [show min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) =
      min (euclideanDyadicCubeShellMass dimension nu shell)
        (euclideanDyadicCubeShellMass dimension mu shell) by exact min_comm _ _]
    apply le_antisymm (min_le_left _ _)
    exact tsub_eq_zero_iff_le.mp (hnu_excess_zero shell)
  let mixture := countableMixtureCoupling commonWeight hweight
    (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
    (fun shell => euclideanDyadicCubeShellLaw dimension shell nu) localCoupling
  have hmu : countableMixtureProbability commonWeight
      (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) hweight = mu := by
    apply Subtype.ext
    change countableMixtureMeasure _ _ =
      (mu : Measure (EuclideanSpace ℝ (Fin dimension)))
    rw [hcommon_mu]
    exact measure_sum_shellMass_smul_euclideanDyadicCubeShellLaw dimension mu
  have hnu : countableMixtureProbability commonWeight
      (fun shell => euclideanDyadicCubeShellLaw dimension shell nu) hweight = nu := by
    apply Subtype.ext
    change countableMixtureMeasure _ _ =
      (nu : Measure (EuclideanSpace ℝ (Fin dimension)))
    rw [hcommon_nu]
    exact measure_sum_shellMass_smul_euclideanDyadicCubeShellLaw dimension nu
  exact hmu ▸ hnu ▸ mixture

/--
When residual mass is zero, the source shell construction has no cross-shell
term: W₁ is bounded by the common shell-mass weighted sum of the supplied
within-shell coupling costs.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_cost_of_zeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hresidual_zero : euclideanDyadicCubeShellResidualMass dimension mu nu = 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) *
        (localCoupling shell).cost (fun z => edist z.1 z.2) := by
  let weight := fun shell => euclideanDyadicCubeShellMass dimension mu shell
  have hweight : HasSum weight 1 := by
    simpa [weight] using hasSum_measure_euclideanDyadicCubeShell dimension mu
  let mixture := countableMixtureCoupling weight hweight
    (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
    (fun shell => euclideanDyadicCubeShellLaw dimension shell nu) localCoupling
  have hmu : countableMixtureProbability weight
      (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) hweight = mu := by
    apply Subtype.ext
    change countableMixtureMeasure _ _ =
      (mu : Measure (EuclideanSpace ℝ (Fin dimension)))
    simpa [weight] using measure_sum_shellMass_smul_euclideanDyadicCubeShellLaw dimension mu
  have hweight_nu : weight = fun shell => euclideanDyadicCubeShellMass dimension nu shell := by
    funext shell
    exact euclideanDyadicCubeShellMass_eq_of_residualMass_eq_zero
      dimension mu nu hresidual_zero shell
  have hnu : countableMixtureProbability weight
      (fun shell => euclideanDyadicCubeShellLaw dimension shell nu) hweight = nu := by
    apply Subtype.ext
    change countableMixtureMeasure _ _ =
      (nu : Measure (EuclideanSpace ℝ (Fin dimension)))
    rw [hweight_nu]
    exact measure_sum_shellMass_smul_euclideanDyadicCubeShellLaw dimension nu
  calc
    ProbabilityCoupling.wassersteinOne mu nu =
        ProbabilityCoupling.wassersteinOne
          (countableMixtureProbability weight
            (fun shell => euclideanDyadicCubeShellLaw dimension shell mu) hweight)
          (countableMixtureProbability weight
            (fun shell => euclideanDyadicCubeShellLaw dimension shell nu) hweight) := by
      rw [hmu, hnu]
    _ ≤ mixture.cost (fun z => edist z.1 z.2) :=
      ProbabilityCoupling.wassersteinOne_le_cost mixture
    _ = ∑' shell, weight shell * (localCoupling shell).cost (fun z => edist z.1 z.2) := by
      exact countableMixtureCoupling_cost weight hweight
        (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
        (fun shell => euclideanDyadicCubeShellLaw dimension shell nu) localCoupling
        (fun z => edist z.1 z.2)
    _ = _ := by
      apply tsum_congr
      intro shell
      change euclideanDyadicCubeShellMass dimension mu shell * _ = _
      rw [euclideanDyadicCubeShellMass_eq_of_residualMass_eq_zero
        dimension mu nu hresidual_zero shell, min_self]

/--
The full source-style shellwise coupling construction. It joins common shell
couplings and, when needed, the independent excess-law product. This provides
the coupling existence part of Fournier--Guillin Lemma 5, Step 2; the
quantitative transport-cost inequality is a separate obligation.
-/
noncomputable def euclideanDyadicCubeShellCoupling
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling mu nu := by
  by_cases hresidual_zero : euclideanDyadicCubeShellResidualMass dimension mu nu = 0
  · exact euclideanDyadicCubeShellCouplingOfZeroResidual
      dimension mu nu hresidual_zero localCoupling
  · exact euclideanDyadicCubeShellCouplingOfNonzeroResidual
      dimension mu nu hresidual_zero
      (by
        rw [← euclideanDyadicCubeShellResidualMass_comm dimension mu nu]
        exact hresidual_zero)
      localCoupling

/--
In the positive-residual case, the shellwise coupling gives this exact
Wasserstein-one upper bound: a weighted sum of local costs plus the cost of
the independent residual product. This is a coupling-cost identity followed
by the primal W₁ infimum bound, not yet the source's geometric estimate of
the residual term.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_cost_of_nonzeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0)
    (hnu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension nu mu ≠ 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      euclideanDyadicCubeShellResidualMass dimension mu nu *
        (ProbabilityCoupling.independent
          (euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hmu_residual_ne_zero)
          (euclideanDyadicCubeShellResidualLawOfNonzero dimension nu mu hnu_residual_ne_zero)).cost
            (fun z => edist z.1 z.2) +
      ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) *
        (localCoupling shell).cost (fun z => edist z.1 z.2) := by
  let commonWeight := fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell)
  let commonMass := euclideanDyadicCubeShellCommonMass dimension mu nu
  let hweight : HasSum (residualMixtureWeight (1 - commonMass) commonWeight) 1 := by
    simpa [commonMass, commonWeight] using
      hasSum_euclideanDyadicCubeShellResidualMixtureWeight dimension mu nu
  let residualMu := euclideanDyadicCubeShellResidualLawOfNonzero
    dimension mu nu hmu_residual_ne_zero
  let residualNu := euclideanDyadicCubeShellResidualLawOfNonzero
    dimension nu mu hnu_residual_ne_zero
  let mixture := residualMixtureCoupling commonWeight commonMass hweight
    residualMu residualNu
    (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
    (fun shell => euclideanDyadicCubeShellLaw dimension shell nu)
    (ProbabilityCoupling.independent residualMu residualNu) localCoupling
  have hmu :
      countableMixtureProbability (residualMixtureWeight (1 - commonMass) commonWeight)
        (residualMixtureLaw residualMu
          (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)) hweight = mu := by
    simpa [commonMass, commonWeight, residualMu,
      euclideanDyadicCubeShellResidualMass] using
      residualMixtureProbability_euclideanDyadicCubeShellLawOfNonzero_eq
        dimension mu nu hmu_residual_ne_zero
  have hnu :
      countableMixtureProbability (residualMixtureWeight (1 - commonMass) commonWeight)
        (residualMixtureLaw residualNu
          (fun shell => euclideanDyadicCubeShellLaw dimension shell nu)) hweight = nu := by
    simpa [commonMass, commonWeight, residualNu,
      euclideanDyadicCubeShellResidualMass] using
      residualMixtureProbability_euclideanDyadicCubeShellLawOfNonzero_eq_second
        dimension mu nu hnu_residual_ne_zero
  calc
    ProbabilityCoupling.wassersteinOne mu nu =
      ProbabilityCoupling.wassersteinOne
        (countableMixtureProbability (residualMixtureWeight (1 - commonMass) commonWeight)
          (residualMixtureLaw residualMu
            (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)) hweight)
        (countableMixtureProbability (residualMixtureWeight (1 - commonMass) commonWeight)
          (residualMixtureLaw residualNu
            (fun shell => euclideanDyadicCubeShellLaw dimension shell nu)) hweight) := by
          rw [hmu, hnu]
    _ ≤ mixture.cost (fun z => edist z.1 z.2) :=
      ProbabilityCoupling.wassersteinOne_le_cost mixture
    _ = _ := by
      simpa [mixture, commonMass, commonWeight, residualMu, residualNu,
        euclideanDyadicCubeShellResidualMass] using
        residualMixtureCoupling_cost commonWeight commonMass hweight residualMu residualNu
          (fun shell => euclideanDyadicCubeShellLaw dimension shell mu)
          (fun shell => euclideanDyadicCubeShellLaw dimension shell nu)
          (ProbabilityCoupling.independent residualMu residualNu) localCoupling
          (fun z => edist z.1 z.2)

/--
In the positive-residual case, the source-style shell coupling is controlled
by local coupling costs and the radial first moments of the two normalized
residual laws.  This is an exact transport interface; the still-open
source-specific step is to estimate those moments by the dyadic shell tails.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_residualMoments_of_nonzeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0)
    (hnu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension nu mu ≠ 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      euclideanDyadicCubeShellResidualMass dimension mu nu *
        ((∫⁻ x, edist x 0 ∂(euclideanDyadicCubeShellResidualLawOfNonzero
          dimension mu nu hmu_residual_ne_zero :
            Measure (EuclideanSpace ℝ (Fin dimension)))) +
          ∫⁻ y, edist 0 y ∂(euclideanDyadicCubeShellResidualLawOfNonzero
            dimension nu mu hnu_residual_ne_zero :
              Measure (EuclideanSpace ℝ (Fin dimension)))) +
      ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) *
        (localCoupling shell).cost (fun z => edist z.1 z.2) := by
  calc
    ProbabilityCoupling.wassersteinOne mu nu ≤
        euclideanDyadicCubeShellResidualMass dimension mu nu *
          (ProbabilityCoupling.independent
            (euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hmu_residual_ne_zero)
            (euclideanDyadicCubeShellResidualLawOfNonzero dimension nu mu hnu_residual_ne_zero)).cost
              (fun z => edist z.1 z.2) +
        ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell) *
          (localCoupling shell).cost (fun z => edist z.1 z.2) :=
      wassersteinOne_euclideanDyadicCubeShells_le_cost_of_nonzeroResidual
        dimension mu nu hmu_residual_ne_zero hnu_residual_ne_zero localCoupling
    _ ≤ _ := by
      apply add_le_add_left
      exact mul_le_mul_right (ProbabilityCoupling.independent_cost_edist_le_lintegral_edist_zero_add
        (euclideanDyadicCubeShellResidualLawOfNonzero dimension mu nu hmu_residual_ne_zero)
        (euclideanDyadicCubeShellResidualLawOfNonzero dimension nu mu hnu_residual_ne_zero)) _

/--
The complete positive-residual geometric part of the source's Step 2 shell
coupling.  It bounds the cross-shell residual product by the two weighted
excess-shell sums, while retaining arbitrary within-shell couplings.  The
subsequent source step is to choose/approximate local W₁ couplings and bound
their compact-coordinate costs; this theorem does not claim the final
Fournier--Guillin shell inequality.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_geometricCost_of_nonzeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0)
    (hnu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension nu mu ≠ 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      (∑' shell, euclideanDyadicCubeShellExcessMass dimension mu nu shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
      (∑' shell, euclideanDyadicCubeShellExcessMass dimension nu mu shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
      ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) *
        (localCoupling shell).cost (fun z => edist z.1 z.2) := by
  have hmu :=
    residualMass_mul_lintegral_edist_zero_euclideanDyadicCubeShellResidualLawOfNonzero_le
      dimension mu nu hmu_residual_ne_zero
  have hnu :=
    residualMass_mul_lintegral_edist_zero_euclideanDyadicCubeShellResidualLawOfNonzero_le
      dimension nu mu hnu_residual_ne_zero
  rw [← euclideanDyadicCubeShellResidualMass_comm dimension mu nu] at hnu
  calc
    ProbabilityCoupling.wassersteinOne mu nu ≤
        euclideanDyadicCubeShellResidualMass dimension mu nu *
          ((∫⁻ x, edist x 0 ∂(euclideanDyadicCubeShellResidualLawOfNonzero
            dimension mu nu hmu_residual_ne_zero :
              Measure (EuclideanSpace ℝ (Fin dimension)))) +
            ∫⁻ y, edist 0 y ∂(euclideanDyadicCubeShellResidualLawOfNonzero
              dimension nu mu hnu_residual_ne_zero :
                Measure (EuclideanSpace ℝ (Fin dimension)))) +
        ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell) *
          (localCoupling shell).cost (fun z => edist z.1 z.2) :=
      wassersteinOne_euclideanDyadicCubeShells_le_residualMoments_of_nonzeroResidual
        dimension mu nu hmu_residual_ne_zero hnu_residual_ne_zero localCoupling
    _ = (euclideanDyadicCubeShellResidualMass dimension mu nu *
          ∫⁻ x, edist x 0 ∂(euclideanDyadicCubeShellResidualLawOfNonzero
            dimension mu nu hmu_residual_ne_zero :
              Measure (EuclideanSpace ℝ (Fin dimension)))) +
        euclideanDyadicCubeShellResidualMass dimension mu nu *
          ∫⁻ y, edist 0 y ∂(euclideanDyadicCubeShellResidualLawOfNonzero
            dimension nu mu hnu_residual_ne_zero :
              Measure (EuclideanSpace ℝ (Fin dimension))) +
        ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell) *
          (localCoupling shell).cost (fun z => edist z.1 z.2) := by
      rw [mul_add, add_assoc]
    _ ≤ _ := by
      apply add_le_add_left
      exact add_le_add hmu (by simpa [edist_comm] using hnu)

/--
The source-style positive-residual shell-coupling bound with its two directed
excess sums combined into one unsigned shell-mass discrepancy sum.  Its
within-shell term still records the supplied local coupling costs, so it is a
checked Step 2 boundary rather than the final Fournier--Guillin inequality.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_discrepancyCost_of_nonzeroResidual
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension mu nu ≠ 0)
    (hnu_residual_ne_zero : euclideanDyadicCubeShellResidualMass dimension nu mu ≠ 0)
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      (∑' shell, euclideanDyadicCubeShellMassDiscrepancy dimension mu nu shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
      ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) *
        (localCoupling shell).cost (fun z => edist z.1 z.2) := by
  calc
    ProbabilityCoupling.wassersteinOne mu nu ≤
        (∑' shell, euclideanDyadicCubeShellExcessMass dimension mu nu shell *
          ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
        (∑' shell, euclideanDyadicCubeShellExcessMass dimension nu mu shell *
          ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
        ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell) *
          (localCoupling shell).cost (fun z => edist z.1 z.2) :=
      wassersteinOne_euclideanDyadicCubeShells_le_geometricCost_of_nonzeroResidual
        dimension mu nu hmu_residual_ne_zero hnu_residual_ne_zero localCoupling
    _ = _ := by
      rw [tsum_euclideanDyadicCubeShellExcessMass_mul_radius_add]

/--
For arbitrary source cube-shell masses, the full Step 2 shell coupling bounds
W₁ by its weighted unsigned shell-mass discrepancy and the weighted supplied
within-shell coupling costs.  This is the completed countable coupling/cost
boundary. It deliberately does not replace those supplied local costs with
local W₁ infima or assert Fournier--Guillin concentration.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_discrepancyCost
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (localCoupling : ∀ shell, ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      (∑' shell, euclideanDyadicCubeShellMassDiscrepancy dimension mu nu shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
      ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) *
        (localCoupling shell).cost (fun z => edist z.1 z.2) := by
  by_cases hresidual_zero : euclideanDyadicCubeShellResidualMass dimension mu nu = 0
  · calc
      ProbabilityCoupling.wassersteinOne mu nu ≤
          ∑' shell, min (euclideanDyadicCubeShellMass dimension mu shell)
            (euclideanDyadicCubeShellMass dimension nu shell) *
            (localCoupling shell).cost (fun z => edist z.1 z.2) :=
        wassersteinOne_euclideanDyadicCubeShells_le_cost_of_zeroResidual
          dimension mu nu hresidual_zero localCoupling
      _ ≤ _ := self_le_add_left _ _
  · exact wassersteinOne_euclideanDyadicCubeShells_le_discrepancyCost_of_nonzeroResidual
      dimension mu nu hresidual_zero
      (by
        rw [← euclideanDyadicCubeShellResidualMass_comm dimension mu nu]
        exact hresidual_zero)
      localCoupling

/--
If the common source-shell mass is supported on a finite shell family, the
completed shell-cost boundary can use the actual local W₁ infima rather than
supplied local couplings.  No local optimal coupling is postulated: the proof
takes the finite infimum of independently chosen local couplings, which is
the form relevant once one argument is an empirical law.

Library provenance: this specializes the local checked
`iInf_fintype_weighted_sum`; the finite-support rewrite directly uses
Mathlib's `tsum_eq_sum` from
[`Topology/Algebra/InfiniteSum/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean),
`ProbabilityMeasure.apply_le_one` from
[`MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean),
and the finite-subtype sum conversion from
[`Algebra/BigOperators/Group/Finset/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean),
all at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_discrepancyWasserstein_of_finiteSupport
    (dimension : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (support : Finset ℕ)
    (hsupport : ∀ shell ∉ support,
      min (euclideanDyadicCubeShellMass dimension mu shell)
        (euclideanDyadicCubeShellMass dimension nu shell) = 0) :
    ProbabilityCoupling.wassersteinOne mu nu ≤
      (∑' shell, euclideanDyadicCubeShellMassDiscrepancy dimension mu nu shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
      ∑ shell ∈ support,
        min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension nu shell) *
          ProbabilityCoupling.wassersteinOne
            (euclideanDyadicCubeShellLaw dimension shell mu)
            (euclideanDyadicCubeShellLaw dimension shell nu) := by
  classical
  let commonWeight := fun shell => min (euclideanDyadicCubeShellMass dimension mu shell)
    (euclideanDyadicCubeShellMass dimension nu shell)
  let discrepancy := ∑' shell, euclideanDyadicCubeShellMassDiscrepancy dimension mu nu shell *
    ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)
  let LocalCoupling : Type := ∀ shell : {shell // shell ∈ support},
    ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)
  letI : Nonempty LocalCoupling := ⟨fun shell => ProbabilityCoupling.independent _ _⟩
  have hcost : ∀ localCoupling : LocalCoupling,
      ProbabilityCoupling.wassersteinOne mu nu ≤ discrepancy +
        ∑ shell : {shell // shell ∈ support}, commonWeight shell *
          (localCoupling shell).cost (fun z => edist z.1 z.2) := by
    intro localCoupling
    let selectedCoupling : ∀ shell, ProbabilityCoupling
        (euclideanDyadicCubeShellLaw dimension shell mu)
        (euclideanDyadicCubeShellLaw dimension shell nu) := fun shell =>
      if hmem : shell ∈ support then localCoupling ⟨shell, hmem⟩
      else ProbabilityCoupling.independent _ _
    have hzero : ∀ shell ∉ support,
        commonWeight shell * (selectedCoupling shell).cost (fun z => edist z.1 z.2) = 0 := by
      intro shell hnotmem
      simp [commonWeight, selectedCoupling, hnotmem, hsupport shell hnotmem]
    calc
      ProbabilityCoupling.wassersteinOne mu nu ≤ discrepancy +
          ∑' shell, commonWeight shell *
            (selectedCoupling shell).cost (fun z => edist z.1 z.2) := by
        simpa [discrepancy, commonWeight] using
          wassersteinOne_euclideanDyadicCubeShells_le_discrepancyCost
            dimension mu nu selectedCoupling
      _ = discrepancy + ∑ shell : {shell // shell ∈ support}, commonWeight shell *
            (localCoupling shell).cost (fun z => edist z.1 z.2) := by
        rw [tsum_eq_sum hzero, ← Finset.sum_coe_sort]
        apply congrArg (discrepancy + ·)
        apply Finset.sum_congr rfl
        intro shell hmem
        simp [selectedCoupling, shell.property]
  have hweight_ne_top : ∀ shell : {shell // shell ∈ support}, commonWeight shell ≠ ∞ := by
    intro shell
    apply ne_of_lt
    apply lt_of_le_of_lt
    · apply (min_le_left _ _).trans
      change euclideanDyadicCubeShellMass dimension mu shell ≤ 1
      unfold euclideanDyadicCubeShellMass
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact ENNReal.coe_le_coe.mpr (ProbabilityMeasure.apply_le_one mu _)
    · exact ENNReal.one_lt_top
  letI : ∀ shell : {shell // shell ∈ support}, Nonempty (ProbabilityCoupling
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu)) := fun shell =>
    ⟨ProbabilityCoupling.independent _ _⟩
  calc
    ProbabilityCoupling.wassersteinOne mu nu ≤
        ⨅ localCoupling : LocalCoupling, discrepancy +
          ∑ shell : {shell // shell ∈ support}, commonWeight shell *
            (localCoupling shell).cost (fun z => edist z.1 z.2) :=
      le_iInf hcost
    _ = discrepancy + ⨅ localCoupling : LocalCoupling,
          ∑ shell : {shell // shell ∈ support}, commonWeight shell *
            (localCoupling shell).cost (fun z => edist z.1 z.2) := by
      exact ENNReal.add_iInf.symm
    _ = discrepancy + ∑ shell : {shell // shell ∈ support}, commonWeight shell *
          ⨅ coupling : ProbabilityCoupling
            (euclideanDyadicCubeShellLaw dimension shell mu)
            (euclideanDyadicCubeShellLaw dimension shell nu),
            coupling.cost (fun z => edist z.1 z.2) := by
      congr 1
      exact iInf_fintype_weighted_sum
        (fun shell : {shell // shell ∈ support} => ProbabilityCoupling
          (euclideanDyadicCubeShellLaw dimension shell mu)
          (euclideanDyadicCubeShellLaw dimension shell nu))
        (fun shell => commonWeight shell) hweight_ne_top
        (fun shell coupling => coupling.cost (fun z => edist z.1 z.2))
    _ = _ := by
      congr 1
      calc
        (∑ shell : {shell // shell ∈ support}, commonWeight shell *
          ⨅ coupling : ProbabilityCoupling
            (euclideanDyadicCubeShellLaw dimension shell mu)
            (euclideanDyadicCubeShellLaw dimension shell nu),
            coupling.cost (fun z => edist z.1 z.2)) =
            ∑ shell : {shell // shell ∈ support}, commonWeight shell *
              ProbabilityCoupling.wassersteinOne
                (euclideanDyadicCubeShellLaw dimension shell mu)
                (euclideanDyadicCubeShellLaw dimension shell nu) := by
          apply Finset.sum_congr rfl
          intro shell hmem
          unfold ProbabilityCoupling.wassersteinOne ProbabilityCoupling.transportCost
          rw [sInf_range]
        _ = ∑ shell ∈ support, commonWeight shell *
              ProbabilityCoupling.wassersteinOne
                (euclideanDyadicCubeShellLaw dimension shell mu)
                (euclideanDyadicCubeShellLaw dimension shell nu) :=
          Finset.sum_coe_sort support (fun shell => commonWeight shell *
            ProbabilityCoupling.wassersteinOne
              (euclideanDyadicCubeShellLaw dimension shell mu)
              (euclideanDyadicCubeShellLaw dimension shell nu))
        _ = _ := by rfl

/--
The finite-local-W₁ source-shell inequality specialized to a nonempty finite
empirical sample. The finite shell family is the image of the selected source
shell indices of the sample points; no compact local optimizer is assumed.
-/
theorem wassersteinOne_euclideanDyadicCubeShells_le_discrepancyWasserstein_empirical
    {count : ℕ} [Nonempty (Fin count)] (dimension : ℕ)
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (sample : Fin count → EuclideanSpace ℝ (Fin dimension)) :
    ProbabilityCoupling.wassersteinOne mu (empiricalSampleProbabilityMeasure sample) ≤
      (∑' shell, euclideanDyadicCubeShellMassDiscrepancy dimension mu
        (empiricalSampleProbabilityMeasure sample) shell *
        ENNReal.ofReal (Real.sqrt dimension * euclideanDyadicCubeRadius shell)) +
      ∑ shell ∈ empiricalEuclideanDyadicCubeShellSupport dimension sample,
        min (euclideanDyadicCubeShellMass dimension mu shell)
          (euclideanDyadicCubeShellMass dimension (empiricalSampleProbabilityMeasure sample) shell) *
          ProbabilityCoupling.wassersteinOne
            (euclideanDyadicCubeShellLaw dimension shell mu)
            (euclideanDyadicCubeShellLaw dimension shell
              (empiricalSampleProbabilityMeasure sample)) := by
  apply wassersteinOne_euclideanDyadicCubeShells_le_discrepancyWasserstein_of_finiteSupport
    dimension mu (empiricalSampleProbabilityMeasure sample)
    (empiricalEuclideanDyadicCubeShellSupport dimension sample)
  exact euclideanDyadicCubeShellCommonMass_finiteSupport_of_empirical dimension mu sample

/-- On a nonzero source shell, normalization is inverse shell mass times restriction. -/
theorem euclideanDyadicCubeShellLaw_toMeasure_eq_of_nonzero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hnonzero : law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    (euclideanDyadicCubeShellLaw dimension shell law :
      Measure (EuclideanSpace ℝ (Fin dimension))) =
      (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)).mass⁻¹ •
        (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) :
          Measure (EuclideanSpace ℝ (Fin dimension))) := by
  unfold euclideanDyadicCubeShellLaw
  exact FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hnonzero

/--
The source conditional shell law in compact coordinates. It normalizes the
finite restricted measure *after* the chosen measurable extension of the
coordinate scale; the extension agrees with the exact source map on the shell.
-/
noncomputable def euclideanDyadicCubeShellCompactLaw (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    ProbabilityMeasure (HalfOpenUnitCube dimension) := by
  letI : Nonempty (HalfOpenUnitCube dimension) := ⟨halfOpenUnitCubeOrigin dimension⟩
  exact ((law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)).map
    (euclideanDyadicCubeShellScaleExtension dimension shell)).normalize

/--
On a nonzero shell, the compact-coordinate law is exactly the pushforward of
the normalized shell law. Thus the choice of the global measurable extension
does not alter the source coordinate scaling on mass-carrying shell points.
-/
theorem euclideanDyadicCubeShellCompactLaw_eq_map_shellLaw_of_nonzero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hnonzero : law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    euclideanDyadicCubeShellCompactLaw dimension shell law =
      (euclideanDyadicCubeShellLaw dimension shell law).map
        (measurable_euclideanDyadicCubeShellScaleExtension dimension shell).aemeasurable := by
  let μ := law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)
  let f := euclideanDyadicCubeShellScaleExtension dimension shell
  have hf : Measurable f :=
    measurable_euclideanDyadicCubeShellScaleExtension dimension shell
  have hmass : (μ.map f).mass = μ.mass := by
    simp only [FiniteMeasure.mass]
    rw [FiniteMeasure.map_apply μ hf MeasurableSet.univ]
    simp
  have hμ : μ ≠ 0 := by
    simpa [μ] using hnonzero
  have hmap : μ.map f ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff, hmass]
    exact (FiniteMeasure.mass_nonzero_iff μ).mpr hμ
  letI : Nonempty (HalfOpenUnitCube dimension) := ⟨halfOpenUnitCubeOrigin dimension⟩
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  simp only [euclideanDyadicCubeShellCompactLaw, euclideanDyadicCubeShellLaw]
  rw [ProbabilityMeasure.map_apply _
    (measurable_euclideanDyadicCubeShellScaleExtension dimension shell).aemeasurable hs]
  change
    ((law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)).map
      (euclideanDyadicCubeShellScaleExtension dimension shell)).normalize s =
    (law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)).normalize
      ((euclideanDyadicCubeShellScaleExtension dimension shell) ⁻¹' s)
  rw [FiniteMeasure.normalize_eq_of_nonzero _ hmap s,
    FiniteMeasure.normalize_eq_of_nonzero _ hμ (f ⁻¹' s),
    FiniteMeasure.map_apply μ hf hs, hmass]

/--
The measurable compact-coordinate extension maps the ambient law conditioned
on a positive source shell to that shell's compact law.

This composes the local conditional-shell identity with the local compact-law
pushforward identity; it introduces no new upstream Lean dependency or source
material.
-/
theorem map_cond_euclideanDyadicCubeShell_eq_compactLaw_of_nonzero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hnonzero : law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    Measure.map (euclideanDyadicCubeShellScaleExtension dimension shell)
      (ProbabilityTheory.cond (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (euclideanDyadicCubeShell dimension shell)) =
      (euclideanDyadicCubeShellCompactLaw dimension shell law :
        Measure (HalfOpenUnitCube dimension)) := by
  rw [cond_eq_euclideanDyadicCubeShellLaw_of_nonzero dimension shell law hnonzero]
  have hcompact := euclideanDyadicCubeShellCompactLaw_eq_map_shellLaw_of_nonzero
    dimension shell law hnonzero
  change Measure.map (euclideanDyadicCubeShellScaleExtension dimension shell)
      (euclideanDyadicCubeShellLaw dimension shell law :
        Measure (EuclideanSpace ℝ (Fin dimension))) =
      (euclideanDyadicCubeShellCompactLaw dimension shell law :
        Measure (HalfOpenUnitCube dimension))
  rw [hcompact]
  rfl

/--
For every positive fixed source-shell membership pattern, enumerating the
selected observations and moving them to compact shell coordinates has exactly
the finite iid compact-shell law. This is the probabilistic resampling bridge
needed before a fixed-length compact empirical-W₁ theorem can be applied.

It composes local conditional-IID and conditional-shell pushforward results;
no new upstream Lean dependency or source material is introduced.
-/
theorem map_finiteIIDCompactShellSample_conditioned
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (count : ℕ) (inside : Finset (Fin count))
    (hpattern : ∀ index : Fin count,
      (law : Measure (EuclideanSpace ℝ (Fin dimension)))
        (if index ∈ inside then euclideanDyadicCubeShell dimension shell
          else (euclideanDyadicCubeShell dimension shell)ᶜ) ≠ 0)
    (hnonzero : law.toFiniteMeasure.restrict
      (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    Measure.map
      (finiteIIDSampleMap (euclideanDyadicCubeShellScaleExtension dimension shell) ∘
        finiteIIDSampleOnFinsetToFin inside)
      (ProbabilityTheory.cond
        (finiteIIDSampleLaw (law : Measure (EuclideanSpace ℝ (Fin dimension))) count)
        (finiteIIDMembershipPattern count inside
          (euclideanDyadicCubeShell dimension shell))) =
      finiteIIDSampleLaw
        (euclideanDyadicCubeShellCompactLaw dimension shell law :
          Measure (HalfOpenUnitCube dimension)) inside.card := by
  have hs_nonzero : (law : Measure (EuclideanSpace ℝ (Fin dimension)))
      (euclideanDyadicCubeShell dimension shell) ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [FiniteMeasure.restrict_eq_zero_iff]
    apply ENNReal.coe_eq_zero.mp
    simpa using hzero
  have hmap := map_finiteIIDSampleMapOnFinsetToFin_conditioned
    (law : Measure (EuclideanSpace ℝ (Fin dimension))) count inside
    (euclideanDyadicCubeShell dimension shell)
    (measurableSet_euclideanDyadicCubeShell dimension shell) hs_nonzero hpattern
    (euclideanDyadicCubeShellScaleExtension dimension shell)
    (measurable_euclideanDyadicCubeShellScaleExtension dimension shell)
  rw [map_cond_euclideanDyadicCubeShell_eq_compactLaw_of_nonzero
    dimension shell law hnonzero] at hmap
  exact hmap

/--
For every realized nonempty source shell, scaling its canonically enumerated
empirical sub-sample has exactly the compact empirical shell law.  This is a
deterministic identity: the preceding conditional-IID theorem supplies its
probabilistic counterpart for a fixed membership pattern.

It composes local empirical reindexing, normalization, and compact-shell-map
lemmas; no new upstream Lean dependency or source material is introduced.
-/
theorem empiricalCompactShellSample_eq_compactLaw
    {count : ℕ} [Nonempty (Fin count)]
    (dimension shell : ℕ)
    (sample : Fin count → EuclideanSpace ℝ (Fin dimension))
    (hselected : (empiricalSampleIndicesInSet sample
      (euclideanDyadicCubeShell dimension shell)).Nonempty) :
    empiricalSampleProbabilityMeasureOfPos (Finset.card_pos.mpr hselected)
      (finiteIIDSampleMap (euclideanDyadicCubeShellScaleExtension dimension shell)
        (finiteIIDSampleOnFinsetToFin
          (empiricalSampleIndicesInSet sample
            (euclideanDyadicCubeShell dimension shell)) sample)) =
      euclideanDyadicCubeShellCompactLaw dimension shell
        (empiricalSampleProbabilityMeasure sample) := by
  let s := euclideanDyadicCubeShell dimension shell
  let inside := empiricalSampleIndicesInSet sample s
  have hselected_s : (empiricalSampleIndicesInSet sample s).Nonempty := by
    simpa only [s] using hselected
  have hrestrict : (empiricalSampleProbabilityMeasure sample).toFiniteMeasure.restrict s ≠ 0 :=
    empiricalSampleProbabilityMeasure_restrict_ne_zero sample s
      (measurableSet_euclideanDyadicCubeShell dimension shell) hselected_s
  change empiricalSampleProbabilityMeasureOfPos (Finset.card_pos.mpr hselected)
      ((euclideanDyadicCubeShellScaleExtension dimension shell) ∘
        finiteIIDSampleOnFinsetToFin inside sample) = _
  rw [← map_empiricalSampleProbabilityMeasureOfPos
    (Finset.card_pos.mpr hselected) (finiteIIDSampleOnFinsetToFin inside sample)
    (euclideanDyadicCubeShellScaleExtension dimension shell)
    (measurable_euclideanDyadicCubeShellScaleExtension dimension shell)]
  rw [empiricalSampleProbabilityMeasure_finiteIIDSampleOnFinsetToFin sample s hselected_s]
  rw [← empiricalSelectedSampleProbabilityMeasure_eq_normalize_restrict sample s
    (measurableSet_euclideanDyadicCubeShell dimension shell) hselected_s]
  rw [euclideanDyadicCubeShellCompactLaw_eq_map_shellLaw_of_nonzero
    dimension shell (empiricalSampleProbabilityMeasure sample) hrestrict]
  rfl

/--
Scaling the exact compact-coordinate shell law back recovers the normalized
source shell law, on every nonzero shell.
-/
theorem map_euclideanDyadicCubeScaleBack_compactLaw_eq_shellLaw_of_nonzero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hnonzero : law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    (euclideanDyadicCubeShellCompactLaw dimension shell law).map
      (measurable_euclideanDyadicCubeScaleBack dimension shell).aemeasurable =
      euclideanDyadicCubeShellLaw dimension shell law := by
  rw [euclideanDyadicCubeShellCompactLaw_eq_map_shellLaw_of_nonzero dimension shell law hnonzero]
  let μ := law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell)
  let f := euclideanDyadicCubeShellScaleExtension dimension shell
  let g := euclideanDyadicCubeScaleBack dimension shell
  have hμ : μ ≠ 0 := by
    simpa [μ] using hnonzero
  have hf : Measurable f :=
    measurable_euclideanDyadicCubeShellScaleExtension dimension shell
  have hg : Measurable g := measurable_euclideanDyadicCubeScaleBack dimension shell
  have hgf : (g ∘ f) =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin dimension)))] id := by
    change ∀ᵐ x ∂(law.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) :
      Measure (EuclideanSpace ℝ (Fin dimension))), (g ∘ f) x = id x
    filter_upwards [ae_restrict_mem
      (measurableSet_euclideanDyadicCubeShell dimension shell)] with x hx
    change euclideanDyadicCubeScaleBack dimension shell
      (euclideanDyadicCubeShellScaleExtension dimension shell x) = x
    rw [euclideanDyadicCubeShellScaleExtension_eq_scale dimension shell ⟨x, hx⟩]
    exact euclideanDyadicCubeScaleBack_euclideanDyadicCubeShellScale dimension shell ⟨x, hx⟩
  have hmapMeasure : (μ : Measure (EuclideanSpace ℝ (Fin dimension))).map (g ∘ f) = μ := by
    rw [Measure.map_congr hgf, Measure.map_id]
  have hvalue (s : Set (EuclideanSpace ℝ (Fin dimension))) (hs : MeasurableSet s) :
      μ ((g ∘ f) ⁻¹' s) = μ s := by
    rw [← FiniteMeasure.map_apply μ (hg.comp hf) hs]
    apply ENNReal.coe_injective
    simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      FiniteMeasure.toMeasure_map] using
      congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin dimension)) => ν s) hmapMeasure
  letI : Nonempty (HalfOpenUnitCube dimension) := ⟨halfOpenUnitCubeOrigin dimension⟩
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  rw [ProbabilityMeasure.map_apply _
    (measurable_euclideanDyadicCubeScaleBack dimension shell).aemeasurable hs,
    ProbabilityMeasure.map_apply _
      (measurable_euclideanDyadicCubeShellScaleExtension dimension shell).aemeasurable
      ((measurable_euclideanDyadicCubeScaleBack dimension shell) hs)]
  simp only [euclideanDyadicCubeShellLaw]
  change μ.normalize ((g ∘ f) ⁻¹' s) = μ.normalize s
  rw [FiniteMeasure.normalize_eq_of_nonzero _ hμ ((g ∘ f) ⁻¹' s),
    FiniteMeasure.normalize_eq_of_nonzero _ hμ s, hvalue s hs]

/--
The exact source shell laws inherit the `2^shell` W₁ scale-back factor from
their compact-coordinate normalizations. This is a within-shell statement;
it does not yet couple mass across distinct shells.
-/
theorem wassersteinOne_euclideanDyadicCubeShellLaw_le
    (dimension shell : ℕ)
    (mu nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmu : mu.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) ≠ 0)
    (hnu : nu.toFiniteMeasure.restrict (euclideanDyadicCubeShell dimension shell) ≠ 0) :
    ProbabilityCoupling.wassersteinOne
      (euclideanDyadicCubeShellLaw dimension shell mu)
      (euclideanDyadicCubeShellLaw dimension shell nu) ≤
      ((NNReal.mk (euclideanDyadicCubeRadius shell)
        (euclideanDyadicCubeRadius_pos shell).le : NNReal) : ℝ≥0∞) *
        ProbabilityCoupling.wassersteinOne
          (euclideanDyadicCubeShellCompactLaw dimension shell mu)
          (euclideanDyadicCubeShellCompactLaw dimension shell nu) := by
  rw [← map_euclideanDyadicCubeScaleBack_compactLaw_eq_shellLaw_of_nonzero
    dimension shell mu hmu,
    ← map_euclideanDyadicCubeScaleBack_compactLaw_eq_shellLaw_of_nonzero
      dimension shell nu hnu]
  exact wassersteinOne_euclideanDyadicCubeScaleBack_le dimension shell
    (euclideanDyadicCubeShellCompactLaw dimension shell mu)
    (euclideanDyadicCubeShellCompactLaw dimension shell nu)

/-- The outer radius of the `shell`-th dyadic Euclidean shell. -/
def euclideanDyadicShellOuterRadius (shell : ℕ) : ℝ :=
  ((2 ^ (shell + 1) : ℕ) : ℝ)

/-- The inner radius of the `shell`-th dyadic Euclidean shell. -/
def euclideanDyadicShellInnerRadius (shell : ℕ) : ℝ :=
  ((2 ^ shell : ℕ) : ℝ)

theorem euclideanDyadicShellInnerRadius_pos (shell : ℕ) :
    0 < euclideanDyadicShellInnerRadius shell := by
  unfold euclideanDyadicShellInnerRadius
  positivity

theorem euclideanDyadicShellOuterRadius_pos (shell : ℕ) :
    0 < euclideanDyadicShellOuterRadius shell := by
  unfold euclideanDyadicShellOuterRadius
  positivity

/-- Points strictly outside the preceding dyadic ball and inside this shell's outer ball. -/
def euclideanDyadicShell (dimension shell : ℕ) : Set (EuclideanSpace ℝ (Fin dimension)) :=
  {x | euclideanDyadicShellInnerRadius shell < ‖x‖ ∧
    ‖x‖ ≤ euclideanDyadicShellOuterRadius shell}

theorem measurableSet_euclideanDyadicShell (dimension shell : ℕ) :
    MeasurableSet (euclideanDyadicShell dimension shell) := by
  exact measurable_norm measurableSet_Ioc

theorem norm_le_euclideanDyadicShellOuterRadius
    (dimension shell : ℕ) (x : euclideanDyadicShell dimension shell) :
    ‖(x : EuclideanSpace ℝ (Fin dimension))‖ ≤ euclideanDyadicShellOuterRadius shell :=
  x.2.2

/-- Distinct dyadic norm shells are disjoint. -/
theorem disjoint_euclideanDyadicShell (dimension first second : ℕ)
    (hne : first ≠ second) :
    Disjoint (euclideanDyadicShell dimension first)
      (euclideanDyadicShell dimension second) := by
  have hdisjoint_of_lt : ∀ {lower upper : ℕ}, lower < upper →
      Disjoint (euclideanDyadicShell dimension lower)
        (euclideanDyadicShell dimension upper) := by
    intro lower upper hlt
    rw [Set.disjoint_left]
    intro x hlower hupper
    have hindex : lower + 1 ≤ upper := by omega
    have hpow_nat : 2 ^ (lower + 1) ≤ 2 ^ upper := by
      exact Nat.pow_le_pow_right (by omega) hindex
    have hpow : euclideanDyadicShellOuterRadius lower ≤ ((2 ^ upper : ℕ) : ℝ) := by
      unfold euclideanDyadicShellOuterRadius
      exact_mod_cast hpow_nat
    exact (not_lt_of_ge (hlower.2.trans hpow)) hupper.1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hdisjoint_of_lt hlt
  · exact (hdisjoint_of_lt hgt).symm

/--
The local compact coordinate for a point in a dyadic shell.  It is the
existing radial-collapse scale at the shell's outer radius; on this subtype
the collapse is the identity.
-/
def euclideanDyadicShellScale (dimension shell : ℕ) :
    euclideanDyadicShell dimension shell → HalfOpenUnitCube dimension :=
  fun x ↦ euclideanRadialCollapseScale dimension (euclideanDyadicShellOuterRadius shell)
    (euclideanDyadicShellOuterRadius_pos shell) x.1

theorem measurable_euclideanDyadicShellScale (dimension shell : ℕ) :
    Measurable (euclideanDyadicShellScale dimension shell) := by
  exact (measurable_euclideanRadialCollapseScale dimension
    (euclideanDyadicShellOuterRadius shell) (euclideanDyadicShellOuterRadius_pos shell)).comp
      measurable_subtype_coe

/-- Scaling a shell point back from the compact cube recovers the original point. -/
theorem euclideanScaleBack_euclideanDyadicShellScale
    (dimension shell : ℕ) (x : euclideanDyadicShell dimension shell) :
    euclideanScaleBack dimension (euclideanDyadicShellOuterRadius shell)
      (euclideanDyadicShellScale dimension shell x) = x.1 := by
  unfold euclideanDyadicShellScale
  rw [euclideanScaleBack_radialCollapseScale]
  simp only [euclideanRadialCollapse,
    if_pos (norm_le_euclideanDyadicShellOuterRadius dimension shell x)]

/--
The source-style probability law obtained by restricting to a shell and
normalizing.  Mathlib totalizes normalization of a zero-mass shell by a
default probability measure; every later shell-weighted theorem must retain
the shell mass, so that branch contributes zero rather than asserting an
undefined conditional law.
-/
def euclideanDyadicShellLaw (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)) :=
  (law.toFiniteMeasure.restrict (euclideanDyadicShell dimension shell)).normalize

/--
The normalized shell law mapped into the compact dyadic cube.  It is the
probability-law counterpart of `euclideanDyadicShellScale`; the global map is
used so that it remains defined on the zero-mass normalization branch.
-/
def euclideanDyadicShellCompactLaw (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension))) :
    ProbabilityMeasure (HalfOpenUnitCube dimension) :=
  (euclideanDyadicShellLaw dimension shell law).map
    (measurable_euclideanRadialCollapseScale dimension
      (euclideanDyadicShellOuterRadius shell)
      (euclideanDyadicShellOuterRadius_pos shell)).aemeasurable

/--
On a nonzero shell, Mathlib's normalized law is exactly inverse shell mass
times the restricted finite measure.  This exposes the source's conditional
law rather than treating normalization as a certificate.
-/
theorem euclideanDyadicShellLaw_toMeasure_eq_of_nonzero
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hnonzero : law.toFiniteMeasure.restrict (euclideanDyadicShell dimension shell) ≠ 0) :
    (euclideanDyadicShellLaw dimension shell law :
      Measure (EuclideanSpace ℝ (Fin dimension))) =
      (law.toFiniteMeasure.restrict (euclideanDyadicShell dimension shell)).mass⁻¹ •
        (law.toFiniteMeasure.restrict (euclideanDyadicShell dimension shell) :
          Measure (EuclideanSpace ℝ (Fin dimension))) := by
  unfold euclideanDyadicShellLaw
  exact FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hnonzero

end
end Probability
end AppliedModelingLib
