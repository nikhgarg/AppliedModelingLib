import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Bounded Density Measures

Reusable interfaces for measures represented by a density bounded above with
respect to a base measure.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace AppliedModelingLib
namespace Probability

/--
`mu` has a density bounded by `C` with respect to the base measure `nu`.

The witness is intentionally `withDensity`-based so later paper proofs can use
mathlib's absolute-continuity and Lebesgue-integral APIs directly.
-/
def HasBoundedDensity
    {α : Type*} [MeasurableSpace α]
    (ν μ : Measure α) (C : ℝ≥0∞) : Prop :=
  ∃ D : α → ℝ≥0∞, μ = ν.withDensity D ∧ ∀ᵐ x ∂ν, D x ≤ C

namespace HasBoundedDensity

theorem absolutelyContinuous
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) :
    μ ≪ ν := by
  rcases h with ⟨D, hμ, _hbound⟩
  rw [hμ]
  exact withDensity_absolutelyContinuous ν D

theorem measure_eq_zero_of_base_null
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) {s : Set α} (hs : ν s = 0) :
    μ s = 0 :=
  h.absolutelyContinuous hs

theorem measure_le_const_mul
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) {s : Set α} (hs : MeasurableSet s) :
    μ s ≤ C * ν s := by
  rcases h with ⟨D, hμ, hbound⟩
  rw [hμ, withDensity_apply D hs]
  calc
    ∫⁻ x in s, D x ∂ν
        ≤ ∫⁻ _x in s, C ∂ν := by
          exact setLIntegral_mono_ae' hs
            (hbound.mono fun _x hx _hxs => hx)
    _ = C * ν s := by
          rw [setLIntegral_const]

theorem measure_le_const_mul_of_base_null
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) {s : Set α} (hs : MeasurableSet s)
    (hνs : ν s = 0) :
    μ s = 0 := by
  exact h.measure_eq_zero_of_base_null hνs

theorem measure_biUnion_finset_le_const_mul_sum
    {α ι : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) (I : Finset ι) (s : ι → Set α)
    (hs : ∀ i, i ∈ I → MeasurableSet (s i)) :
    μ (⋃ i ∈ I, s i) ≤ C * ∑ i ∈ I, ν (s i) := by
  calc
    μ (⋃ i ∈ I, s i) ≤ ∑ i ∈ I, μ (s i) := by
      exact measure_biUnion_finset_le I s
    _ ≤ ∑ i ∈ I, C * ν (s i) := by
      exact Finset.sum_le_sum fun i hi => h.measure_le_const_mul (hs i hi)
    _ = C * ∑ i ∈ I, ν (s i) := by
      rw [Finset.mul_sum]

theorem measure_Icc_le_const_mul_length
    {μ : Measure ℝ} {C : ℝ≥0∞}
    (h : HasBoundedDensity StieltjesFunction.id.measure μ C) (a b : ℝ) :
    μ (Set.Icc a b) ≤ C * ENNReal.ofReal (b - a) := by
  have hlength :
      StieltjesFunction.id.measure (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    rw [← Real.volume_eq_stieltjes_id]
    exact Real.volume_Icc
  simpa [hlength] using
    h.measure_le_const_mul (s := Set.Icc a b) measurableSet_Icc

theorem measure_Ioo_le_const_mul_length
    {μ : Measure ℝ} {C : ℝ≥0∞}
    (h : HasBoundedDensity StieltjesFunction.id.measure μ C) (a b : ℝ) :
    μ (Set.Ioo a b) ≤ C * ENNReal.ofReal (b - a) := by
  have hlength :
      StieltjesFunction.id.measure (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
    rw [← Real.volume_eq_stieltjes_id]
    exact Real.volume_Ioo
  simpa [hlength] using
    h.measure_le_const_mul (s := Set.Ioo a b) measurableSet_Ioo

/--
A bounded-density measure on a finite-dimensional real coordinate space assigns
at most density-bound times Lebesgue volume to an axis-aligned closed box.
-/
theorem measure_Icc_pi_le_const_mul_volume
    {ι : Type*} [Fintype ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b : ι → ℝ) :
    μ (Set.Icc a b) ≤ C * ∏ i, ENNReal.ofReal (b i - a i) := by
  have hbox :=
    h.measure_le_const_mul (s := Set.Icc a b) measurableSet_Icc
  simpa [Real.volume_Icc_pi] using hbox

/--
Coordinate-slab bound inside an axis-aligned box.  The selected coordinate is
restricted to an interval of radius `r` around `center`; all other coordinates
are bounded by the ambient box.  This is the reusable geometric estimate behind
fixed-dimension small-slab probability bounds on bounded domains.
-/
theorem measure_coordinate_slab_Icc_le_const_mul_volume
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b : ι → ℝ) (i : ι) (center r : ℝ) :
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
      ≤ C *
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center + r)) j -
            (Function.update a i (center - r)) j) := by
  let lo : ι → ℝ := Function.update a i (center - r)
  let hi : ι → ℝ := Function.update b i (center + r)
  have hsubset :
      {x : ι → ℝ |
          x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
        ⊆ Set.Icc lo hi := by
    intro x hx
    rcases hx with ⟨hbox, hslab⟩
    constructor
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa [lo] using hslab.1
      · simpa [lo, hji] using hbox.1 j
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa [hi] using hslab.2
      · simpa [hi, hji] using hbox.2 j
  calc
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
        ≤ μ (Set.Icc lo hi) := measure_mono hsubset
    _ ≤ C * ∏ j, ENNReal.ofReal (hi j - lo j) := by
        exact measure_Icc_pi_le_const_mul_volume h lo hi
    _ = C *
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center + r)) j -
            (Function.update a i (center - r)) j) := by
        rfl

/--
An oblique coordinate slab has the same rectangular-volume upper bound as an
ordinary coordinate slab.  The proof uses a volume-preserving transvection to
replace `x i + coefficient * x j` by a coordinate while leaving the remaining
coordinates unchanged.
-/
theorem volume_linear_coordinate_slab_Icc_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (a b : ι → ℝ)
    (coefficient center r : ℝ) :
    volume {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ≤
      ∏ k, ENNReal.ofReal
        ((Function.update b i (center + r)) k -
          (Function.update a i (center - r)) k) := by
  let t : Matrix.TransvectionStruct ι ℝ := ⟨i, j, hij, coefficient⟩
  let lo : ι → ℝ := Function.update a i (center - r)
  let hi : ι → ℝ := Function.update b i (center + r)
  have ht_i (x : ι → ℝ) : Matrix.toLin' t.toMatrix x i =
      x i + coefficient * x j := by
    dsimp [t]
    change (Matrix.mulVec (Matrix.transvection i j coefficient) x) i =
      x i + coefficient * x j
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec]
    simp
  have ht_ne (x : ι → ℝ) {k : ι} (hk : k ≠ i) :
      Matrix.toLin' t.toMatrix x k = x k := by
    dsimp [t]
    change (Matrix.mulVec (Matrix.transvection i j coefficient) x) k = x k
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec]
    simp [hk]
  have hsubset :
      {x : ι → ℝ |
        x ∈ Set.Icc a b ∧
          x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ⊆
        (Matrix.toLin' t.toMatrix) ⁻¹' Set.Icc lo hi := by
    intro x hx
    constructor
    · intro k
      by_cases hki : k = i
      · subst k
        simpa [lo, ht_i] using hx.2.1
      · rw [ht_ne x hki]
        simpa [lo, hki] using hx.1.1 k
    · intro k
      by_cases hki : k = i
      · subst k
        simpa [hi, ht_i] using hx.2.2
      · rw [ht_ne x hki]
        simpa [hi, hki] using hx.1.2 k
  calc
    volume {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ≤
        volume ((Matrix.toLin' t.toMatrix) ⁻¹' Set.Icc lo hi) :=
      measure_mono hsubset
    _ = volume (Set.Icc lo hi) := by
      exact (Real.volume_preserving_transvectionStruct t).measure_preimage
        measurableSet_Icc.nullMeasurableSet
    _ = ∏ k, ENNReal.ofReal
        ((Function.update b i (center + r)) k -
          (Function.update a i (center - r)) k) := by
      simpa [lo, hi] using (Real.volume_Icc_pi (a := lo) (b := hi))

/--
Bounded-density version of the oblique-coordinate slab estimate.  It applies
to a linear combination of two distinct coordinates inside a fixed box and is
useful for fixed-dimensional near-tie probability bounds.
-/
theorem measure_linear_coordinate_slab_Icc_le_const_mul_volume
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (i j : ι) (hij : i ≠ j) (a b : ι → ℝ)
    (coefficient center r : ℝ) :
    μ {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ≤
      C * ∏ k, ENNReal.ofReal
        ((Function.update b i (center + r)) k -
          (Function.update a i (center - r)) k) := by
  have hs : MeasurableSet {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} := by
    change MeasurableSet (Set.Icc a b ∩
      (fun x : ι → ℝ => x i + coefficient * x j) ⁻¹'
        Set.Icc (center - r) (center + r))
    apply MeasurableSet.inter measurableSet_Icc
    apply MeasurableSet.preimage measurableSet_Icc
    exact (measurable_pi_apply i).add
      (measurable_const.mul (measurable_pi_apply j))
  calc
    μ {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ≤
        C * volume {x : ι → ℝ |
          x ∈ Set.Icc a b ∧
            x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} :=
      h.measure_le_const_mul hs
    _ ≤ C * ∏ k, ENNReal.ofReal
        ((Function.update b i (center + r)) k -
          (Function.update a i (center - r)) k) := by
      gcongr
      exact volume_linear_coordinate_slab_Icc_le i j hij a b coefficient center r

/--
The oblique-coordinate slab bound factors its selected-coordinate width as
`2 * r`.  The remaining factor is the volume of the ambient box in all other
coordinates.
-/
theorem measure_linear_coordinate_slab_Icc_le_const_mul_twoRadius_mul_volume_erase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (i j : ι) (hij : i ≠ j) (a b : ι → ℝ)
    (coefficient center r : ℝ) :
    μ {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ≤
      C * (ENNReal.ofReal (2 * r) *
        ∏ k ∈ (Finset.univ.erase i), ENNReal.ofReal (b k - a k)) := by
  let f : ι → ℝ≥0∞ := fun k => ENNReal.ofReal
    ((Function.update b i (center + r)) k -
      (Function.update a i (center - r)) k)
  have hfi : f i = ENNReal.ofReal (2 * r) := by
    simp only [f, Function.update_apply, if_pos]
    congr 1
    ring
  have hrest :
      ∏ k ∈ (Finset.univ.erase i), f k =
        ∏ k ∈ (Finset.univ.erase i), ENNReal.ofReal (b k - a k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp [f, hki]
  calc
    μ {x : ι → ℝ |
      x ∈ Set.Icc a b ∧
        x i + coefficient * x j ∈ Set.Icc (center - r) (center + r)} ≤
        C * ∏ k, f k := by
      simpa only [f] using
        measure_linear_coordinate_slab_Icc_le_const_mul_volume
          h i j hij a b coefficient center r
    _ = C * (f i * ∏ k ∈ (Finset.univ.erase i), f k) := by
      rw [Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
    _ = C * (ENNReal.ofReal (2 * r) *
        ∏ k ∈ (Finset.univ.erase i), ENNReal.ofReal (b k - a k)) := by
      rw [hfi, hrest]

/--
Finite union bound for coordinate slabs in an axis-aligned box.  This is the
paper-neutral form of the ``one coordinate is within radius `r`'' estimate:
the right-hand side retains the exact rectangular-volume bound for each slab,
so clients may impose their own bounded-domain hypotheses to obtain a linear
in-`r` constant.
-/
theorem measure_exists_coordinate_slab_Icc_le_const_mul_sum_volume
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b center : ι → ℝ) (r : ℝ) :
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧
          ∃ i, x i ∈ Set.Icc (center i - r) (center i + r)}
      ≤ C * ∑ i,
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center i + r)) j -
            (Function.update a i (center i - r)) j) := by
  classical
  let slab : ι → Set (ι → ℝ) := fun i =>
    {x | x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center i - r) (center i + r)}
  have hunion :
      {x : ι → ℝ |
          x ∈ Set.Icc a b ∧
            ∃ i, x i ∈ Set.Icc (center i - r) (center i + r)} =
        ⋃ i ∈ (Finset.univ : Finset ι), slab i := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ,
      Set.mem_Icc, slab]
    aesop
  rw [hunion]
  calc
    μ (⋃ i ∈ (Finset.univ : Finset ι), slab i) ≤
        ∑ i ∈ (Finset.univ : Finset ι), μ (slab i) := by
      exact measure_biUnion_finset_le Finset.univ slab
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), C *
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center i + r)) j -
            (Function.update a i (center i - r)) j) := by
      exact Finset.sum_le_sum fun i _ =>
        measure_coordinate_slab_Icc_le_const_mul_volume h a b i (center i) r
    _ = C * ∑ i,
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center i + r)) j -
            (Function.update a i (center i - r)) j) := by
      rw [Finset.mul_sum]

/--
The rectangular-volume bound for one coordinate slab factors its selected
coordinate as the interval length `2 * r`.  No positivity assumption on `r`
is needed: a negative radius gives the empty slab and `ENNReal.ofReal (2 * r)`
is zero.
-/
theorem measure_coordinate_slab_Icc_le_const_mul_twoRadius_mul_volume_erase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b : ι → ℝ) (i : ι) (center r : ℝ) :
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
      ≤ C * (ENNReal.ofReal (2 * r) *
        ∏ j ∈ (Finset.univ.erase i), ENNReal.ofReal (b j - a j)) := by
  let f : ι → ℝ≥0∞ := fun j => ENNReal.ofReal
    ((Function.update b i (center + r)) j -
      (Function.update a i (center - r)) j)
  have hfi : f i = ENNReal.ofReal (2 * r) := by
    simp only [f, Function.update_apply, if_pos]
    congr 1
    ring
  have hrest :
      ∏ j ∈ (Finset.univ.erase i), f j =
        ∏ j ∈ (Finset.univ.erase i), ENNReal.ofReal (b j - a j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [f, hji]
  calc
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)} ≤
        C * ∏ j, f j := by
      simpa only [f] using
        measure_coordinate_slab_Icc_le_const_mul_volume h a b i center r
    _ = C * (f i * ∏ j ∈ (Finset.univ.erase i), f j) := by
      rw [Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
    _ = C * (ENNReal.ofReal (2 * r) *
        ∏ j ∈ (Finset.univ.erase i), ENNReal.ofReal (b j - a j)) := by
      rw [hfi, hrest]

/--
Finite union version of the linear coordinate-slab estimate.  On a fixed box,
the probability mass of points within radius `r` of the center in at least one
coordinate is bounded by an explicit constant times `ENNReal.ofReal (2 * r)`.
-/
theorem measure_exists_coordinate_slab_Icc_le_const_mul_twoRadius_mul_sum_volume_erase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b center : ι → ℝ) (r : ℝ) :
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧
          ∃ i, x i ∈ Set.Icc (center i - r) (center i + r)}
      ≤ C * (ENNReal.ofReal (2 * r) * ∑ i,
        ∏ j ∈ (Finset.univ.erase i), ENNReal.ofReal (b j - a j)) := by
  classical
  let slab : ι → Set (ι → ℝ) := fun i =>
    {x | x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center i - r) (center i + r)}
  have hunion :
      {x : ι → ℝ |
          x ∈ Set.Icc a b ∧
            ∃ i, x i ∈ Set.Icc (center i - r) (center i + r)} =
        ⋃ i ∈ (Finset.univ : Finset ι), slab i := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ,
      Set.mem_Icc, slab]
    aesop
  rw [hunion]
  calc
    μ (⋃ i ∈ (Finset.univ : Finset ι), slab i) ≤
        ∑ i ∈ (Finset.univ : Finset ι), μ (slab i) := by
      exact measure_biUnion_finset_le Finset.univ slab
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), C *
        (ENNReal.ofReal (2 * r) *
          ∏ j ∈ (Finset.univ.erase i), ENNReal.ofReal (b j - a j)) := by
      exact Finset.sum_le_sum fun i _ =>
        measure_coordinate_slab_Icc_le_const_mul_twoRadius_mul_volume_erase
          h a b i (center i) r
    _ = C * (ENNReal.ofReal (2 * r) * ∑ i,
        ∏ j ∈ (Finset.univ.erase i), ENNReal.ofReal (b j - a j)) := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]

end HasBoundedDensity

end Probability
end AppliedModelingLib
