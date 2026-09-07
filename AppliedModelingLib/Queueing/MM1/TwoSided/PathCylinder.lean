import AppliedModelingLib.Queueing.MM1.Marked.Suspension
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Extending contiguous two-sided path windows to a path law

For integer-indexed product paths, equality of the laws of every finite
contiguous coordinate interval determines the whole path measure. This module
packages that measurable-cylinder argument and its measure-preserving
corollary. It is the general final step after a two-sided Markov construction
has established all finite-window shift identities.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory Set

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Equality of all finite coordinate restrictions determines a finite path
measure. -/
theorem measure_eq_of_all_finset_restrict
    {μ ν : Measure (ℤ → α)} [IsFiniteMeasure μ]
    (h : ∀ I : Finset ℤ, μ.map I.restrict = ν.map I.restrict)
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  refine ext_of_generate_finite (measurableCylinders fun _ : ℤ => α)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ huniv
  intro s hs
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [cylinder, ← Measure.map_apply _ hS, h I, Measure.map_apply _ hS]
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The restriction to an empty finite coordinate set is determined by total
mass alone. -/
theorem map_empty_restrict_eq_of_univ
    {μ ν : Measure (ℤ → α)}
    (huniv : μ Set.univ = ν Set.univ) :
    μ.map (∅ : Finset ℤ).restrict = ν.map (∅ : Finset ℤ).restrict := by
  apply Measure.ext
  intro s hs
  rcases Set.eq_empty_or_nonempty s with hzero | ⟨x, hx⟩
  · simp [hzero]
  have hs_univ : s = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rw [show y = x by exact Subsingleton.elim _ _]
    exact hx
  calc
    μ.map (∅ : Finset ℤ).restrict s = μ Set.univ := by
      rw [hs_univ, Measure.map_apply (Finset.measurable_restrict (∅ : Finset ℤ))
        MeasurableSet.univ, preimage_univ]
    _ = ν Set.univ := huniv
    _ = ν.map (∅ : Finset ℤ).restrict s := by
      rw [hs_univ, Measure.map_apply (Finset.measurable_restrict (∅ : Finset ℤ))
        MeasurableSet.univ, preimage_univ]

/-- Equality of every finite contiguous integer interval restriction determines
the whole two-sided path measure. -/
theorem measure_eq_of_all_Icc_restrict
    {μ ν : Measure (ℤ → α)} [IsFiniteMeasure μ]
    (h : ∀ a b : ℤ,
      μ.map (Finset.Icc a b).restrict = ν.map (Finset.Icc a b).restrict)
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  apply measure_eq_of_all_finset_restrict (μ := μ) (ν := ν) ?_ huniv
  intro I
  by_cases hI : I = ∅
  · subst I
    exact map_empty_restrict_eq_of_univ huniv
  let hne : I.Nonempty := Finset.nonempty_of_ne_empty hI
  let J : Finset ℤ := Finset.Icc (I.min' hne) (I.max' hne)
  have hIJ : I ⊆ J := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le I i hi, Finset.le_max' I i hi⟩
  let rJ : (ℤ → α) → (J → α) := @Finset.restrict ℤ (fun _ : ℤ => α) J
  let rIJ : (J → α) → (I → α) :=
    @Finset.restrict₂ ℤ (fun _ : ℤ => α) I J hIJ
  have hrJ : Measurable rJ := by
    exact Finset.measurable_restrict J
  have hrIJ : Measurable rIJ := by
    exact Finset.measurable_restrict₂ hIJ
  have hcomp : rIJ ∘ rJ = I.restrict := by
    exact Finset.restrict₂_comp_restrict hIJ
  have hJ : μ.map rJ = ν.map rJ := by
    change μ.map (Finset.Icc (I.min' hne) (I.max' hne)).restrict =
      ν.map (Finset.Icc (I.min' hne) (I.max' hne)).restrict
    exact h (I.min' hne) (I.max' hne)
  calc
    μ.map I.restrict = (μ.map rJ).map rIJ := by
      symm
      rw [Measure.map_map hrIJ hrJ, hcomp]
    _ = (ν.map rJ).map rIJ := by
      rw [hJ]
    _ = ν.map I.restrict := by
      rw [Measure.map_map hrIJ hrJ, hcomp]

/-- The interval-restriction criterion specialized to probability path laws. -/
theorem measure_eq_of_all_Icc_restrict_probability
    {μ ν : Measure (ℤ → α)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ a b : ℤ,
      μ.map (Finset.Icc a b).restrict = ν.map (Finset.Icc a b).restrict) :
    μ = ν :=
  measure_eq_of_all_Icc_restrict h (by simp)

/-- A measurable path map is measure-preserving if it preserves every finite
contiguous coordinate-window law. -/
theorem measurePreserving_of_all_Icc_restrict
    {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (f : (ℤ → α) → (ℤ → α)) (hf : Measurable f)
    (h : ∀ a b : ℤ,
      μ.map (Finset.Icc a b).restrict =
        (μ.map f).map (Finset.Icc a b).restrict) :
    MeasurePreserving f μ μ := by
  letI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  refine ⟨hf, ?_⟩
  exact (measure_eq_of_all_Icc_restrict_probability h).symm

/-- Integer relabeling preserves a probability path law once every finite
contiguous integer window has the same law after that relabeling. -/
theorem intPathShift_measurePreserving_of_all_Icc_restrict
    {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] (k : ℤ)
    (h : ∀ a b : ℤ,
      μ.map (Finset.Icc a b).restrict =
        (μ.map (intPathShift (α := α) k)).map
          (Finset.Icc a b).restrict) :
    MeasurePreserving (intPathShift (α := α) k) μ μ :=
  measurePreserving_of_all_Icc_restrict _
    (measurable_intPathShift (α := α) k) h

end

end AppliedModelingLib.Probability.Queueing
