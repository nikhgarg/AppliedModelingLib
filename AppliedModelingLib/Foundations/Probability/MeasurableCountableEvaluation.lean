import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Measurable evaluation at a countable random index

Finite-window point-process constructions often reindex an infinite path at a
random integer crossing index.  This small lemma records the relevant Borel
fact directly: evaluation remains measurable when the index takes values in a
countable measurable singleton space.  It avoids replacing a random finite
window by an opaque selector.
-/

namespace AppliedModelingLib.Probability

noncomputable section

/-- Evaluate a jointly path-indexed family at a measurable countable index.
The proof forms the measurable uncurried map by countable fibers and then
composes it with the index/path pair. -/
theorem measurable_apply_of_measurable_countable_index
    {Ω : Type*} {ι : Type*} {β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSpace β]
    [Countable ι] [MeasurableSingletonClass ι]
    (f : Ω → ι → β)
    (hf : ∀ i, Measurable fun ω => f ω i)
    (index : Ω → ι) (hindex : Measurable index) :
    Measurable fun ω => f ω (index ω) := by
  have huncurry : Measurable (fun p : ι × Ω => f p.2 p.1) :=
    measurable_from_prod_countable_right fun i => hf i
  exact huncurry.comp (hindex.prodMk measurable_id)

/-- Glue Borel formulas along a countable measurable cover.  Empty and
overlapping covering sets are allowed: the pointwise agreement hypothesis is
the only compatibility requirement.  This is useful when a random finite
carrier is analyzed on its countably many fixed-carrier fibers, without
introducing a measurable-space structure on that carrier type. -/
theorem measurable_of_countable_measurable_cover
    {Ω : Type*} {ι : Type*} {β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [Countable ι]
    (cover : ι → Set Ω) (hcover_measurable : ∀ i, MeasurableSet (cover i))
    (hcover : (⋃ i, cover i) = Set.univ)
    (f : Ω → β) (piece : ι → Ω → β)
    (hpiece : ∀ i, Measurable (piece i))
    (hagree : ∀ i omega, omega ∈ cover i → f omega = piece i omega) :
    Measurable f := by
  intro s hs
  have hpreimage : f ⁻¹' s = ⋃ i, cover i ∩ (piece i) ⁻¹' s := by
    ext omega
    constructor
    · intro hmem
      have hcovered : omega ∈ ⋃ i, cover i := by
        rw [hcover]
        exact Set.mem_univ omega
      rcases Set.mem_iUnion.mp hcovered with ⟨i, hi⟩
      refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
      change piece i omega ∈ s
      change f omega ∈ s at hmem
      rwa [← hagree i omega hi]
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨i, hi, hpiece_mem⟩
      change piece i omega ∈ s at hpiece_mem
      change f omega ∈ s
      rwa [hagree i omega hi]
  rw [hpreimage]
  exact MeasurableSet.iUnion fun i =>
    (hcover_measurable i).inter ((hpiece i) hs)

/-- Glue Borel formulas along a countable measurable cover when the local
formula is topologically inseparable from the target.  This is the natural
variant for pseudometric path spaces whose Borel structure identifies
representatives that differ only outside the observed time domain. -/
theorem measurable_of_countable_measurable_cover_inseparable
    {Ω : Type*} {ι : Type*} {β : Type*}
    [MeasurableSpace Ω] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [Countable ι]
    (cover : ι → Set Ω) (hcover_measurable : ∀ i, MeasurableSet (cover i))
    (hcover : (⋃ i, cover i) = Set.univ)
    (f : Ω → β) (piece : ι → Ω → β)
    (hpiece : ∀ i, Measurable (piece i))
    (hclose : ∀ i omega, omega ∈ cover i → Inseparable (f omega) (piece i omega)) :
    Measurable f := by
  intro s hs
  have hpreimage : f ⁻¹' s = ⋃ i, cover i ∩ (piece i) ⁻¹' s := by
    ext omega
    constructor
    · intro hmem
      have hcovered : omega ∈ ⋃ i, cover i := by
        rw [hcover]
        exact Set.mem_univ omega
      rcases Set.mem_iUnion.mp hcovered with ⟨i, hi⟩
      refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
      exact ((hclose i omega hi).mem_measurableSet_iff hs).1 hmem
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨i, hi, hpiece_mem⟩
      exact ((hclose i omega hi).mem_measurableSet_iff hs).2 hpiece_mem
  rw [hpreimage]
  exact MeasurableSet.iUnion fun i =>
    (hcover_measurable i).inter ((hpiece i) hs)

/-- A finite integer window selected by random integer bounds and a
coordinatewise predicate.  This remains a plain `Finset` construction: the
measurability API below works through its fixed-label fibers rather than
postulating a measurable-space instance for finite sets. -/
noncomputable def finiteIntWindow
    {Omega : Type*} (lower upper : Omega → ℤ)
    (keep : Omega → ℤ → Prop) (omega : Omega) : Finset ℤ := by
  classical
  exact (Finset.Icc (lower omega) (upper omega)).filter (keep omega)

/-- Membership in a random filtered integer window is the conjunction of two
fixed-coordinate bound tests and the corresponding coordinate predicate. -/
theorem mem_finiteIntWindow_iff
    {Omega : Type*} (lower upper : Omega → ℤ)
    (keep : Omega → ℤ → Prop) (omega : Omega) (n : ℤ) :
    n ∈ finiteIntWindow lower upper keep omega ↔
      lower omega ≤ n ∧ n ≤ upper omega ∧ keep omega n := by
  classical
  simp [finiteIntWindow, and_assoc]

/-- Each fixed label has a measurable membership event in a random filtered
integer window. -/
theorem measurableSet_mem_finiteIntWindow
    {Omega : Type*} [MeasurableSpace Omega]
    (lower upper : Omega → ℤ) (keep : Omega → ℤ → Prop)
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hkeep : ∀ n : ℤ, MeasurableSet {omega | keep omega n})
    (n : ℤ) :
    MeasurableSet {omega | n ∈ finiteIntWindow lower upper keep omega} := by
  have hlower_bound : MeasurableSet {omega : Omega | lower omega ≤ n} :=
    measurableSet_le hlower measurable_const
  have hupper_bound : MeasurableSet {omega : Omega | n ≤ upper omega} :=
    measurableSet_le measurable_const hupper
  simpa only [mem_finiteIntWindow_iff] using
    hlower_bound.inter (hupper_bound.inter (hkeep n))

/-- Every fixed finite label set is a measurable fiber of a random filtered
integer window.  The proof is a countable intersection of its fixed-label
membership decisions, which is the usable Borel stratification for a later
finite execution proof. -/
theorem measurableSet_finiteIntWindow_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (lower upper : Omega → ℤ) (keep : Omega → ℤ → Prop)
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hkeep : ∀ n : ℤ, MeasurableSet {omega | keep omega n})
    (labels : Finset ℤ) :
    MeasurableSet {omega | finiteIntWindow lower upper keep omega = labels} := by
  classical
  have hmem : ∀ n : ℤ,
      MeasurableSet {omega | n ∈ finiteIntWindow lower upper keep omega} := by
    intro n
    exact measurableSet_mem_finiteIntWindow lower upper keep hlower hupper hkeep n
  have hfiber : ∀ n : ℤ,
      MeasurableSet {omega | n ∈ finiteIntWindow lower upper keep omega ↔ n ∈ labels} := by
    intro n
    by_cases hn : n ∈ labels
    · simpa [hn] using hmem n
    · have hnot : MeasurableSet
          {omega | n ∉ finiteIntWindow lower upper keep omega} := by
        convert (hmem n).compl using 1
      simpa [hn] using hnot
  have heq : {omega | finiteIntWindow lower upper keep omega = labels} =
      ⋂ n : ℤ, {omega | n ∈ finiteIntWindow lower upper keep omega ↔ n ∈ labels} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h n
      simpa [h]
    · intro h
      ext n
      exact h n
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The fixed-label fibers of a random filtered integer window are disjoint. -/
theorem pairwiseDisjoint_finiteIntWindow_eq
    {Omega : Type*} (lower upper : Omega → ℤ) (keep : Omega → ℤ → Prop) :
    Pairwise (fun left right : Finset ℤ =>
      Disjoint {omega | finiteIntWindow lower upper keep omega = left}
        {omega | finiteIntWindow lower upper keep omega = right}) := by
  intro left right hne
  rw [Set.disjoint_left]
  intro omega hleft hright
  exact hne (hleft.symm.trans hright)

/-- The measurable fixed-label fibers cover the entire input space. -/
theorem iUnion_finiteIntWindow_eq_univ
    {Omega : Type*} (lower upper : Omega → ℤ) (keep : Omega → ℤ → Prop) :
    (⋃ labels : Finset ℤ,
      {omega | finiteIntWindow lower upper keep omega = labels}) = Set.univ := by
  ext omega
  constructor
  · intro _
    simp
  · intro _
    exact Set.mem_iUnion.mpr ⟨finiteIntWindow lower upper keep omega, rfl⟩

end

end AppliedModelingLib.Probability
