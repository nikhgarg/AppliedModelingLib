import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import AppliedModelingLib.Foundations.Probability.FiniteIID

/-!
# Finite empirical probability measures

This module gives the measure-valued empirical law of a nonempty finite sample.
It is independent of any learning objective, so it can be used by empirical
process, optimal-transport, and statistical-learning arguments alike.

The empirical pushforward lemmas directly use `PMF.map_comp` and
`PMF.toMeasure_map` from
[`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean)
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/

namespace AppliedModelingLib

/-- The empirical probability measure obtained by uniformly selecting an arbitrary finite index. -/
noncomputable def empiricalFintypeProbabilityMeasure
    {Index Sample : Type*} [Fintype Index] [Nonempty Index] [MeasurableSpace Sample]
    (sample : Index → Sample) : MeasureTheory.ProbabilityMeasure Sample :=
  ⟨((PMF.uniformOfFintype Index).map sample).toMeasure, inferInstance⟩

/-- The finite index set of observations from a finite sample that lie in `s`. -/
noncomputable def empiricalFintypeIndicesInSet
    {Index Sample : Type*} [Fintype Index]
    (sample : Index → Sample) (s : Set Sample) : Finset Index := by
  classical
  exact Finset.univ.filter fun index => sample index ∈ s

/-- The value of a finite-index empirical probability measure on a measurable set. -/
theorem empiricalFintypeProbabilityMeasure_apply
    {Index Sample : Type*} [Fintype Index] [Nonempty Index]
    [MeasurableSpace Index] [MeasurableSingletonClass Index] [MeasurableSpace Sample]
    (sample : Index → Sample) (t : Set Sample) (ht : MeasurableSet t) :
    (empiricalFintypeProbabilityMeasure sample : MeasureTheory.Measure Sample) t =
      (empiricalFintypeIndicesInSet sample t).card /
        Fintype.card Index := by
  classical
  letI : Fintype (↥(sample ⁻¹' t)) := Fintype.ofFinite _
  change ((PMF.uniformOfFintype Index).map sample).toMeasure t = _
  rw [PMF.toMeasure_map_apply sample (PMF.uniformOfFintype Index) t
    (measurable_of_finite sample) ht]
  rw [PMF.toMeasure_uniformOfFintype_apply (sample ⁻¹' t)
    (ht.preimage (measurable_of_finite sample))]
  congr 1
  change (Fintype.card (↥(sample ⁻¹' t)) : ENNReal) = _
  rw [Fintype.card_of_subtype (empiricalFintypeIndicesInSet sample t)]
  intro index
  simp [empiricalFintypeIndicesInSet]

/--
Reindexing a nonempty finite empirical sample along an equivalence does not
change its empirical probability law.

Library provenance: the finite-cardinality steps use Mathlib's
`Fintype.card_of_subtype` and `Fintype.card_congr` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/Card.lean>,
and `Equiv.subtypeEquiv` from
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Logic/Equiv/Basic.lean>.
These pinned Mathlib sources are Apache-2.0; no external Lean source is copied
or ported.
-/
theorem empiricalFintypeProbabilityMeasure_comp_equiv
    {Index Target Sample : Type*} [Fintype Index] [Nonempty Index]
    [Fintype Target] [Nonempty Target]
    [MeasurableSpace Index] [MeasurableSingletonClass Index]
    [MeasurableSpace Target] [MeasurableSingletonClass Target]
    [MeasurableSpace Sample]
    (sample : Target → Sample) (e : Index ≃ Target) :
    empiricalFintypeProbabilityMeasure (sample ∘ e) =
      empiricalFintypeProbabilityMeasure sample := by
  apply Subtype.ext
  apply MeasureTheory.Measure.ext
  intro t ht
  have hleft := empiricalFintypeProbabilityMeasure_apply (sample ∘ e) t ht
  have hright := empiricalFintypeProbabilityMeasure_apply sample t ht
  letI : Fintype {index : Index // (sample ∘ e) index ∈ t} := Fintype.ofFinite _
  letI : Fintype {index : Target // sample index ∈ t} := Fintype.ofFinite _
  have hcard :
      (empiricalFintypeIndicesInSet (sample ∘ e) t).card =
        (empiricalFintypeIndicesInSet sample t).card := by
    calc
      (empiricalFintypeIndicesInSet (sample ∘ e) t).card =
          Fintype.card {index : Index // (sample ∘ e) index ∈ t} := by
            symm
            apply Fintype.card_of_subtype
            intro index
            simp [empiricalFintypeIndicesInSet]
      _ = Fintype.card {index : Target // sample index ∈ t} :=
        Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
      _ = (empiricalFintypeIndicesInSet sample t).card := by
            apply Fintype.card_of_subtype
            intro index
            simp [empiricalFintypeIndicesInSet]
  change (empiricalFintypeProbabilityMeasure (sample ∘ e)).val t =
    (empiricalFintypeProbabilityMeasure sample).val t
  calc
    (empiricalFintypeProbabilityMeasure (sample ∘ e)).val t =
        (empiricalFintypeIndicesInSet (sample ∘ e) t).card / Fintype.card Index := hleft
    _ = (empiricalFintypeIndicesInSet sample t).card / Fintype.card Target := by
      rw [hcard, Fintype.card_congr e]
    _ = (empiricalFintypeProbabilityMeasure sample).val t := hright.symm

/-- Membership in the selected finite index set is exactly membership of the observation in `s`. -/
theorem empiricalFintypeIndicesInSet_mem_iff
    {Index Sample : Type*} [Fintype Index]
    (sample : Index → Sample) (s : Set Sample) (index : Index) :
    index ∈ empiricalFintypeIndicesInSet sample s ↔ sample index ∈ s := by
  classical
  simp [empiricalFintypeIndicesInSet]

/-- The empirical PMF obtained by uniformly selecting one index of a nonempty sample. -/
noncomputable def empiricalSampleLaw {Sample : Type*} {count : ℕ}
    [Nonempty (Fin count)] (sample : Fin count → Sample) : PMF Sample :=
  (PMF.uniformOfFintype (Fin count)).map sample

/-- The probability-measure realization of a nonempty finite sample's empirical law. -/
noncomputable def empiricalSampleProbabilityMeasure {Sample : Type*} [MeasurableSpace Sample]
    {count : ℕ} [Nonempty (Fin count)] (sample : Fin count → Sample) :
    MeasureTheory.ProbabilityMeasure Sample :=
  ⟨(empiricalSampleLaw sample).toMeasure, inferInstance⟩

/-- The measure underlying the empirical probability law is the empirical PMF measure. -/
theorem empiricalSampleProbabilityMeasure_toMeasure {Sample : Type*} [MeasurableSpace Sample]
    {count : ℕ} [Nonempty (Fin count)] (sample : Fin count → Sample) :
    (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure Sample) =
      (empiricalSampleLaw sample).toMeasure :=
  rfl

/-- The `Fin count` empirical law is the corresponding general finite-index empirical law. -/
theorem empiricalSampleProbabilityMeasure_eq_empiricalFintypeProbabilityMeasure
    {Sample : Type*} [MeasurableSpace Sample] {count : ℕ} [Nonempty (Fin count)]
    (sample : Fin count → Sample) :
    empiricalSampleProbabilityMeasure sample = empiricalFintypeProbabilityMeasure sample := by
  rfl

/--
The empirical PMF with positivity supplied explicitly, for theorem statements
whose sample size varies with a non-typeclass index.
-/
noncomputable def empiricalSampleLawOfPos {Sample : Type*} {count : ℕ}
    (hcount : 0 < count) (sample : Fin count → Sample) : PMF Sample := by
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  exact empiricalSampleLaw sample

/-- The explicit-positive-size empirical PMF agrees with the instance-based form. -/
theorem empiricalSampleLawOfPos_eq_empiricalSampleLaw {Sample : Type*} {count : ℕ}
    [Nonempty (Fin count)] (hcount : 0 < count) (sample : Fin count → Sample) :
    empiricalSampleLawOfPos hcount sample = empiricalSampleLaw sample := by
  rfl

/-- The probability-measure empirical law with a nonempty sample size supplied explicitly. -/
noncomputable def empiricalSampleProbabilityMeasureOfPos
    {Sample : Type*} [MeasurableSpace Sample] {count : ℕ}
    (hcount : 0 < count) (sample : Fin count → Sample) :
    MeasureTheory.ProbabilityMeasure Sample := by
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  exact empiricalSampleProbabilityMeasure sample

/-- The explicit-positive-size empirical probability law agrees with the instance-based form. -/
theorem empiricalSampleProbabilityMeasureOfPos_eq_empiricalSampleProbabilityMeasure
    {Sample : Type*} [MeasurableSpace Sample] {count : ℕ} [Nonempty (Fin count)]
    (hcount : 0 < count) (sample : Fin count → Sample) :
    empiricalSampleProbabilityMeasureOfPos hcount sample =
      empiricalSampleProbabilityMeasure sample := by
  rfl

/-- The indices of a `Fin count` sample whose observations lie in `s`. -/
noncomputable def empiricalSampleIndicesInSet
    {Sample : Type*} {count : ℕ} (sample : Fin count → Sample) (s : Set Sample) :
    Finset (Fin count) :=
  empiricalFintypeIndicesInSet sample s

/--
A finite-IID membership pattern is exactly the fiber on which the empirical
selected-index finset takes its displayed value.  This deterministic bridge
is the finite partition needed to aggregate fixed-pattern conditional tails
without introducing an artificial factor for the number of patterns.

It only unfolds the local selected-index and membership-pattern definitions;
no new upstream Lean dependency or source material is introduced.
-/
theorem mem_finiteIIDMembershipPattern_iff_empiricalSampleIndicesInSet_eq
    {Sample : Type*} [MeasurableSpace Sample] {count : ℕ}
    (sample : Fin count → Sample) (inside : Finset (Fin count)) (s : Set Sample) :
    sample ∈ Probability.finiteIIDMembershipPattern count inside s ↔
      empiricalSampleIndicesInSet sample s = inside := by
  classical
  unfold Probability.finiteIIDMembershipPattern
  simp only [Set.mem_iInter, Set.mem_preimage]
  change (∀ index : Fin count,
    sample index ∈ if index ∈ inside then s else sᶜ) ↔
      empiricalSampleIndicesInSet sample s = inside
  constructor
  · intro hpattern
    apply Finset.Subset.antisymm
    · intro index hindex
      have hsample : sample index ∈ s :=
        (empiricalFintypeIndicesInSet_mem_iff sample s index).mp hindex
      by_contra hnotinside
      have hnotmem : sample index ∉ s := by
        simpa [hnotinside] using hpattern index
      exact hnotmem hsample
    · intro index hindex
      apply (empiricalFintypeIndicesInSet_mem_iff sample s index).mpr
      simpa [hindex] using hpattern index
  · intro hindices
    intro index
    by_cases hinside : index ∈ inside
    · have hsample : sample index ∈ s := by
        apply (empiricalFintypeIndicesInSet_mem_iff sample s index).mp
        change index ∈ empiricalSampleIndicesInSet sample s
        rw [hindices]
        exact hinside
      simpa [hinside] using hsample
    · have hnotmem : sample index ∉ s := by
        intro hsample
        apply hinside
        rw [← hindices]
        exact (empiricalFintypeIndicesInSet_mem_iff sample s index).mpr hsample
      simpa [hinside] using hnotmem

/-- The empirical sub-sample obtained by retaining exactly the observations in `s`. -/
noncomputable def empiricalSelectedSample
    {Sample : Type*} {count : ℕ} (sample : Fin count → Sample) (s : Set Sample) :
    empiricalSampleIndicesInSet sample s → Sample :=
  fun index => sample index

/-- The empirical probability law of a nonempty selected sub-sample. -/
noncomputable def empiricalSelectedProbabilityMeasure
    {Sample : Type*} [MeasurableSpace Sample] {count : ℕ}
    (sample : Fin count → Sample) (s : Set Sample)
    (hselected : (empiricalSampleIndicesInSet sample s).Nonempty) :
    MeasureTheory.ProbabilityMeasure Sample := by
  letI : Nonempty (empiricalSampleIndicesInSet sample s) := hselected.to_subtype
  exact empiricalFintypeProbabilityMeasure (empiricalSelectedSample sample s)

/--
The finite-`Fin` enumeration of an empirical selected sample has exactly the
same empirical law as the selected subtype-indexed sample.

This combines the local canonical finite-iid enumeration with the local
finite-equivalence invariance of empirical measures; it introduces no new
upstream Lean dependency or source material.
-/
theorem empiricalSampleProbabilityMeasure_finiteIIDSampleOnFinsetToFin
    {Sample : Type*} [MeasurableSpace Sample] {count : ℕ}
    (sample : Fin count → Sample) (s : Set Sample)
    (hselected : (empiricalSampleIndicesInSet sample s).Nonempty) :
    empiricalSampleProbabilityMeasureOfPos
      (Finset.card_pos.mpr hselected)
      (Probability.finiteIIDSampleOnFinsetToFin (empiricalSampleIndicesInSet sample s) sample) =
      empiricalSelectedProbabilityMeasure sample s hselected := by
  let inside := empiricalSampleIndicesInSet sample s
  let indexEquiv : Fin inside.card ≃ inside :=
    (finCongr (Fintype.card_coe inside).symm).trans (Fintype.equivFin inside).symm
  have hsample : Probability.finiteIIDSampleOnFinsetToFin inside sample =
      (empiricalSelectedSample sample s) ∘ indexEquiv := by
    rfl
  rw [hsample]
  letI : Nonempty (Fin inside.card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hselected)
  letI : Nonempty inside := hselected.to_subtype
  change empiricalFintypeProbabilityMeasure ((empiricalSelectedSample sample s) ∘ indexEquiv) =
    empiricalFintypeProbabilityMeasure (empiricalSelectedSample sample s)
  exact empiricalFintypeProbabilityMeasure_comp_equiv
    (empiricalSelectedSample sample s) indexEquiv

/-- Every observation of the selected empirical sub-sample lies in its selection set. -/
theorem empiricalSelectedSample_mem
    {Sample : Type*} {count : ℕ} (sample : Fin count → Sample) (s : Set Sample)
    (index : empiricalSampleIndicesInSet sample s) :
    empiricalSelectedSample sample s index ∈ s := by
  classical
  change sample index.1 ∈ s
  have hmem := index.2
  change index.1 ∈ Finset.univ.filter (fun i => sample i ∈ s) at hmem
  exact (Finset.mem_filter.mp hmem).2

/--
A measurable set containing a nonempty sub-sample has nonzero restriction of
the ambient finite empirical measure.  This isolates the positivity fact used
both by empirical reindexing and by conditional shell laws.
-/
theorem empiricalSampleProbabilityMeasure_restrict_ne_zero
    {Sample : Type*} [MeasurableSpace Sample] [Nonempty Sample]
    {count : ℕ} [Nonempty (Fin count)]
    (sample : Fin count → Sample) (s : Set Sample) (hs : MeasurableSet s)
    (hselected : (empiricalSampleIndicesInSet sample s).Nonempty) :
    (empiricalSampleProbabilityMeasure sample).toFiniteMeasure.restrict s ≠ 0 := by
  classical
  apply (MeasureTheory.FiniteMeasure.mass_nonzero_iff _).mp
  intro hzero
  have hmass : (((empiricalSampleProbabilityMeasure sample).toFiniteMeasure.restrict s).mass :
      ENNReal) =
      (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure Sample) s := by
    rw [MeasureTheory.FiniteMeasure.ennreal_mass]
    rw [MeasureTheory.FiniteMeasure.restrict_apply_measure _ _ MeasurableSet.univ]
    simp
  have hzero' : (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure Sample) s = 0 := by
    rw [← hmass]
    exact ENNReal.coe_eq_zero.mpr hzero
  rw [empiricalSampleProbabilityMeasure_eq_empiricalFintypeProbabilityMeasure,
    empiricalFintypeProbabilityMeasure_apply sample s hs] at hzero'
  exact (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hselected.card_ne_zero,
    ENNReal.natCast_ne_top _⟩) hzero'

/--
Restricting a nonempty finite empirical measure to a measurable set and
normalizing is exactly the empirical probability measure of the observations
selected by that set. This is the deterministic reindexing seam needed before
a conditional-IID argument can identify the selected observations' law.

Library provenance: the counting formula uses Mathlib's
`PMF.toMeasure_map_apply` and `PMF.toMeasure_uniformOfFintype_apply` from
[`ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean)
and [`Probability/Distributions/Uniform.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Distributions/Uniform.lean).
The normalization and restriction identities are Mathlib's
`FiniteMeasure.normalize_eq_of_nonzero`, `restrict_mass`, and `restrict_apply`
from [`MeasureTheory/Measure/FiniteMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean).
The finite-subtype cardinal identities are Mathlib's `Fintype.card_of_subtype`
from [`Data/Fintype/Card.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/Card.lean).
All are used at the pinned Apache-2.0 Mathlib commit; no source text is copied
or ported.
-/
theorem empiricalSelectedSampleProbabilityMeasure_eq_normalize_restrict
    {Sample : Type*} [MeasurableSpace Sample] [Nonempty Sample]
    {count : ℕ} [Nonempty (Fin count)]
    (sample : Fin count → Sample) (s : Set Sample) (hs : MeasurableSet s)
    (hselected : (empiricalSampleIndicesInSet sample s).Nonempty) :
    ((empiricalSampleProbabilityMeasure sample).toFiniteMeasure.restrict s).normalize =
      empiricalSelectedProbabilityMeasure sample s hselected := by
  classical
  letI : Nonempty (empiricalSampleIndicesInSet sample s) := hselected.to_subtype
  have hmass : (((empiricalSampleProbabilityMeasure sample).toFiniteMeasure.restrict s).mass :
      ENNReal) =
      (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure Sample) s := by
    rw [MeasureTheory.FiniteMeasure.ennreal_mass]
    rw [MeasureTheory.FiniteMeasure.restrict_apply_measure _ _ MeasurableSet.univ]
    simp
  have hmass_nonzero :
      ((empiricalSampleProbabilityMeasure sample).toFiniteMeasure.restrict s).mass ≠ 0 := by
    intro hzero
    have hzero' : (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure Sample) s = 0 := by
      rw [← hmass]
      exact ENNReal.coe_eq_zero.mpr hzero
    rw [empiricalSampleProbabilityMeasure_eq_empiricalFintypeProbabilityMeasure,
      empiricalFintypeProbabilityMeasure_apply sample s hs] at hzero'
    exact (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hselected.card_ne_zero,
      ENNReal.natCast_ne_top _⟩) hzero'
  apply MeasureTheory.ProbabilityMeasure.eq_of_forall_apply_eq
  intro t ht
  rw [MeasureTheory.FiniteMeasure.normalize_eq_of_nonzero _
    ((MeasureTheory.FiniteMeasure.mass_nonzero_iff _).mp hmass_nonzero),
    MeasureTheory.FiniteMeasure.restrict_mass, MeasureTheory.FiniteMeasure.restrict_apply _ _ ht]
  apply ENNReal.coe_injective
  simp only [MeasureTheory.ProbabilityMeasure.toFiniteMeasure_apply]
  simp only [ENNReal.coe_mul, MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [empiricalSampleProbabilityMeasure_eq_empiricalFintypeProbabilityMeasure]
  have hsample_mass_nonzero : (empiricalFintypeProbabilityMeasure sample) s ≠ 0 := by
    intro hzero
    have hzero' : (empiricalFintypeProbabilityMeasure sample : MeasureTheory.Measure Sample) s = 0 := by
      rw [← MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact ENNReal.coe_eq_zero.mpr hzero
    rw [empiricalFintypeProbabilityMeasure_apply sample s hs] at hzero'
    exact (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hselected.card_ne_zero,
      ENNReal.natCast_ne_top _⟩) hzero'
  rw [ENNReal.coe_inv hsample_mass_nonzero]
  rw [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure
    (empiricalFintypeProbabilityMeasure sample) s]
  change ((empiricalFintypeProbabilityMeasure sample : MeasureTheory.Measure Sample) s)⁻¹ *
      (empiricalFintypeProbabilityMeasure sample : MeasureTheory.Measure Sample) (t ∩ s) =
        (empiricalSelectedProbabilityMeasure sample s hselected : MeasureTheory.Measure Sample) t
  have hright : (empiricalSelectedProbabilityMeasure sample s hselected :
      MeasureTheory.Measure Sample) t =
      (empiricalFintypeProbabilityMeasure (empiricalSelectedSample sample s) :
        MeasureTheory.Measure Sample) t := by
    rfl
  rw [empiricalFintypeProbabilityMeasure_apply sample s hs,
    empiricalFintypeProbabilityMeasure_apply sample (t ∩ s) (ht.inter hs), hright,
    empiricalFintypeProbabilityMeasure_apply (empiricalSelectedSample sample s) t ht]
  have hcard_selected_t :
      (empiricalFintypeIndicesInSet (empiricalSelectedSample sample s) t).card =
        (empiricalFintypeIndicesInSet sample (t ∩ s)).card := by
    let selected := empiricalSampleIndicesInSet sample s
    have hselected_mem {index : Fin count} (hindex : index ∈ selected) : sample index ∈ s := by
      change index ∈ Finset.univ.filter (fun i => sample i ∈ s) at hindex
      exact (Finset.mem_filter.mp hindex).2
    let reindex : {index : selected // sample index.1 ∈ t} ≃
        {index : Fin count // sample index ∈ t ∩ s} :=
      { toFun := fun index => ⟨index.1.1, index.2, hselected_mem index.1.2⟩
        invFun := fun index => ⟨⟨index.1, by
          change index.1 ∈ Finset.univ.filter (fun i => sample i ∈ s)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, index.2.2⟩⟩, index.2.1⟩
        left_inv := by
          intro index
          rfl
        right_inv := by
          intro index
          rfl }
    calc
      (empiricalFintypeIndicesInSet (empiricalSelectedSample sample s) t).card =
          Fintype.card {index : selected // sample index.1 ∈ t} := by
            symm
            apply Fintype.card_of_subtype
            intro index
            simp [empiricalFintypeIndicesInSet, empiricalSelectedSample, selected]
      _ = Fintype.card {index : Fin count // sample index ∈ t ∩ s} :=
            Fintype.card_congr reindex
      _ = (empiricalFintypeIndicesInSet sample (t ∩ s)).card := by
            apply Fintype.card_of_subtype
            intro index
            simp [empiricalFintypeIndicesInSet]
  rw [hcard_selected_t, Fintype.card_coe (empiricalSampleIndicesInSet sample s)]
  have hselected_card_nonzero :
      ((empiricalSampleIndicesInSet sample s).card : ENNReal) ≠ 0 := by
    exact_mod_cast hselected.card_ne_zero
  have hcount_card_nonzero : ((Fintype.card (Fin count) : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hselected_card_ne_top :
      ((empiricalSampleIndicesInSet sample s).card : ENNReal) ≠ (⊤ : ENNReal) :=
    ENNReal.natCast_ne_top _
  have hcount_card_ne_top :
      ((Fintype.card (Fin count) : ℕ) : ENNReal) ≠ (⊤ : ENNReal) :=
    ENNReal.natCast_ne_top _
  rw [ENNReal.inv_div (Or.inl hcount_card_ne_top) (Or.inl hcount_card_nonzero)]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  change _ = ((empiricalFintypeIndicesInSet sample s).card : ENNReal)⁻¹ *
    (empiricalFintypeIndicesInSet sample (t ∩ s)).card
  calc
    ((empiricalFintypeIndicesInSet sample s).card : ENNReal)⁻¹ *
        (Fintype.card (Fin count) : ENNReal) *
          ((Fintype.card (Fin count) : ENNReal)⁻¹ *
            (empiricalFintypeIndicesInSet sample (t ∩ s)).card) =
        ((empiricalFintypeIndicesInSet sample s).card : ENNReal)⁻¹ *
          ((Fintype.card (Fin count) : ENNReal) *
            (Fintype.card (Fin count) : ENNReal)⁻¹) *
              (empiricalFintypeIndicesInSet sample (t ∩ s)).card := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel hcount_card_nonzero hcount_card_ne_top]
      simp

/--
Pushing an empirical probability law through a measurable map is exactly the
empirical law of the mapped sample.
-/
theorem map_empiricalSampleProbabilityMeasure
    {Sample Target : Type*} [MeasurableSpace Sample] [MeasurableSpace Target]
    {count : ℕ} [Nonempty (Fin count)] (sample : Fin count → Sample)
    (f : Sample → Target) (hf : Measurable f) :
    (empiricalSampleProbabilityMeasure sample).map hf.aemeasurable =
      empiricalSampleProbabilityMeasure (f ∘ sample) := by
  apply Subtype.ext
  change MeasureTheory.Measure.map f ((empiricalSampleLaw sample).toMeasure) =
    (empiricalSampleLaw (f ∘ sample)).toMeasure
  rw [show empiricalSampleLaw (f ∘ sample) = (empiricalSampleLaw sample).map f by
    simp only [empiricalSampleLaw, ← PMF.map_comp]]
  rw [PMF.toMeasure_map f (empiricalSampleLaw sample) hf]

/-- Explicit-positive-size form of `map_empiricalSampleProbabilityMeasure`. -/
theorem map_empiricalSampleProbabilityMeasureOfPos
    {Sample Target : Type*} [MeasurableSpace Sample] [MeasurableSpace Target]
    {count : ℕ} (hcount : 0 < count) (sample : Fin count → Sample)
    (f : Sample → Target) (hf : Measurable f) :
    (empiricalSampleProbabilityMeasureOfPos hcount sample).map hf.aemeasurable =
      empiricalSampleProbabilityMeasureOfPos hcount (f ∘ sample) := by
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp hcount
  change (empiricalSampleProbabilityMeasure sample).map hf.aemeasurable =
    empiricalSampleProbabilityMeasure (f ∘ sample)
  exact map_empiricalSampleProbabilityMeasure sample f hf

/--
An empirical probability law assigns zero mass to every measurable set missed
by every sampled observation. This is the finite-support bridge used when a
finite sample is partitioned into countably many dyadic shells.

Library provenance: this directly uses Mathlib's `PMF.toMeasure_map` from
[`Probability/ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean)
and `Measure.map_apply` from
[`MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No source text is copied or
ported.
-/
theorem empiricalSampleProbabilityMeasure_apply_eq_zero_of_forall_not_mem
    {Sample : Type*} [MeasurableSpace Sample]
    {count : ℕ} [Nonempty (Fin count)] (sample : Fin count → Sample)
    (s : Set Sample) (hs : MeasurableSet s)
    (hnotmem : ∀ index, sample index ∉ s) :
    (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure Sample) s = 0 := by
  rw [empiricalSampleProbabilityMeasure_toMeasure,
    show empiricalSampleLaw sample = (PMF.uniformOfFintype (Fin count)).map sample by rfl,
    ← PMF.toMeasure_map sample (PMF.uniformOfFintype (Fin count)) (measurable_of_finite sample),
    MeasureTheory.Measure.map_apply (measurable_of_finite sample) hs]
  have hpreimage : sample ⁻¹' s = ∅ := by
    ext index
    simp [hnotmem index]
  rw [hpreimage, MeasureTheory.measure_empty]

/--
Every nonempty finite empirical law on a second-countable normed Borel space
has an integrable norm.  Thus only the population law needs a first-moment
assumption when forming a finite real W₁ comparison with an empirical sample.
-/
theorem integrable_norm_empiricalSampleProbabilityMeasure
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {count : ℕ} [Nonempty (Fin count)]
    (sample : Fin count → E) :
    MeasureTheory.Integrable (fun x : E => ‖x‖)
      (empiricalSampleProbabilityMeasure sample : MeasureTheory.Measure E) := by
  rw [empiricalSampleProbabilityMeasure_toMeasure,
    show (empiricalSampleLaw sample).toMeasure =
      ((PMF.uniformOfFintype (Fin count)).map sample).toMeasure by rfl]
  rw [← PMF.toMeasure_map sample (PMF.uniformOfFintype (Fin count))
    (measurable_of_finite sample)]
  refine (MeasureTheory.integrable_map_measure measurable_norm.aestronglyMeasurable
    (measurable_of_finite sample).aemeasurable).mpr ?_
  exact MeasureTheory.Integrable.of_finite

end AppliedModelingLib
