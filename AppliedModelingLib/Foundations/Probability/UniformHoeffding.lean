import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# Finite uniform Hoeffding bounds

Reusable concentration bounds for a finite collection of independent bounded
observations.  The uniform theorem is a direct union bound over a finite
hypothesis family; VC arguments can subsequently replace that family by the
finite set of traces realized on a sample.
-/

open scoped BigOperators ProbabilityTheory NNReal

namespace AppliedModelingLib
namespace Probability

open MeasureTheory ProbabilityTheory

/--
The centered sum of independent `[0,1]` observations satisfies the one-sided
Hoeffding upper tail.  Identical distribution is not needed for this base
concentration result.
-/
theorem boundedIIndep_centeredSum_upperTail
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : ℕ → Ω → ℝ) (count : ℕ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | (count : ℝ) * error ≤
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let centered : ℕ → Ω → ℝ :=
    fun index outcome => observation index outcome - law[observation index]
  have hcentered_independent : iIndepFun centered law := by
    simpa [centered, Function.comp_def] using
      hindependent.comp
        (fun index value => value - law[observation index])
        (fun _ => measurable_id.sub measurable_const)
  have hsubgaussian : ∀ index < count,
      HasSubgaussianMGF
        (centered index) ((2 : ℝ≥0) ^ 2)⁻¹ law := by
    intro index hindex
    simpa using
      (hasSubgaussianMGF_of_mem_Icc (hmeasurable index).aemeasurable
        (hbounded index hindex) (a := (0 : ℝ)) (b := (1 : ℝ)))
  convert
    (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hcentered_independent hsubgaussian
      (mul_nonneg (Nat.cast_nonneg count) herror)) using 1
  norm_num [centered]

/--
Finite-index form of `boundedIIndep_centeredSum_upperTail`.  This is useful
when independent observations are naturally indexed by a finite product or a
disjoint union, rather than by a prefix of `ℕ`.
-/
theorem boundedIIndep_centeredSum_upperTail_finset
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Index → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | error ≤
      ∑ index, (observation index outcome - law[observation index])} ≤
      Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
  let centered : Index → Ω → ℝ :=
    fun index outcome => observation index outcome - law[observation index]
  have hcentered_independent : iIndepFun centered law := by
    simpa [centered, Function.comp_def] using
      hindependent.comp
        (fun index value => value - law[observation index])
        (fun _ => measurable_id.sub measurable_const)
  have hsubgaussian : ∀ index,
      HasSubgaussianMGF
        (centered index) ((2 : ℝ≥0) ^ 2)⁻¹ law := by
    intro index
    simpa using
      (hasSubgaussianMGF_of_mem_Icc (hmeasurable index).aemeasurable
        (hbounded index) (a := (0 : ℝ)) (b := (1 : ℝ)))
  convert
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcentered_independent
      (s := Finset.univ) (fun index _ => hsubgaussian index) herror) using 1
  norm_num [centered]
  ring

/-- The finite-index lower-tail companion to the bounded Hoeffding bound. -/
theorem boundedIIndep_centeredSum_lowerTail_finset
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Index → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome |
      ∑ index, (observation index outcome - law[observation index]) ≤ -error} ≤
      Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
  let complement : Index → Ω → ℝ := fun index outcome => 1 - observation index outcome
  have hcomplement_independent : iIndepFun complement law := by
    simpa [complement, Function.comp_def] using
      hindependent.comp (fun _ value => 1 - value)
        (fun _ => measurable_const.sub measurable_id)
  have hcomplement_measurable : ∀ index, Measurable (complement index) := by
    intro index
    exact measurable_const.sub (hmeasurable index)
  have hcomplement_bounded : ∀ index, ∀ᵐ outcome ∂law,
      complement index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    filter_upwards [hbounded index] with outcome hvalue
    constructor <;> linarith [hvalue.1, hvalue.2]
  have hcomplement_mean : ∀ index,
      law[complement index] = 1 - law[observation index] := by
    intro index
    have hintegrable : Integrable (observation index) law :=
      Integrable.of_mem_Icc 0 1 (hmeasurable index).aemeasurable (hbounded index)
    simp only [complement]
    rw [integral_sub (integrable_const _) hintegrable]
    simp
  have hsum : ∀ outcome,
      (∑ index, (complement index outcome - law[complement index])) =
        -(∑ index, (observation index outcome - law[observation index])) := by
    intro outcome
    calc
      (∑ index, (complement index outcome - law[complement index])) =
          ∑ index, -(observation index outcome - law[observation index]) := by
            apply Finset.sum_congr rfl
            intro index _
            rw [hcomplement_mean index]
            simp only [complement]
            ring
      _ = -(∑ index, (observation index outcome - law[observation index])) := by
        rw [Finset.sum_neg_distrib]
  have hevent : {outcome |
      ∑ index, (observation index outcome - law[observation index]) ≤ -error} =
      {outcome | error ≤
        ∑ index, (complement index outcome - law[complement index])} := by
    ext outcome
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact boundedIIndep_centeredSum_upperTail_finset law complement
    hcomplement_independent hcomplement_measurable hcomplement_bounded error herror

/-- The matching lower tail for independent bounded observations. -/
theorem boundedIIndep_centeredSum_lowerTail
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : ℕ → Ω → ℝ) (count : ℕ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome |
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index]) ≤ -(count : ℝ) * error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let complement : ℕ → Ω → ℝ := fun index outcome => 1 - observation index outcome
  have hcomplement_independent : iIndepFun complement law := by
    simpa [complement, Function.comp_def] using
      hindependent.comp (fun _ value => 1 - value)
        (fun _ => measurable_const.sub measurable_id)
  have hcomplement_measurable : ∀ index, Measurable (complement index) := by
    intro index
    exact measurable_const.sub (hmeasurable index)
  have hcomplement_bounded : ∀ index < count, ∀ᵐ outcome ∂law,
      complement index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index hindex
    filter_upwards [hbounded index hindex] with outcome hvalue
    constructor <;> linarith [hvalue.1, hvalue.2]
  have hcomplement_mean : ∀ index < count,
      law[complement index] = 1 - law[observation index] := by
    intro index hindex
    have hintegrable : Integrable (observation index) law :=
      Integrable.of_mem_Icc 0 1 (hmeasurable index).aemeasurable (hbounded index hindex)
    simp only [complement]
    rw [integral_sub (integrable_const _) hintegrable]
    simp
  have hsum : ∀ outcome,
      (∑ index ∈ Finset.range count,
        (complement index outcome - law[complement index])) =
      -(∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) := by
    intro outcome
    calc
      (∑ index ∈ Finset.range count,
          (complement index outcome - law[complement index])) =
          ∑ index ∈ Finset.range count,
            -(observation index outcome - law[observation index]) := by
              apply Finset.sum_congr rfl
              intro index hindex
              rw [hcomplement_mean index (Finset.mem_range.mp hindex)]
              simp only [complement]
              ring
      _ = -(∑ index ∈ Finset.range count,
          (observation index outcome - law[observation index])) := by
            rw [Finset.sum_neg_distrib]
  have hevent : {outcome |
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index]) ≤ -(count : ℝ) * error} =
      {outcome | (count : ℝ) * error ≤
        ∑ index ∈ Finset.range count,
          (complement index outcome - law[complement index])} := by
    ext outcome
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact boundedIIndep_centeredSum_upperTail law complement count
    hcomplement_independent hcomplement_measurable hcomplement_bounded error herror

/-- The two-sided Hoeffding bound for one independent bounded observation path. -/
theorem boundedIIndep_centeredSum_abs_upperTail
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : ℕ → Ω → ℝ) (count : ℕ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | (count : ℝ) * error ≤
      |∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])|} ≤
      2 * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let upperEvent : Set Ω := {outcome | (count : ℝ) * error ≤
    ∑ index ∈ Finset.range count,
      (observation index outcome - law[observation index])}
  let lowerEvent : Set Ω := {outcome |
    ∑ index ∈ Finset.range count,
      (observation index outcome - law[observation index]) ≤ -(count : ℝ) * error}
  have hupper : law.real upperEvent ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
    boundedIIndep_centeredSum_upperTail law observation count
      hindependent hmeasurable hbounded error herror
  have hlower : law.real lowerEvent ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
    boundedIIndep_centeredSum_lowerTail law observation count
      hindependent hmeasurable hbounded error herror
  let absoluteEvent : Set Ω := {outcome | (count : ℝ) * error ≤
    |∑ index ∈ Finset.range count,
      (observation index outcome - law[observation index])|}
  have hsubset : absoluteEvent ⊆ upperEvent ∪ lowerEvent := by
    intro outcome habsolute
    change (count : ℝ) * error ≤
      |∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])| at habsolute
    change ((count : ℝ) * error ≤
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) ∨
      ((∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) ≤ -(count : ℝ) * error)
    rcases le_abs.mp habsolute with hupper | hnegated
    · exact Or.inl hupper
    · right
      linarith
  calc
    law.real absoluteEvent ≤ law.real (upperEvent ∪ lowerEvent) :=
      measureReal_mono hsubset
    _ ≤ law.real upperEvent + law.real lowerEvent := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
          nlinarith [hupper, hlower]

/--
A finite hypothesis family obeys a uniform two-sided Hoeffding bound.  Each
hypothesis may use a different independent observation path; this separation
makes the union-bound layer reusable for trace-representative arguments.
-/
theorem finite_uniform_boundedIIndep_centeredSum_abs_upperTail
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] [Fintype Hypothesis]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Hypothesis → ℕ → Ω → ℝ) (count : ℕ)
    (hindependent : ∀ (hypothesis : Hypothesis), iIndepFun (observation hypothesis) law)
    (hmeasurable : ∀ (hypothesis : Hypothesis) (index : ℕ),
      Measurable (observation hypothesis index))
    (hbounded : ∀ (hypothesis : Hypothesis) (index : ℕ), index < count →
      ∀ᵐ outcome ∂law, observation hypothesis index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      (count : ℝ) * error ≤
        |∑ index ∈ Finset.range count,
          (observation hypothesis index outcome - law[observation hypothesis index])|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  classical
  let bad : Hypothesis → Set Ω := fun hypothesis => {outcome |
    (count : ℝ) * error ≤
      |∑ index ∈ Finset.range count,
        (observation hypothesis index outcome - law[observation hypothesis index])|}
  have hbad : ∀ hypothesis, law.real (bad hypothesis) ≤
      2 * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    intro hypothesis
    exact boundedIIndep_centeredSum_abs_upperTail law (observation hypothesis) count
      (hindependent hypothesis) (hmeasurable hypothesis) (hbounded hypothesis) error herror
  have hbad_union : {outcome | ∃ hypothesis,
      (count : ℝ) * error ≤
        |∑ index ∈ Finset.range count,
          (observation hypothesis index outcome - law[observation hypothesis index])|} =
      ⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis := by
    ext outcome
    simp [bad]
  rw [hbad_union]
  calc
    law.real (⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis) ≤
        ∑ hypothesis ∈ (Finset.univ : Finset Hypothesis), law.real (bad hypothesis) := by
      simpa using (measureReal_biUnion_finset_le (μ := law)
        (Finset.univ : Finset Hypothesis) bad)
    _ ≤ ∑ _hypothesis ∈ (Finset.univ : Finset Hypothesis),
        2 * Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
      apply Finset.sum_le_sum
      intro hypothesis _
      exact hbad hypothesis
    _ = (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
      simp [mul_assoc, mul_comm]

/-- The finite-index two-sided Hoeffding bound for one independent bounded path. -/
theorem boundedIIndep_centeredSum_abs_upperTail_finset
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Index → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | error ≤
      |∑ index, (observation index outcome - law[observation index])|} ≤
      2 * Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
  let upperEvent : Set Ω := {outcome | error ≤
    ∑ index, (observation index outcome - law[observation index])}
  let lowerEvent : Set Ω := {outcome |
    ∑ index, (observation index outcome - law[observation index]) ≤ -error}
  have hupper : law.real upperEvent ≤
      Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) :=
    boundedIIndep_centeredSum_upperTail_finset law observation
      hindependent hmeasurable hbounded error herror
  have hlower : law.real lowerEvent ≤
      Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) :=
    boundedIIndep_centeredSum_lowerTail_finset law observation
      hindependent hmeasurable hbounded error herror
  let absoluteEvent : Set Ω := {outcome | error ≤
    |∑ index, (observation index outcome - law[observation index])|}
  have hsubset : absoluteEvent ⊆ upperEvent ∪ lowerEvent := by
    intro outcome habsolute
    change error ≤
      |∑ index, (observation index outcome - law[observation index])| at habsolute
    change (error ≤
      ∑ index, (observation index outcome - law[observation index])) ∨
      ((∑ index, (observation index outcome - law[observation index]) ≤ -error))
    rcases le_abs.mp habsolute with hupper | hnegated
    · exact Or.inl hupper
    · right
      linarith
  calc
    law.real absoluteEvent ≤ law.real (upperEvent ∪ lowerEvent) :=
      measureReal_mono hsubset
    _ ≤ law.real upperEvent + law.real lowerEvent := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
      nlinarith [hupper, hlower]

/--
A finite hypothesis family obeys the same uniform two-sided Hoeffding bound
when observations are indexed directly by an arbitrary finite type. This
avoids padding a finite iid sample to a natural-number-indexed sequence.
-/
theorem finite_uniform_boundedIIndep_centeredSum_abs_upperTail_finset
    {Ω Hypothesis Index : Type*} [MeasurableSpace Ω] [Fintype Hypothesis] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Hypothesis → Index → Ω → ℝ)
    (hindependent : ∀ hypothesis, iIndepFun (observation hypothesis) law)
    (hmeasurable : ∀ hypothesis index, Measurable (observation hypothesis index))
    (hbounded : ∀ hypothesis index, ∀ᵐ outcome ∂law,
      observation hypothesis index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      error ≤ |∑ index, (observation hypothesis index outcome -
        law[observation hypothesis index])|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-error ^ 2 /
          (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
  classical
  let bad : Hypothesis → Set Ω := fun hypothesis => {outcome |
    error ≤ |∑ index, (observation hypothesis index outcome -
      law[observation hypothesis index])|}
  have hbad : ∀ hypothesis, law.real (bad hypothesis) ≤
      2 * Real.exp (-error ^ 2 /
        (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
    intro hypothesis
    exact boundedIIndep_centeredSum_abs_upperTail_finset law
      (observation hypothesis) (hindependent hypothesis) (hmeasurable hypothesis)
      (hbounded hypothesis) error herror
  have hbad_union : {outcome | ∃ hypothesis,
      error ≤ |∑ index, (observation hypothesis index outcome -
        law[observation hypothesis index])|} =
      ⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis := by
    ext outcome
    simp [bad]
  rw [hbad_union]
  calc
    law.real (⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis) ≤
        ∑ hypothesis ∈ (Finset.univ : Finset Hypothesis), law.real (bad hypothesis) := by
      simpa using (measureReal_biUnion_finset_le (μ := law)
        (Finset.univ : Finset Hypothesis) bad)
    _ ≤ ∑ _hypothesis ∈ (Finset.univ : Finset Hypothesis),
        2 * Real.exp (-error ^ 2 /
          (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
      apply Finset.sum_le_sum
      intro hypothesis _
      exact hbad hypothesis
    _ = (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-error ^ 2 /
          (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
      simp [mul_assoc, mul_comm]

/-- The empirical mean of observations indexed by an arbitrary finite type. -/
noncomputable def finiteEmpiricalMean
    {Ω Hypothesis Index : Type*} [Fintype Index]
    (observation : Hypothesis → Index → Ω → ℝ)
    (hypothesis : Hypothesis) (outcome : Ω) : ℝ :=
  (∑ index, observation hypothesis index outcome) / (Fintype.card Index : ℝ)

/--
Uniform finite-family Hoeffding bound stated directly for a finite-index
empirical mean. The common expectation is supplied explicitly, so this result
also applies to finite iid products and other independently sampled designs.
-/
theorem finite_uniform_finiteEmpiricalMean_abs_gt
    {Ω Hypothesis Index : Type*} [MeasurableSpace Ω] [Fintype Hypothesis]
    [Fintype Index] [Nonempty Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Hypothesis → Index → Ω → ℝ)
    (hindependent : ∀ hypothesis, iIndepFun (observation hypothesis) law)
    (hmean : Hypothesis → ℝ)
    (hsame_mean : ∀ hypothesis index, law[observation hypothesis index] = hmean hypothesis)
    (hmeasurable : ∀ hypothesis index, Measurable (observation hypothesis index))
    (hbounded : ∀ hypothesis index, ∀ᵐ outcome ∂law,
      observation hypothesis index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      error < |finiteEmpiricalMean observation hypothesis outcome - hmean hypothesis|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-((Fintype.card Index : ℝ) * error) ^ 2 /
          (2 * (Fintype.card Index : ℝ) * (1 / 4 : ℝ))) := by
  classical
  have hcard_pos : 0 < (Fintype.card Index : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty Index)
  have hsubset : {outcome | ∃ hypothesis,
      error < |finiteEmpiricalMean observation hypothesis outcome - hmean hypothesis|} ⊆
      {outcome | ∃ hypothesis,
        (Fintype.card Index : ℝ) * error ≤
          |∑ index, (observation hypothesis index outcome -
            law[observation hypothesis index])|} := by
    intro outcome houtcome
    rcases houtcome with ⟨hypothesis, hdeviation⟩
    refine ⟨hypothesis, ?_⟩
    have hsum :
        (∑ index, (observation hypothesis index outcome -
          law[observation hypothesis index])) =
        (Fintype.card Index : ℝ) *
          (finiteEmpiricalMean observation hypothesis outcome - hmean hypothesis) := by
      calc
        (∑ index, (observation hypothesis index outcome -
          law[observation hypothesis index])) =
            ∑ index, (observation hypothesis index outcome - hmean hypothesis) := by
              apply Finset.sum_congr rfl
              intro index _
              rw [hsame_mean hypothesis index]
        _ = (Fintype.card Index : ℝ) *
            (finiteEmpiricalMean observation hypothesis outcome - hmean hypothesis) := by
              unfold finiteEmpiricalMean
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              have hcard_ne : (Fintype.card Index : ℝ) ≠ 0 := ne_of_gt hcard_pos
              field_simp [hcard_ne]
    rw [hsum, abs_mul, abs_of_nonneg hcard_pos.le]
    exact le_of_lt (mul_lt_mul_of_pos_left hdeviation hcard_pos)
  exact (measureReal_mono hsubset).trans
    (finite_uniform_boundedIIndep_centeredSum_abs_upperTail_finset law observation
      hindependent hmeasurable hbounded ((Fintype.card Index : ℝ) * error)
      (mul_nonneg hcard_pos.le herror))

/-- The empirical mean of a finite observation prefix. -/
noncomputable def empiricalMean
    {Ω Hypothesis : Type*} (observation : Hypothesis → ℕ → Ω → ℝ)
    (count : ℕ) (hypothesis : Hypothesis) (outcome : Ω) : ℝ :=
  (∑ index ∈ Finset.range count, observation hypothesis index outcome) / (count : ℝ)

/-- The population mean represented by the zeroth coordinate of an iid path. -/
noncomputable def populationMean
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    (observation : Hypothesis → ℕ → Ω → ℝ) (hypothesis : Hypothesis) : ℝ :=
  law[observation hypothesis 0]

/-- The unit-interval Hoeffding exponent simplifies to its familiar form. -/
theorem boundedHoeffdingExponent_eq_neg_two_mul
    (count : ℕ) (hcount : 0 < count) (error : ℝ) :
    -((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)) =
      -2 * (count : ℝ) * error ^ 2 := by
  have hcount_real : (count : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcount
  field_simp [hcount_real]
  ring

/--
Uniform finite-class generalization from iid bounded losses.  The
`hsame_mean` condition is the identical-distribution part of iid sampling,
while `hindependent` is its independence part.  The event is deliberately
strict, matching the usual VC-generalization statement.
-/
theorem finite_uniform_empiricalMean_abs_gt
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] [Fintype Hypothesis]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Hypothesis → ℕ → Ω → ℝ) (count : ℕ) (hcount : 0 < count)
    (hindependent : ∀ (hypothesis : Hypothesis), iIndepFun (observation hypothesis) law)
    (hsame_mean : ∀ (hypothesis : Hypothesis) (index : ℕ),
      law[observation hypothesis index] = law[observation hypothesis 0])
    (hmeasurable : ∀ (hypothesis : Hypothesis) (index : ℕ),
      Measurable (observation hypothesis index))
    (hbounded : ∀ (hypothesis : Hypothesis) (index : ℕ), index < count →
      ∀ᵐ outcome ∂law, observation hypothesis index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      error < |empiricalMean observation count hypothesis outcome -
        populationMean law observation hypothesis|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  classical
  have hcount_real_pos : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hsubset : {outcome | ∃ hypothesis,
      error < |empiricalMean observation count hypothesis outcome -
        populationMean law observation hypothesis|} ⊆
      {outcome | ∃ hypothesis,
        (count : ℝ) * error ≤
          |∑ index ∈ Finset.range count,
            (observation hypothesis index outcome - law[observation hypothesis index])|} := by
    intro outcome houtcome
    rcases houtcome with ⟨hypothesis, hdeviation⟩
    refine ⟨hypothesis, ?_⟩
    have hsum :
        (∑ index ∈ Finset.range count,
          (observation hypothesis index outcome - law[observation hypothesis index])) =
        (count : ℝ) *
          (empiricalMean observation count hypothesis outcome -
            populationMean law observation hypothesis) := by
      calc
        (∑ index ∈ Finset.range count,
            (observation hypothesis index outcome - law[observation hypothesis index])) =
            ∑ index ∈ Finset.range count,
              (observation hypothesis index outcome -
                populationMean law observation hypothesis) := by
              apply Finset.sum_congr rfl
              intro index _
              rw [populationMean, hsame_mean hypothesis index]
        _ = (count : ℝ) *
            (empiricalMean observation count hypothesis outcome -
              populationMean law observation hypothesis) := by
              unfold empiricalMean
              have hcount_ne : (count : ℝ) ≠ 0 := ne_of_gt hcount_real_pos
              rw [Finset.sum_sub_distrib]
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              field_simp [hcount_ne]
    rw [hsum, abs_mul, abs_of_nonneg hcount_real_pos.le]
    exact le_of_lt (mul_lt_mul_of_pos_left hdeviation hcount_real_pos)
  exact (measureReal_mono hsubset).trans
    (finite_uniform_boundedIIndep_centeredSum_abs_upperTail law observation count
      hindependent hmeasurable hbounded error herror)

/-- The finite iid generalization bound in the standard `exp (-2 N ε²)` form. -/
theorem finite_uniform_empiricalMean_abs_gt_exp_neg_two_mul
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] [Fintype Hypothesis]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Hypothesis → ℕ → Ω → ℝ) (count : ℕ) (hcount : 0 < count)
    (hindependent : ∀ (hypothesis : Hypothesis), iIndepFun (observation hypothesis) law)
    (hsame_mean : ∀ (hypothesis : Hypothesis) (index : ℕ),
      law[observation hypothesis index] = law[observation hypothesis 0])
    (hmeasurable : ∀ (hypothesis : Hypothesis) (index : ℕ),
      Measurable (observation hypothesis index))
    (hbounded : ∀ (hypothesis : Hypothesis) (index : ℕ), index < count →
      ∀ᵐ outcome ∂law, observation hypothesis index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      error < |empiricalMean observation count hypothesis outcome -
        populationMean law observation hypothesis|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) * error ^ 2) := by
  simpa only [boundedHoeffdingExponent_eq_neg_two_mul count hcount error] using
    finite_uniform_empiricalMean_abs_gt law observation count hcount hindependent hsame_mean
      hmeasurable hbounded error herror

/--
A finite family of lower/upper brackets transfers a one-sided uniform
population-minus-empirical deviation to the lower bracket functions.  The
probabilistic concentration of those finitely many lower brackets is supplied
separately, so this deterministic event inclusion applies to entropy,
bracketing, and finite-state arguments alike.
-/
theorem uniform_populationMean_sub_empiricalMean_gt_le_of_finite_brackets
    {Ω Parameter Net : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (score : Parameter → ℕ → Ω → ℝ)
    (lowerBracket upperBracket : Net → ℕ → Ω → ℝ)
    (count : ℕ) (parameterSet : Set Parameter) (choose : Parameter → Net)
    (tolerance width tail : ℝ)
    (hempirical_lower : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      empiricalMean lowerBracket count (choose parameter) outcome ≤
        empiricalMean score count parameter outcome)
    (hpopulation_upper : ∀ parameter, parameter ∈ parameterSet →
      populationMean law score parameter ≤
        populationMean law upperBracket (choose parameter))
    (hbracket_width : ∀ bracket,
      populationMean law upperBracket bracket -
        populationMean law lowerBracket bracket ≤ width)
    (hlower_tail : law.real {outcome | ∃ bracket,
      tolerance - width < |empiricalMean lowerBracket count bracket outcome -
        populationMean law lowerBracket bracket|} ≤ tail) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < populationMean law score parameter -
        empiricalMean score count parameter outcome} ≤ tail := by
  apply (measureReal_mono ?_).trans hlower_tail
  rintro outcome ⟨parameter, hparameter, hdeviation⟩
  refine ⟨choose parameter, ?_⟩
  have hlower := hempirical_lower parameter hparameter outcome
  have hupper := hpopulation_upper parameter hparameter
  have hwidth := hbracket_width (choose parameter)
  have hgap : tolerance - width <
      populationMean law lowerBracket (choose parameter) -
        empiricalMean lowerBracket count (choose parameter) outcome := by
    linarith
  rw [abs_sub_comm]
  exact lt_of_lt_of_le hgap (le_abs_self _)

/--
A finite cover transfers a uniform empirical-mean deviation event from an
arbitrary parameter set to its finite set of centers.  The hypotheses make the
two approximation errors explicit: `empiricalApproximation` controls every
realized sample average and `populationApproximation` controls its expectation.

This is measure-space general.  The finite-class concentration input is
`finite_uniform_empiricalMean_abs_gt_exp_neg_two_mul`, which in turn uses
Mathlib's independent sub-Gaussian Hoeffding bound.
-/
theorem uniform_empiricalMean_abs_gt_le_of_finite_cover
    {Ω Parameter Net : Type*} [MeasurableSpace Ω] [Fintype Net]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Parameter → ℕ → Ω → ℝ) (count : ℕ) (hcount : 0 < count)
    (parameterSet : Set Parameter) (center : Net → Parameter) (choose : Parameter → Net)
    (tolerance approximation : ℝ)
    (hindependent : ∀ parameter, iIndepFun (observation parameter) law)
    (hsameMean : ∀ parameter index,
      law[observation parameter index] = law[observation parameter 0])
    (hmeasurable : ∀ parameter index, Measurable (observation parameter index))
    (hbounded : ∀ parameter index, index < count →
      ∀ᵐ outcome ∂law, observation parameter index outcome ∈ Set.Icc (0 : ℝ) 1)
    (empiricalApproximation : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      |empiricalMean observation count parameter outcome -
          empiricalMean observation count (center (choose parameter)) outcome| ≤ approximation)
    (populationApproximation : ∀ parameter, parameter ∈ parameterSet →
      |populationMean law observation parameter -
          populationMean law observation (center (choose parameter))| ≤ approximation)
    (herror : 0 ≤ tolerance - 2 * approximation) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < |empiricalMean observation count parameter outcome -
        populationMean law observation parameter|} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) * (tolerance - 2 * approximation) ^ 2) := by
  have hsubset :
      {outcome | ∃ parameter, parameter ∈ parameterSet ∧
        tolerance < |empiricalMean observation count parameter outcome -
          populationMean law observation parameter|} ⊆
        {outcome | ∃ net,
          tolerance - 2 * approximation <
            |empiricalMean (fun net => observation (center net)) count net outcome -
              populationMean law (fun net => observation (center net)) net|} := by
    intro outcome houtcome
    rcases houtcome with ⟨parameter, hparameter, hdeviation⟩
    let net := choose parameter
    have hempirical := empiricalApproximation parameter hparameter outcome
    have hpopulation := populationApproximation parameter hparameter
    have hpopulation' :
        |populationMean law observation parameter -
            populationMean law observation (center net)| ≤ approximation := by
      simpa [net] using hpopulation
    have hbound :
        |empiricalMean observation count parameter outcome -
            populationMean law observation parameter| ≤
          |empiricalMean observation count (center net) outcome -
              populationMean law observation (center net)| + 2 * approximation := by
      calc
        |empiricalMean observation count parameter outcome -
            populationMean law observation parameter| ≤
            |empiricalMean observation count parameter outcome -
                empiricalMean observation count (center net) outcome| +
              |empiricalMean observation count (center net) outcome -
                populationMean law observation parameter| :=
          abs_sub_le _ _ _
        _ ≤ |empiricalMean observation count parameter outcome -
                empiricalMean observation count (center net) outcome| +
              (|empiricalMean observation count (center net) outcome -
                  populationMean law observation (center net)| +
                |populationMean law observation (center net) -
                  populationMean law observation parameter|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ ≤ |empiricalMean observation count (center net) outcome -
                populationMean law observation (center net)| + 2 * approximation := by
          rw [abs_sub_comm (populationMean law observation (center net))
            (populationMean law observation parameter)]
          linarith
    refine ⟨net, ?_⟩
    have : tolerance <
        |empiricalMean observation count (center (choose parameter)) outcome -
            populationMean law observation (center (choose parameter))| + 2 * approximation :=
      lt_of_lt_of_le hdeviation hbound
    have hcenter : tolerance - 2 * approximation <
        |empiricalMean observation count (center net) outcome -
            populationMean law observation (center net)| := by
      have hcenter' : tolerance - 2 * approximation <
          |empiricalMean observation count (center (choose parameter)) outcome -
              populationMean law observation (center (choose parameter))| := by
        linarith
      simpa [net] using hcenter'
    simpa [net] using hcenter
  refine (measureReal_mono hsubset).trans ?_
  simpa using
    (finite_uniform_empiricalMean_abs_gt_exp_neg_two_mul law
      (fun net => observation (center net)) count hcount
      (fun net => hindependent (center net))
      (fun net index => hsameMean (center net) index)
      (fun net index => hmeasurable (center net) index)
      (fun net index hindex => hbounded (center net) index hindex)
      (tolerance - 2 * approximation) herror)

/-- Dividing every observation by a scalar divides its empirical mean by that scalar. -/
theorem empiricalMean_div
    {Ω Hypothesis : Type*} (observation : Hypothesis → ℕ → Ω → ℝ)
    (count : ℕ) (hypothesis : Hypothesis) (outcome : Ω) (bound : ℝ) :
    empiricalMean (fun parameter index sample => observation parameter index sample / bound)
        count hypothesis outcome =
      empiricalMean observation count hypothesis outcome / bound := by
  unfold empiricalMean
  change
    (∑ index ∈ Finset.range count, observation hypothesis index outcome / bound) /
        (count : ℝ) =
      ((∑ index ∈ Finset.range count, observation hypothesis index outcome) /
        (count : ℝ)) / bound
  rw [← Finset.sum_div]
  ring

/-- Translating every observation translates its empirical mean by the same constant. -/
theorem empiricalMean_sub_const
    {Ω Hypothesis : Type*} (observation : Hypothesis → ℕ → Ω → ℝ)
    (count : ℕ) (hcount : 0 < count) (hypothesis : Hypothesis) (outcome : Ω) (offset : ℝ) :
    empiricalMean (fun parameter index sample => observation parameter index sample - offset)
        count hypothesis outcome =
      empiricalMean observation count hypothesis outcome - offset := by
  unfold empiricalMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcount_ne : (count : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcount
  field_simp [hcount_ne]

/-- Dividing an integrable observation by a scalar divides its population mean by that scalar. -/
theorem populationMean_div
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    (observation : Hypothesis → ℕ → Ω → ℝ) (hypothesis : Hypothesis) (bound : ℝ) :
    populationMean law (fun parameter index sample => observation parameter index sample / bound)
        hypothesis = populationMean law observation hypothesis / bound := by
  unfold populationMean
  change (∫ sample, observation hypothesis 0 sample / bound ∂law) = _
  rw [integral_div bound]

/-- Translating an integrable observation translates its population mean by that constant. -/
theorem populationMean_sub_const
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Hypothesis → ℕ → Ω → ℝ)
    (hypothesis : Hypothesis) (offset : ℝ)
    (hintegrable : Integrable (observation hypothesis 0) law) :
    populationMean law (fun parameter index sample => observation parameter index sample - offset)
        hypothesis = populationMean law observation hypothesis - offset := by
  unfold populationMean
  change (∫ sample, observation hypothesis 0 sample - offset ∂law) = _
  rw [integral_sub hintegrable (integrable_const _)]
  simp

/--
A uniform pointwise score bound transfers directly to the corresponding
empirical means.  This is the deterministic half of a metric-cover argument.
-/
theorem empiricalMean_abs_sub_le_of_pointwise_bound
    {Ω Hypothesis : Type*} (observation : Hypothesis → ℕ → Ω → ℝ)
    (count : ℕ) (hcount : 0 < count) (first second : Hypothesis)
    (outcome : Ω) (approximation : ℝ)
    (hpointwise : ∀ index < count,
      |observation first index outcome - observation second index outcome| ≤ approximation) :
    |empiricalMean observation count first outcome -
        empiricalMean observation count second outcome| ≤ approximation := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  unfold empiricalMean
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcount_real]
  apply (div_le_iff₀ hcount_real).2
  calc
    |∑ index ∈ Finset.range count,
        (observation first index outcome - observation second index outcome)| ≤
        ∑ index ∈ Finset.range count,
          |observation first index outcome - observation second index outcome| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index ∈ Finset.range count, approximation := by
      apply Finset.sum_le_sum
      intro index hindex
      exact hpointwise index (Finset.mem_range.mp hindex)
    _ = approximation * (count : ℝ) := by
      simp [mul_comm]

/--
A pointwise almost-everywhere score bound transfers to population means under
a probability law.  Integrability of the two scores is kept explicit.
-/
theorem populationMean_abs_sub_le_of_ae_pointwise_bound
    {Ω Hypothesis : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Hypothesis → ℕ → Ω → ℝ)
    (first second : Hypothesis) (approximation : ℝ)
    (hintegrable_first : Integrable (observation first 0) law)
    (hintegrable_second : Integrable (observation second 0) law)
    (hpointwise : ∀ᵐ outcome ∂law,
      |observation first 0 outcome - observation second 0 outcome| ≤ approximation) :
    |populationMean law observation first - populationMean law observation second| ≤
      approximation := by
  unfold populationMean
  rw [← integral_sub hintegrable_first hintegrable_second]
  calc
    |∫ outcome, observation first 0 outcome - observation second 0 outcome ∂law| ≤
        approximation * law.real Set.univ := by
      simpa using
        (norm_integral_le_of_norm_le_const
          (f := fun outcome => observation first 0 outcome - observation second 0 outcome)
          hpointwise)
    _ = approximation := by simp

/-- Measurable post-processing preserves independence of an iid sample path. -/
theorem iIndepFun_score_comp
    {Ω Sample : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample] (law : Measure Ω)
    (sample : ℕ → Ω → Sample) (score : Sample → ℝ)
    (hindependent : iIndepFun sample law) (hscore_measurable : Measurable score) :
    iIndepFun (fun index outcome => score (sample index outcome)) law := by
  simpa [Function.comp_def] using
    hindependent.comp (fun _ value => score value) (fun _ => hscore_measurable)

/-- Measurable post-processing preserves equality of expectations under identical laws. -/
theorem score_comp_integral_eq_of_identDistrib
    {Ω Sample : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample]
    (law : Measure Ω) (sample : ℕ → Ω → Sample) (score : Sample → ℝ)
    (hscore_measurable : Measurable score)
    (hsame : ∀ index, IdentDistrib (sample index) (sample 0) law law)
    (index : ℕ) :
    law[fun outcome => score (sample index outcome)] =
      law[fun outcome => score (sample 0 outcome)] := by
  simpa [Function.comp_def] using ((hsame index).comp hscore_measurable).integral_eq

/-- A measurable score composed with a measurable sample coordinate is measurable. -/
theorem measurable_score_comp
    {Ω Sample : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample]
    (sample : ℕ → Ω → Sample) (score : Sample → ℝ)
    (hsample_measurable : ∀ index, Measurable (sample index))
    (hscore_measurable : Measurable score) (index : ℕ) :
    Measurable (fun outcome => score (sample index outcome)) :=
  hscore_measurable.comp (hsample_measurable index)

/--
Finite-cover Hoeffding transfer for scores in an arbitrary interval `[0, B]`.
The result is obtained by normalizing the scores to `[0,1]`; its exponent is
therefore stated in the paper-friendly normalized form.  This is valid on an
arbitrary probability space, not only on a finite sample support.
-/
theorem uniform_empiricalMean_abs_gt_le_of_finite_cover_of_mem_Icc
    {Ω Parameter Net : Type*} [MeasurableSpace Ω] [Fintype Net]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Parameter → ℕ → Ω → ℝ) (count : ℕ) (hcount : 0 < count)
    (parameterSet : Set Parameter) (center : Net → Parameter) (choose : Parameter → Net)
    (bound tolerance approximation : ℝ) (hbound_pos : 0 < bound)
    (hindependent : ∀ parameter, iIndepFun (observation parameter) law)
    (hsameMean : ∀ parameter index,
      law[observation parameter index] = law[observation parameter 0])
    (hmeasurable : ∀ parameter index, Measurable (observation parameter index))
    (hbounded : ∀ parameter index,
      ∀ᵐ outcome ∂law, observation parameter index outcome ∈ Set.Icc (0 : ℝ) bound)
    (empiricalApproximation : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      |empiricalMean observation count parameter outcome -
          empiricalMean observation count (center (choose parameter)) outcome| ≤ approximation)
    (populationApproximation : ∀ parameter, parameter ∈ parameterSet →
      |populationMean law observation parameter -
          populationMean law observation (center (choose parameter))| ≤ approximation)
    (herror : 0 ≤ tolerance - 2 * approximation) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < |empiricalMean observation count parameter outcome -
        populationMean law observation parameter|} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) *
          (tolerance / bound - 2 * (approximation / bound)) ^ 2) := by
  let normalized : Parameter → ℕ → Ω → ℝ :=
    fun parameter index outcome => observation parameter index outcome / bound
  have hnormalized_independent : ∀ parameter, iIndepFun (normalized parameter) law := by
    intro parameter
    simpa [normalized, Function.comp_def] using
      (hindependent parameter).comp (fun _ value => value / bound)
        (fun _ => measurable_id.div measurable_const)
  have hnormalized_sameMean : ∀ parameter index,
      law[normalized parameter index] = law[normalized parameter 0] := by
    intro parameter index
    have hintegrable_index : Integrable (observation parameter index) law :=
      Integrable.of_mem_Icc 0 bound (hmeasurable parameter index).aemeasurable
        (hbounded parameter index)
    have hintegrable_zero : Integrable (observation parameter 0) law :=
      Integrable.of_mem_Icc 0 bound (hmeasurable parameter 0).aemeasurable
        (hbounded parameter 0)
    simp only [normalized]
    rw [integral_div bound, integral_div bound, hsameMean]
  have hnormalized_measurable : ∀ parameter index, Measurable (normalized parameter index) := by
    intro parameter index
    exact (hmeasurable parameter index).div measurable_const
  have hnormalized_bounded : ∀ parameter index, index < count →
      ∀ᵐ outcome ∂law, normalized parameter index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro parameter index _
    filter_upwards [hbounded parameter index] with outcome houtcome
    constructor
    · exact div_nonneg houtcome.1 hbound_pos.le
    · exact (div_le_iff₀ hbound_pos).2 (by simpa using houtcome.2)
  have hnormalized_empirical : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      |empiricalMean normalized count parameter outcome -
          empiricalMean normalized count (center (choose parameter)) outcome| ≤
        approximation / bound := by
    intro parameter hparameter outcome
    rw [empiricalMean_div, empiricalMean_div, ← sub_div, abs_div,
      abs_of_pos hbound_pos]
    apply (div_le_iff₀ hbound_pos).2
    calc
      |empiricalMean observation count parameter outcome -
          empiricalMean observation count (center (choose parameter)) outcome| ≤ approximation :=
        empiricalApproximation parameter hparameter outcome
      _ = (approximation / bound) * bound := by field_simp
  have hnormalized_population : ∀ parameter, parameter ∈ parameterSet →
      |populationMean law normalized parameter -
          populationMean law normalized (center (choose parameter))| ≤
        approximation / bound := by
    intro parameter hparameter
    rw [populationMean_div, populationMean_div, ← sub_div, abs_div,
      abs_of_pos hbound_pos]
    apply (div_le_iff₀ hbound_pos).2
    calc
      |populationMean law observation parameter -
          populationMean law observation (center (choose parameter))| ≤ approximation :=
        populationApproximation parameter hparameter
      _ = (approximation / bound) * bound := by field_simp
  have hnormalized_error : 0 ≤ tolerance / bound - 2 * (approximation / bound) := by
    have hscale : tolerance / bound - 2 * (approximation / bound) =
        (tolerance - 2 * approximation) / bound := by ring
    rw [hscale]
    exact div_nonneg herror hbound_pos.le
  have hnormalized := uniform_empiricalMean_abs_gt_le_of_finite_cover law normalized count hcount
    parameterSet center choose (tolerance / bound) (approximation / bound)
    hnormalized_independent hnormalized_sameMean hnormalized_measurable hnormalized_bounded
    hnormalized_empirical hnormalized_population hnormalized_error
  have hevent : {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < |empiricalMean observation count parameter outcome -
        populationMean law observation parameter|} =
      {outcome | ∃ parameter, parameter ∈ parameterSet ∧
        tolerance / bound < |empiricalMean normalized count parameter outcome -
          populationMean law normalized parameter|} := by
    ext outcome
    constructor
    · rintro ⟨parameter, hparameter, hdeviation⟩
      refine ⟨parameter, hparameter, ?_⟩
      rw [empiricalMean_div, populationMean_div, ← sub_div, abs_div, abs_of_pos hbound_pos]
      exact (div_lt_div_iff_of_pos_right hbound_pos).2 hdeviation
    · rintro ⟨parameter, hparameter, hdeviation⟩
      refine ⟨parameter, hparameter, ?_⟩
      rw [empiricalMean_div, populationMean_div, ← sub_div, abs_div, abs_of_pos hbound_pos] at hdeviation
      exact (div_lt_div_iff_of_pos_right hbound_pos).1 hdeviation
  rw [hevent]
  exact hnormalized

/--
Finite-cover Hoeffding transfer for scores in an arbitrary bounded interval
`[lower, upper]`.  Translation to `[0, upper - lower]` leaves every empirical
minus population deviation unchanged, so the range width is the only scale in
the exponent.
-/
theorem uniform_empiricalMean_abs_gt_le_of_finite_cover_of_mem_Icc_affine
    {Ω Parameter Net : Type*} [MeasurableSpace Ω] [Fintype Net]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Parameter → ℕ → Ω → ℝ) (count : ℕ) (hcount : 0 < count)
    (parameterSet : Set Parameter) (center : Net → Parameter) (choose : Parameter → Net)
    (lower upper tolerance approximation : ℝ) (hwidth_pos : 0 < upper - lower)
    (hindependent : ∀ parameter, iIndepFun (observation parameter) law)
    (hsameMean : ∀ parameter index,
      law[observation parameter index] = law[observation parameter 0])
    (hmeasurable : ∀ parameter index, Measurable (observation parameter index))
    (hbounded : ∀ parameter index,
      ∀ᵐ outcome ∂law, observation parameter index outcome ∈ Set.Icc lower upper)
    (empiricalApproximation : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      |empiricalMean observation count parameter outcome -
          empiricalMean observation count (center (choose parameter)) outcome| ≤ approximation)
    (populationApproximation : ∀ parameter, parameter ∈ parameterSet →
      |populationMean law observation parameter -
          populationMean law observation (center (choose parameter))| ≤ approximation)
    (herror : 0 ≤ tolerance - 2 * approximation) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < |empiricalMean observation count parameter outcome -
        populationMean law observation parameter|} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) *
          (tolerance / (upper - lower) -
            2 * (approximation / (upper - lower))) ^ 2) := by
  let shifted : Parameter → ℕ → Ω → ℝ :=
    fun parameter index outcome => observation parameter index outcome - lower
  have hempirical_shift : ∀ parameter outcome,
      empiricalMean shifted count parameter outcome =
        empiricalMean observation count parameter outcome - lower := by
    intro parameter outcome
    exact empiricalMean_sub_const observation count hcount parameter outcome lower
  have hpopulation_shift : ∀ parameter,
      populationMean law shifted parameter = populationMean law observation parameter - lower := by
    intro parameter
    exact populationMean_sub_const law observation parameter lower
      (Integrable.of_mem_Icc lower upper (hmeasurable parameter 0).aemeasurable
        (hbounded parameter 0))
  have hshifted_independent : ∀ parameter, iIndepFun (shifted parameter) law := by
    intro parameter
    simpa [shifted, Function.comp_def] using
      (hindependent parameter).comp (fun _ value => value - lower)
        (fun _ => measurable_id.sub measurable_const)
  have hshifted_sameMean : ∀ parameter index,
      law[shifted parameter index] = law[shifted parameter 0] := by
    intro parameter index
    have hintegrable_index : Integrable (observation parameter index) law :=
      Integrable.of_mem_Icc lower upper (hmeasurable parameter index).aemeasurable
        (hbounded parameter index)
    have hintegrable_zero : Integrable (observation parameter 0) law :=
      Integrable.of_mem_Icc lower upper (hmeasurable parameter 0).aemeasurable
        (hbounded parameter 0)
    simp only [shifted]
    rw [integral_sub hintegrable_index (integrable_const _),
      integral_sub hintegrable_zero (integrable_const _), hsameMean]
  have hshifted_measurable : ∀ parameter index, Measurable (shifted parameter index) := by
    intro parameter index
    exact (hmeasurable parameter index).sub measurable_const
  have hshifted_bounded : ∀ parameter index,
      ∀ᵐ outcome ∂law, shifted parameter index outcome ∈ Set.Icc (0 : ℝ) (upper - lower) := by
    intro parameter index
    filter_upwards [hbounded parameter index] with outcome houtcome
    constructor <;> linarith [houtcome.1, houtcome.2]
  have hshifted_empirical : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      |empiricalMean shifted count parameter outcome -
          empiricalMean shifted count (center (choose parameter)) outcome| ≤ approximation := by
    intro parameter hparameter outcome
    rw [hempirical_shift, hempirical_shift]
    convert empiricalApproximation parameter hparameter outcome using 1
    ring
  have hshifted_population : ∀ parameter, parameter ∈ parameterSet →
      |populationMean law shifted parameter -
          populationMean law shifted (center (choose parameter))| ≤ approximation := by
    intro parameter hparameter
    rw [hpopulation_shift, hpopulation_shift]
    convert populationApproximation parameter hparameter using 1
    ring
  have hshifted := uniform_empiricalMean_abs_gt_le_of_finite_cover_of_mem_Icc law
    shifted count hcount parameterSet center choose (upper - lower) tolerance approximation
    hwidth_pos hshifted_independent hshifted_sameMean hshifted_measurable hshifted_bounded
    hshifted_empirical hshifted_population herror
  have hevent : {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < |empiricalMean observation count parameter outcome -
        populationMean law observation parameter|} =
      {outcome | ∃ parameter, parameter ∈ parameterSet ∧
        tolerance < |empiricalMean shifted count parameter outcome -
          populationMean law shifted parameter|} := by
    ext outcome
    constructor <;> rintro ⟨parameter, hparameter, hdeviation⟩
    · refine ⟨parameter, hparameter, ?_⟩
      rw [hempirical_shift, hpopulation_shift]
      convert hdeviation using 1
      ring
    · refine ⟨parameter, hparameter, ?_⟩
      rw [hempirical_shift, hpopulation_shift] at hdeviation
      convert hdeviation using 1
      ring
  rw [hevent]
  exact hshifted

/--
Hoeffding concentration for the one-sided uniform deviation controlled by a
finite family of real-valued brackets.  The bracket width is measured in the
population mean, so no pointwise closeness or finite cover of the full class
is required.
-/
theorem uniform_populationMean_sub_empiricalMean_gt_le_of_finite_brackets_affine
    {Ω Parameter Net : Type*} [MeasurableSpace Ω] [Fintype Net]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (score : Parameter → ℕ → Ω → ℝ)
    (lowerBracket upperBracket : Net → ℕ → Ω → ℝ)
    (count : ℕ) (hcount : 0 < count) (parameterSet : Set Parameter)
    (choose : Parameter → Net) (lower upper tolerance width : ℝ)
    (hwidth_pos : 0 < upper - lower)
    (hlower_independent : ∀ bracket, iIndepFun (lowerBracket bracket) law)
    (hlower_sameMean : ∀ bracket index,
      law[lowerBracket bracket index] = law[lowerBracket bracket 0])
    (hlower_measurable : ∀ bracket index, Measurable (lowerBracket bracket index))
    (hlower_bounded : ∀ bracket index,
      ∀ᵐ outcome ∂law, lowerBracket bracket index outcome ∈ Set.Icc lower upper)
    (hempirical_lower : ∀ parameter, parameter ∈ parameterSet → ∀ outcome,
      empiricalMean lowerBracket count (choose parameter) outcome ≤
        empiricalMean score count parameter outcome)
    (hpopulation_upper : ∀ parameter, parameter ∈ parameterSet →
      populationMean law score parameter ≤
        populationMean law upperBracket (choose parameter))
    (hbracket_width : ∀ bracket,
      populationMean law upperBracket bracket -
        populationMean law lowerBracket bracket ≤ width)
    (herror : 0 ≤ tolerance - width) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance < populationMean law score parameter -
        empiricalMean score count parameter outcome} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) * ((tolerance - width) / (upper - lower)) ^ 2) := by
  have hlower_tail : law.real {outcome | ∃ bracket,
      tolerance - width < |empiricalMean lowerBracket count bracket outcome -
        populationMean law lowerBracket bracket|} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) * ((tolerance - width) / (upper - lower)) ^ 2) := by
    simpa using
      (uniform_empiricalMean_abs_gt_le_of_finite_cover_of_mem_Icc_affine
        law lowerBracket count hcount Set.univ id id lower upper (tolerance - width) 0
        hwidth_pos hlower_independent hlower_sameMean hlower_measurable hlower_bounded
        (fun bracket _ outcome => by simp)
        (fun bracket _ => by simp) (by simpa using herror))
  exact uniform_populationMean_sub_empiricalMean_gt_le_of_finite_brackets
    law score lowerBracket upperBracket count parameterSet choose tolerance width _
    hempirical_lower hpopulation_upper hbracket_width hlower_tail

/--
Uniform finite-cover concentration for iid scores in an arbitrary bounded
interval.  The score is evaluated on an iid sample path; measurable
post-processing supplies the independence and identical-mean hypotheses.
-/
theorem uniform_empiricalMean_abs_gt_le_of_iid_score_cover_affine
    {Ω Sample Parameter Net : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample]
    [PseudoMetricSpace Parameter] [Fintype Net]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (sample : ℕ → Ω → Sample) (score : Parameter → Sample → ℝ)
    (parameterSet : Set Parameter) (center : Net → Parameter) (choose : Parameter → Net)
    (lower upper radius lipschitz tolerance : ℝ) (count : ℕ)
    (hwidth_pos : 0 < upper - lower) (hcount : 0 < count)
    (hsample_independent : iIndepFun sample law)
    (hsample_measurable : ∀ index, Measurable (sample index))
    (hsample_identDistrib : ∀ index, IdentDistrib (sample index) (sample 0) law law)
    (hscore_measurable : ∀ parameter, Measurable (score parameter))
    (hscore_bounded : ∀ parameter sample,
      score parameter sample ∈ Set.Icc lower upper)
    (hcover : ∀ parameter, parameter ∈ parameterSet →
      dist parameter (center (choose parameter)) ≤ radius)
    (hlipschitz : ∀ first second sample,
      |score first sample - score second sample| ≤ lipschitz * dist first second)
    (hlipschitz_nonneg : 0 ≤ lipschitz)
    (herror : 0 ≤ tolerance - 2 * (lipschitz * radius)) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance <
        |empiricalMean (fun parameter index outcome => score parameter (sample index outcome))
            count parameter outcome -
          populationMean law
            (fun parameter index outcome => score parameter (sample index outcome)) parameter|} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) *
          (tolerance / (upper - lower) -
            2 * ((lipschitz * radius) / (upper - lower))) ^ 2) := by
  apply uniform_empiricalMean_abs_gt_le_of_finite_cover_of_mem_Icc_affine law
    (fun parameter index outcome => score parameter (sample index outcome)) count hcount
    parameterSet center choose lower upper tolerance (lipschitz * radius) hwidth_pos
  · intro parameter
    exact iIndepFun_score_comp law sample (score parameter) hsample_independent
      (hscore_measurable parameter)
  · intro parameter index
    exact score_comp_integral_eq_of_identDistrib law sample (score parameter)
      (hscore_measurable parameter) hsample_identDistrib index
  · intro parameter index
    exact measurable_score_comp sample (score parameter) hsample_measurable
      (hscore_measurable parameter) index
  · intro parameter index
    filter_upwards with outcome
    exact hscore_bounded parameter (sample index outcome)
  · intro parameter hparameter outcome
    apply empiricalMean_abs_sub_le_of_pointwise_bound
      (fun parameter index outcome => score parameter (sample index outcome)) count hcount
      parameter (center (choose parameter)) outcome
    intro index _
    calc
      |score parameter (sample index outcome) -
          score (center (choose parameter)) (sample index outcome)| ≤
          lipschitz * dist parameter (center (choose parameter)) :=
        hlipschitz parameter (center (choose parameter)) (sample index outcome)
      _ ≤ lipschitz * radius :=
        mul_le_mul_of_nonneg_left (hcover parameter hparameter) hlipschitz_nonneg
  · intro parameter hparameter
    apply populationMean_abs_sub_le_of_ae_pointwise_bound law
      (fun parameter index outcome => score parameter (sample index outcome))
      parameter (center (choose parameter)) (lipschitz * radius)
    · exact Integrable.of_mem_Icc lower upper
        (measurable_score_comp sample (score parameter) hsample_measurable
          (hscore_measurable parameter) 0).aemeasurable (by
            filter_upwards with outcome
            exact hscore_bounded parameter (sample 0 outcome))
    · exact Integrable.of_mem_Icc lower upper
        (measurable_score_comp sample (score (center (choose parameter))) hsample_measurable
          (hscore_measurable (center (choose parameter))) 0).aemeasurable (by
            filter_upwards with outcome
            exact hscore_bounded (center (choose parameter)) (sample 0 outcome))
    filter_upwards with outcome
    calc
      |score parameter (sample 0 outcome) -
          score (center (choose parameter)) (sample 0 outcome)| ≤
          lipschitz * dist parameter (center (choose parameter)) :=
        hlipschitz parameter (center (choose parameter)) (sample 0 outcome)
      _ ≤ lipschitz * radius :=
        mul_le_mul_of_nonneg_left (hcover parameter hparameter) hlipschitz_nonneg
  · exact herror

/--
Uniform finite-cover concentration for scores evaluated on an iid sample
process in `[0,B]`.  This is the nonnegative specialization of the affine
interval theorem above.
-/
theorem uniform_empiricalMean_abs_gt_le_of_iid_score_cover
    {Ω Sample Parameter Net : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample]
    [PseudoMetricSpace Parameter] [Fintype Net]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (sample : ℕ → Ω → Sample) (score : Parameter → Sample → ℝ)
    (parameterSet : Set Parameter) (center : Net → Parameter) (choose : Parameter → Net)
    (bound radius lipschitz tolerance : ℝ) (count : ℕ)
    (hbound_pos : 0 < bound) (hcount : 0 < count)
    (hsample_independent : iIndepFun sample law)
    (hsample_measurable : ∀ index, Measurable (sample index))
    (hsample_identDistrib : ∀ index, IdentDistrib (sample index) (sample 0) law law)
    (hscore_measurable : ∀ parameter, Measurable (score parameter))
    (hscore_bounded : ∀ parameter sample,
      score parameter sample ∈ Set.Icc (0 : ℝ) bound)
    (hcover : ∀ parameter, parameter ∈ parameterSet →
      dist parameter (center (choose parameter)) ≤ radius)
    (hlipschitz : ∀ first second sample,
      |score first sample - score second sample| ≤ lipschitz * dist first second)
    (hlipschitz_nonneg : 0 ≤ lipschitz)
    (herror : 0 ≤ tolerance - 2 * (lipschitz * radius)) :
    law.real {outcome | ∃ parameter, parameter ∈ parameterSet ∧
      tolerance <
        |empiricalMean (fun parameter index outcome => score parameter (sample index outcome))
            count parameter outcome -
          populationMean law
            (fun parameter index outcome => score parameter (sample index outcome)) parameter|} ≤
      (Fintype.card Net : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) *
          (tolerance / bound - 2 * ((lipschitz * radius) / bound)) ^ 2) := by
  simpa using
    (uniform_empiricalMean_abs_gt_le_of_iid_score_cover_affine law sample score
      parameterSet center choose 0 bound radius lipschitz tolerance count
      (by simpa using hbound_pos) hcount hsample_independent hsample_measurable
      hsample_identDistrib hscore_measurable hscore_bounded hcover hlipschitz
      hlipschitz_nonneg herror)

end Probability
end AppliedModelingLib
