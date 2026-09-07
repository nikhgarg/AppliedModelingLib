import FalahatgarEtAl2017MaxingRanking.CanonicalComparisonBatches

/-!
# Finite-batch iid concentration

The finite Bernoulli batches used by `Compare` have only the coordinates that
the algorithm can read. These Hoeffding bounds therefore take independence on
`Fin count`, rather than requiring an unused infinite observation stream.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The upper Hoeffding tail for a finite independent family in `[0,1]`. -/
theorem finiteIidBoundedObservation_centeredSum_upperTail
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω) [IsProbabilityMeasure law]
    (count : ℕ) (observation : Fin count → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | (count : ℝ) * error ≤
      ∑ index : Fin count, (observation index outcome - law[observation index])} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let centered : Fin count → Ω → ℝ :=
    fun index outcome => observation index outcome - law[observation index]
  have hcenteredIndependent : iIndepFun centered law := by
    simpa [centered, Function.comp_def] using
      hindependent.comp
        (fun index value => value - law[observation index])
        (fun _ => measurable_id.sub measurable_const)
  have hsubgaussian : ∀ index ∈ (Finset.univ : Finset (Fin count)),
      HasSubgaussianMGF (centered index) ((2 : NNReal) ^ 2)⁻¹ law := by
    intro index _
    simpa using
      (hasSubgaussianMGF_of_mem_Icc (hmeasurable index).aemeasurable (hbounded index)
        (a := (0 : ℝ)) (b := (1 : ℝ)))
  convert HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcenteredIndependent
    hsubgaussian (mul_nonneg (Nat.cast_nonneg count) herror) using 1
  all_goals norm_num [centered, Finset.sum_const, nsmul_eq_mul]
  all_goals ring

/-- The matching lower Hoeffding tail for a finite independent family in `[0,1]`. -/
theorem finiteIidBoundedObservation_centeredSum_lowerTail
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω) [IsProbabilityMeasure law]
    (count : ℕ) (observation : Fin count → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome |
      (∑ index : Fin count, (observation index outcome - law[observation index])) ≤
        -(count : ℝ) * error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let complement : Fin count → Ω → ℝ := fun index outcome => 1 - observation index outcome
  have hcomplementIndependent : iIndepFun complement law := by
    simpa [complement, Function.comp_def] using
      hindependent.comp (fun _ value => 1 - value)
        (fun _ => measurable_const.sub measurable_id)
  have hcomplementMeasurable : ∀ index, Measurable (complement index) := by
    intro index
    exact measurable_const.sub (hmeasurable index)
  have hcomplementBounded : ∀ index, ∀ᵐ outcome ∂law,
      complement index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    filter_upwards [hbounded index] with outcome hvalue
    constructor <;> linarith [hvalue.1, hvalue.2]
  have hcomplementMean : ∀ index, law[complement index] = 1 - law[observation index] := by
    intro index
    have hintegrable : Integrable (observation index) law :=
      Integrable.of_mem_Icc 0 1 (hmeasurable index).aemeasurable (hbounded index)
    simp only [complement]
    rw [integral_sub (integrable_const _) hintegrable]
    simp
  have hsum : ∀ outcome,
      (∑ index : Fin count, (complement index outcome - law[complement index])) =
        -(∑ index : Fin count, (observation index outcome - law[observation index])) := by
    intro outcome
    calc
      (∑ index : Fin count, (complement index outcome - law[complement index])) =
          ∑ index : Fin count, (-(observation index outcome - law[observation index])) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [hcomplementMean index]
        simp only [complement]
        ring
      _ = -(∑ index : Fin count, (observation index outcome - law[observation index])) := by
        rw [Finset.sum_neg_distrib]
  have hevent : {outcome |
      (∑ index : Fin count, (observation index outcome - law[observation index])) ≤
        -(count : ℝ) * error} =
      {outcome | (count : ℝ) * error ≤
        ∑ index : Fin count, (complement index outcome - law[complement index])} := by
    ext outcome
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact finiteIidBoundedObservation_centeredSum_upperTail law count complement
    hcomplementIndependent hcomplementMeasurable hcomplementBounded error herror

/-- The two-sided finite-batch Hoeffding bound. -/
theorem finiteIidBoundedObservation_centeredSum_abs_upperTail
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω) [IsProbabilityMeasure law]
    (count : ℕ) (observation : Fin count → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | (count : ℝ) * error ≤
      |∑ index : Fin count, (observation index outcome - law[observation index])|} ≤
      2 * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let upperEvent : Set Ω := {outcome | (count : ℝ) * error ≤
    ∑ index : Fin count, (observation index outcome - law[observation index])}
  let lowerEvent : Set Ω := {outcome |
    (∑ index : Fin count, (observation index outcome - law[observation index])) ≤
      -(count : ℝ) * error}
  have hupper : law.real upperEvent ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
    finiteIidBoundedObservation_centeredSum_upperTail law count observation
      hindependent hmeasurable hbounded error herror
  have hlower : law.real lowerEvent ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
    finiteIidBoundedObservation_centeredSum_lowerTail law count observation
      hindependent hmeasurable hbounded error herror
  let absoluteEvent : Set Ω := {outcome | (count : ℝ) * error ≤
    |∑ index : Fin count, (observation index outcome - law[observation index])|}
  have hsubset : absoluteEvent ⊆ upperEvent ∪ lowerEvent := by
    intro outcome habsolute
    change (count : ℝ) * error ≤
      |∑ index : Fin count, (observation index outcome - law[observation index])| at habsolute
    change ((count : ℝ) * error ≤
      ∑ index : Fin count, (observation index outcome - law[observation index])) ∨
      ((∑ index : Fin count, (observation index outcome - law[observation index])) ≤
        -(count : ℝ) * error)
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

end FalahatgarEtAl2017MaxingRanking
