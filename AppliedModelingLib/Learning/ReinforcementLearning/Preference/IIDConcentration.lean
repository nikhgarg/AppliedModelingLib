import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Probability.MDP

/-!
# IID concentration for bounded preference observations

This is the measurable probability layer used when a preference interface
repeats a binary comparison.  It records the one-sided Hoeffding bound directly
from Mathlib's independent sub-Gaussian-sum theorem.
-/

open scoped BigOperators ProbabilityTheory NNReal

namespace AppliedModelingLib

namespace PreferenceRL

open MeasureTheory ProbabilityTheory

/--
The centered sum over an arbitrary finite index set has the same bounded
independent-observation upper tail as the range-indexed form below.  Keeping
the index set explicit is useful for one ranking query: its disjoint-pair
labels are naturally indexed by `Fin capacity`, rather than by an artificially
extended sequence on `Nat`.
-/
theorem iIndepBoundedObservation_centeredSum_upperTail_finset
    {Ω Index : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Index → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (sample : Finset Index)
    (hmeasurable : ∀ index ∈ sample, Measurable (observation index))
    (hbounded : ∀ index ∈ sample, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | (sample.card : ℝ) * error ≤
      ∑ index ∈ sample,
        (observation index outcome - law[observation index])} ≤
      Real.exp (-((sample.card : ℝ) * error) ^ 2 /
        (2 * (sample.card : ℝ) * (1 / 4 : ℝ))) := by
  let centered : Index → Ω → ℝ :=
    fun index outcome => observation index outcome - law[observation index]
  have hcentered_independent : iIndepFun centered law := by
    simpa [centered, Function.comp_def] using
      hindependent.comp
        (fun index value => value - law[observation index])
        (fun _ => measurable_id.sub measurable_const)
  have hsubgaussian : ∀ index ∈ sample,
      HasSubgaussianMGF
        (centered index) ((2 : ℝ≥0) ^ 2)⁻¹ law := by
    intro index hindex
    simpa using
      (hasSubgaussianMGF_of_mem_Icc (hmeasurable index hindex).aemeasurable
        (hbounded index hindex) (a := (0 : ℝ)) (b := (1 : ℝ)))
  convert
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcentered_independent
      hsubgaussian (mul_nonneg (Nat.cast_nonneg sample.card) herror)) using 1
  norm_num [centered]
  ring

/-- The matching lower tail over an arbitrary finite family of observations. -/
theorem iIndepBoundedObservation_centeredSum_lowerTail_finset
    {Ω Index : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Index → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (sample : Finset Index)
    (hmeasurable : ∀ index ∈ sample, Measurable (observation index))
    (hbounded : ∀ index ∈ sample, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome |
      ∑ index ∈ sample,
        (observation index outcome - law[observation index]) ≤
          -(sample.card : ℝ) * error} ≤
      Real.exp (-((sample.card : ℝ) * error) ^ 2 /
        (2 * (sample.card : ℝ) * (1 / 4 : ℝ))) := by
  let complement : Index → Ω → ℝ :=
    fun index outcome => 1 - observation index outcome
  have hcomplement_independent : iIndepFun complement law := by
    simpa [complement, Function.comp_def] using
      hindependent.comp (fun _ value => 1 - value)
        (fun _ => measurable_const.sub measurable_id)
  have hcomplement_measurable : ∀ index ∈ sample, Measurable (complement index) := by
    intro index hindex
    exact measurable_const.sub (hmeasurable index hindex)
  have hcomplement_bounded : ∀ index ∈ sample, ∀ᵐ outcome ∂law,
      complement index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index hindex
    filter_upwards [hbounded index hindex] with outcome hvalue
    constructor <;> linarith [hvalue.1, hvalue.2]
  have hcomplement_mean : ∀ index ∈ sample,
      law[complement index] = 1 - law[observation index] := by
    intro index hindex
    have hintegrable : Integrable (observation index) law :=
      Integrable.of_mem_Icc 0 1 (hmeasurable index hindex).aemeasurable
        (hbounded index hindex)
    simp only [complement]
    rw [integral_sub (integrable_const _) hintegrable]
    simp
  have hsum : ∀ outcome,
      (∑ index ∈ sample,
        (complement index outcome - law[complement index])) =
        -(∑ index ∈ sample,
          (observation index outcome - law[observation index])) := by
    intro outcome
    calc
      (∑ index ∈ sample,
          (complement index outcome - law[complement index])) =
          ∑ index ∈ sample,
            -(observation index outcome - law[observation index]) := by
              apply Finset.sum_congr rfl
              intro index hindex
              rw [hcomplement_mean index hindex]
              simp only [complement]
              ring
      _ = -(∑ index ∈ sample,
          (observation index outcome - law[observation index])) := by
            rw [Finset.sum_neg_distrib]
  have hevent : {outcome |
      ∑ index ∈ sample,
        (observation index outcome - law[observation index]) ≤
          -(sample.card : ℝ) * error} =
      {outcome | (sample.card : ℝ) * error ≤
        ∑ index ∈ sample,
          (complement index outcome - law[complement index])} := by
    ext outcome
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact iIndepBoundedObservation_centeredSum_upperTail_finset law complement
    hcomplement_independent sample hcomplement_measurable hcomplement_bounded error herror

/-- The two-sided finite-index Hoeffding bound for observations in `[0,1]`. -/
theorem iIndepBoundedObservation_centeredSum_abs_upperTail_finset
    {Ω Index : Type*} [MeasurableSpace Ω] (law : Measure Ω)
    [IsProbabilityMeasure law] (observation : Index → Ω → ℝ)
    (hindependent : iIndepFun observation law)
    (sample : Finset Index)
    (hmeasurable : ∀ index ∈ sample, Measurable (observation index))
    (hbounded : ∀ index ∈ sample, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | (sample.card : ℝ) * error ≤
      |∑ index ∈ sample,
        (observation index outcome - law[observation index])|} ≤
      2 * Real.exp (-((sample.card : ℝ) * error) ^ 2 /
        (2 * (sample.card : ℝ) * (1 / 4 : ℝ))) := by
  let upperEvent : Set Ω := {outcome | (sample.card : ℝ) * error ≤
    ∑ index ∈ sample,
      (observation index outcome - law[observation index])}
  let lowerEvent : Set Ω := {outcome |
    ∑ index ∈ sample,
      (observation index outcome - law[observation index]) ≤
        -(sample.card : ℝ) * error}
  have hupper : law.real upperEvent ≤
      Real.exp (-((sample.card : ℝ) * error) ^ 2 /
        (2 * (sample.card : ℝ) * (1 / 4 : ℝ))) :=
    iIndepBoundedObservation_centeredSum_upperTail_finset law observation
      hindependent sample hmeasurable hbounded error herror
  have hlower : law.real lowerEvent ≤
      Real.exp (-((sample.card : ℝ) * error) ^ 2 /
        (2 * (sample.card : ℝ) * (1 / 4 : ℝ))) :=
    iIndepBoundedObservation_centeredSum_lowerTail_finset law observation
      hindependent sample hmeasurable hbounded error herror
  let absoluteEvent : Set Ω := {outcome | (sample.card : ℝ) * error ≤
    |∑ index ∈ sample,
      (observation index outcome - law[observation index])|}
  have hsubset : absoluteEvent ⊆ upperEvent ∪ lowerEvent := by
    intro outcome habsolute
    change (sample.card : ℝ) * error ≤
      |∑ index ∈ sample,
        (observation index outcome - law[observation index])| at habsolute
    change ((sample.card : ℝ) * error ≤
      ∑ index ∈ sample,
        (observation index outcome - law[observation index])) ∨
      ((∑ index ∈ sample,
        (observation index outcome - law[observation index])) ≤
          -(sample.card : ℝ) * error)
    rcases le_abs.mp habsolute with hupper | hnegated
    · exact Or.inl hupper
    · exact Or.inr (by linarith)
  calc
    law.real absoluteEvent ≤ law.real (upperEvent ∪ lowerEvent) :=
      measureReal_mono hsubset
    _ ≤ law.real upperEvent + law.real lowerEvent := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((sample.card : ℝ) * error) ^ 2 /
        (2 * (sample.card : ℝ) * (1 / 4 : ℝ))) := by
          nlinarith [hupper, hlower]

/--
The centered sum of independent observations taking values in `[0,1]` has the
one-sided Hoeffding upper tail.  This does not assume identical marginals; an
iid comparison experiment is its equal-mean specialization.
-/
theorem iidBoundedObservation_centeredSum_upperTail
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
      (hasSubgaussianMGF_of_mem_Icc (hmeasurable index).aemeasurable (hbounded index hindex)
        (a := (0 : ℝ)) (b := (1 : ℝ)))
  convert
    (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hcentered_independent hsubgaussian
      (mul_nonneg (Nat.cast_nonneg count) herror)) using 1
  norm_num [centered]

/-- The matching lower tail for the centered sum of bounded independent observations. -/
theorem iidBoundedObservation_centeredSum_lowerTail
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
  exact iidBoundedObservation_centeredSum_upperTail law complement count
    hcomplement_independent hcomplement_measurable hcomplement_bounded error herror

/-- The two-sided Hoeffding bound obtained by unioning the two centered tails. -/
theorem iidBoundedObservation_centeredSum_abs_upperTail
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
    iidBoundedObservation_centeredSum_upperTail law observation count
      hindependent hmeasurable hbounded error herror
  have hlower : law.real lowerEvent ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
    iidBoundedObservation_centeredSum_lowerTail law observation count
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
Finite sequential good-event composition.  No independence is required among
the indexed events: once each call's failure event has an unconditional
probability bound, the simultaneous event follows from the finite union
bound.  This is the probability-composition layer used after deriving a
per-call bound for an adaptive querying procedure.
-/
theorem finiteSequential_goodEvent_probability
    {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω) [IsProbabilityMeasure law]
    (queryCount : ℕ) (good : ℕ → Ω → Prop) (failureBudget : ℝ)
    (hmeasurable : ∀ queryIndex < queryCount,
      MeasurableSet {sample | good queryIndex sample})
    (hfailure : ∀ queryIndex < queryCount,
      law.real {sample | ¬ good queryIndex sample} ≤ failureBudget) :
    1 - (queryCount : ℝ) * failureBudget ≤
      law.real {sample | ∀ queryIndex < queryCount, good queryIndex sample} := by
  classical
  let badUnion : Set Ω := ⋃ queryIndex ∈ Finset.range queryCount,
    {sample | ¬ good queryIndex sample}
  let allGood : Set Ω := {sample | ∀ queryIndex < queryCount, good queryIndex sample}
  have hbadUnionMeasurable : MeasurableSet badUnion := by
    dsimp [badUnion]
    refine Finset.measurableSet_biUnion (s := Finset.range queryCount) ?_
    intro queryIndex hqueryIndex
    exact (hmeasurable queryIndex (Finset.mem_range.mp hqueryIndex)).compl
  have hgoodComplement : allGood = badUnionᶜ := by
    ext sample
    simp [allGood, badUnion]
  have hunion : law.real badUnion ≤
      ∑ queryIndex ∈ Finset.range queryCount,
        law.real {sample | ¬ good queryIndex sample} := by
    dsimp [badUnion]
    simpa using (measureReal_biUnion_finset_le (μ := law)
      (Finset.range queryCount) (fun queryIndex =>
        {sample | ¬ good queryIndex sample}))
  have hsum :
      (∑ queryIndex ∈ Finset.range queryCount,
        law.real {sample | ¬ good queryIndex sample}) ≤
        (queryCount : ℝ) * failureBudget := by
    calc
      (∑ queryIndex ∈ Finset.range queryCount,
        law.real {sample | ¬ good queryIndex sample}) ≤
          ∑ _queryIndex ∈ Finset.range queryCount, failureBudget := by
            apply Finset.sum_le_sum
            intro queryIndex hqueryIndex
            exact hfailure queryIndex (Finset.mem_range.mp hqueryIndex)
      _ = (queryCount : ℝ) * failureBudget := by
            simp [mul_comm]
  have hcomplement : law.real badUnionᶜ = 1 - law.real badUnion :=
    probReal_compl_eq_one_sub (μ := law) hbadUnionMeasurable
  calc
    1 - (queryCount : ℝ) * failureBudget ≤ 1 - law.real badUnion := by
      linarith [hunion, hsum]
    _ = law.real allGood := by
      rw [hgoodComplement]
      exact hcomplement.symm

/--
A history-dependent comparison experiment inherits a uniform conditional
failure bound after averaging over the history that selected the comparison.
The joint PMF retains the history coordinate, so the event may depend on the
adaptively selected trajectory and on that trajectory's fresh outcome.
-/
theorem pmfProb_adaptiveStep_le_of_historywiseBound
    {History Outcome : Type*} [Fintype History] [DecidableEq History]
    [Fintype Outcome] [DecidableEq Outcome]
    (historyLaw : PMF History) (outcomeLaw : History → PMF Outcome)
    (bad : History → Outcome → Prop) (failureBudget : ℝ)
    [∀ history outcome, Decidable (bad history outcome)]
    (hfailure : ∀ history,
      pmfProb (outcomeLaw history) (bad history) ≤ failureBudget) :
    pmfProb
        (historyLaw.bind fun history => (outcomeLaw history).map fun outcome =>
          (history, outcome))
        (fun historyOutcome => bad historyOutcome.1 historyOutcome.2) ≤ failureBudget := by
  classical
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  exact FiniteMDP.pmfExp_le_const historyLaw hfailure

/--
For a finite discrete outcome space, the PMF probability of an event agrees
with the real-valued measure of that event under the PMF's canonical measure.
This is the conversion used to feed finite comparison batches into the
measure-theoretic Hoeffding theorem.
-/
theorem pmfProb_eq_toMeasure_real
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (law : PMF Outcome) (event : Outcome → Prop) [DecidablePred event] :
    pmfProb law event = law.toMeasure.real {outcome | event outcome} := by
  classical
  unfold pmfProb pmfExp Measure.real
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro outcome _
    by_cases hevent : event outcome <;> simp [hevent]
  · intro outcome _
    by_cases hevent : event outcome <;>
      simp [Set.indicator, hevent, law.apply_ne_top outcome]

end PreferenceRL

end AppliedModelingLib
