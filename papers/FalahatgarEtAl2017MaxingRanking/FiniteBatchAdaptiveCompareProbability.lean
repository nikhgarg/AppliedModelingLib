import FalahatgarEtAl2017MaxingRanking.AdaptiveCompareProbability
import FalahatgarEtAl2017MaxingRanking.FiniteBatchConcentration

/-!
# Finite-batch adaptive comparison probability

The source's `Compare` call reads a finite fresh batch.  These lemmas transfer
finite-coordinate concentration to its natural-number prefix statistic without
postulating observations beyond the call's budget.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- A one-sided upper tail for a prefix of a finite fresh comparison batch. -/
theorem finiteBatchCenteredEstimate_upperTail_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap count : ℕ) (trueGap error : ℝ)
    (hcount : 0 < count) (hcountLeCap : count ≤ cap) (herror : 0 ≤ error)
    (hindependent : iIndepFun (fun index : Fin cap => observation index.val) law)
    (hmeasurable : ∀ index < cap, Measurable (observation index))
    (hbounded : ∀ index < cap, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < cap,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      adaptiveCenteredEstimate observation count outcome - trueGap < error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let prefixObservation : Fin count → Ω → ℝ := fun index => observation index.val
  have hprefixIndependent : iIndepFun prefixObservation law := by
    simpa [prefixObservation] using hindependent.precomp
      (Fin.castLEEmb hcountLeCap).injective
  have hprefixMeasurable : ∀ index, Measurable (prefixObservation index) := by
    intro index
    exact hmeasurable index.val (lt_of_lt_of_le index.isLt hcountLeCap)
  have hprefixBounded : ∀ index, ∀ᵐ outcome ∂law,
      prefixObservation index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    exact hbounded index.val (lt_of_lt_of_le index.isLt hcountLeCap)
  have htail := finiteIidBoundedObservation_centeredSum_upperTail law count
    prefixObservation hprefixIndependent hprefixMeasurable hprefixBounded error herror
  have htailFin : law.real {outcome | (count : ℝ) * error ≤
      ∑ index : Fin count,
        (observation index.val outcome - law[observation index.val])} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    simpa [prefixObservation] using htail
  have hsumFin : ∀ outcome,
      (∑ index : Fin count,
        (observation index.val outcome - law[observation index.val])) =
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index]) := by
    intro outcome
    exact Fin.sum_univ_eq_sum_range
      (fun index => observation index outcome - law[observation index]) count
  have heventFin :
      {outcome | (count : ℝ) * error ≤
        ∑ index : Fin count,
          (observation index.val outcome - law[observation index.val])} =
      {outcome | (count : ℝ) * error ≤
        ∑ index ∈ Finset.range count,
          (observation index outcome - law[observation index])} := by
    ext outcome
    simp only [Set.mem_setOf_eq]
    rw [hsumFin]
  have htailNat : law.real {outcome | (count : ℝ) * error ≤
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    rw [← heventFin]
    exact htailFin
  have hsum : ∀ outcome,
      (∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) =
        (∑ index ∈ Finset.range count, observation index outcome) -
          (count : ℝ) * (1 / 2 + trueGap) := by
    intro outcome
    rw [Finset.sum_sub_distrib]
    have hmeans :
        (∑ index ∈ Finset.range count, law[observation index]) =
          (count : ℝ) * (1 / 2 + trueGap) := by
      rw [show (∑ index ∈ Finset.range count, law[observation index]) =
          ∑ index ∈ Finset.range count, (1 / 2 + trueGap) by
        apply Finset.sum_congr rfl
        intro index hindex
        exact hmean index (lt_of_lt_of_le (Finset.mem_range.mp hindex) hcountLeCap)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hmeans]
  have hevent :
      {outcome | ¬
        adaptiveCenteredEstimate observation count outcome - trueGap < error} =
        {outcome | (count : ℝ) * error ≤
          ∑ index ∈ Finset.range count,
            (observation index outcome - law[observation index])} := by
    ext outcome
    simp only [Set.mem_setOf_eq, not_lt]
    rw [adaptiveCenteredEstimate, hsum]
    have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
    have hrewrite :
        ((∑ index ∈ Finset.range count, observation index outcome) / (count : ℝ) -
            1 / 2 - trueGap) =
          ((∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * (1 / 2 + trueGap)) / (count : ℝ) := by
      field_simp [ne_of_gt hcountReal]
      ring
    rw [hrewrite]
    constructor <;> intro h
    · have hdiv := (le_div_iff₀ hcountReal).mp h
      nlinarith
    · apply (le_div_iff₀ hcountReal).mpr
      nlinarith
  rw [hevent]
  exact htailNat

/-- A one-sided lower tail for a prefix of a finite fresh comparison batch. -/
theorem finiteBatchCenteredEstimate_lowerTail_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap count : ℕ) (trueGap error : ℝ)
    (hcount : 0 < count) (hcountLeCap : count ≤ cap) (herror : 0 ≤ error)
    (hindependent : iIndepFun (fun index : Fin cap => observation index.val) law)
    (hmeasurable : ∀ index < cap, Measurable (observation index))
    (hbounded : ∀ index < cap, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < cap,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      trueGap - adaptiveCenteredEstimate observation count outcome < error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  let prefixObservation : Fin count → Ω → ℝ := fun index => observation index.val
  have hprefixIndependent : iIndepFun prefixObservation law := by
    simpa [prefixObservation] using hindependent.precomp
      (Fin.castLEEmb hcountLeCap).injective
  have hprefixMeasurable : ∀ index, Measurable (prefixObservation index) := by
    intro index
    exact hmeasurable index.val (lt_of_lt_of_le index.isLt hcountLeCap)
  have hprefixBounded : ∀ index, ∀ᵐ outcome ∂law,
      prefixObservation index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    exact hbounded index.val (lt_of_lt_of_le index.isLt hcountLeCap)
  have htail := finiteIidBoundedObservation_centeredSum_lowerTail law count
    prefixObservation hprefixIndependent hprefixMeasurable hprefixBounded error herror
  have htailFin : law.real {outcome |
      (∑ index : Fin count,
        (observation index.val outcome - law[observation index.val])) ≤
          -(count : ℝ) * error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    simpa [prefixObservation] using htail
  have hsumFin : ∀ outcome,
      (∑ index : Fin count,
        (observation index.val outcome - law[observation index.val])) =
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index]) := by
    intro outcome
    exact Fin.sum_univ_eq_sum_range
      (fun index => observation index outcome - law[observation index]) count
  have heventFin :
      {outcome | (∑ index : Fin count,
        (observation index.val outcome - law[observation index.val])) ≤
          -(count : ℝ) * error} =
      {outcome | (∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) ≤
          -(count : ℝ) * error} := by
    ext outcome
    simp only [Set.mem_setOf_eq]
    rw [hsumFin]
  have htailNat : law.real {outcome |
      (∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) ≤
          -(count : ℝ) * error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    rw [← heventFin]
    exact htailFin
  have hsum : ∀ outcome,
      (∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) =
        (∑ index ∈ Finset.range count, observation index outcome) -
          (count : ℝ) * (1 / 2 + trueGap) := by
    intro outcome
    rw [Finset.sum_sub_distrib]
    have hmeans :
        (∑ index ∈ Finset.range count, law[observation index]) =
          (count : ℝ) * (1 / 2 + trueGap) := by
      rw [show (∑ index ∈ Finset.range count, law[observation index]) =
          ∑ index ∈ Finset.range count, (1 / 2 + trueGap) by
        apply Finset.sum_congr rfl
        intro index hindex
        exact hmean index (lt_of_lt_of_le (Finset.mem_range.mp hindex) hcountLeCap)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hmeans]
  have hevent :
      {outcome | ¬
        trueGap - adaptiveCenteredEstimate observation count outcome < error} =
        {outcome | ∑ index ∈ Finset.range count,
          (observation index outcome - law[observation index]) ≤
          -(count : ℝ) * error} := by
    ext outcome
    simp only [Set.mem_setOf_eq, not_lt]
    rw [adaptiveCenteredEstimate, hsum]
    have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
    have hrewrite :
        trueGap - ((∑ index ∈ Finset.range count, observation index outcome) /
          (count : ℝ) - 1 / 2) =
          -(((∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * (1 / 2 + trueGap)) / (count : ℝ)) := by
      field_simp [ne_of_gt hcountReal]
      ring
    rw [hrewrite]
    constructor <;> intro h
    · have hdiv :
          ((∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * (1 / 2 + trueGap)) / (count : ℝ) ≤ -error := by
        linarith
      have hmul := (div_le_iff₀ hcountReal).mp hdiv
      nlinarith
    · have hdiv :
          ((∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * (1 / 2 + trueGap)) / (count : ℝ) ≤ -error := by
        apply (div_le_iff₀ hcountReal).mpr
        nlinarith
      linarith
  rw [hevent]
  exact htailNat

/-- The finite-batch upper confidence sequence through every readable prefix. -/
theorem finiteBatchAdaptiveUniformUpperConfidence_failure_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap : ℕ) (trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin cap => observation index.val) law)
    (hmeasurable : ∀ index < cap, Measurable (observation index))
    (hbounded : ∀ index < cap, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < cap,
      law[observation index] = 1 / 2 + trueGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ∃ time ∈ Finset.Icc 1 cap, ¬
      adaptiveCenteredEstimate observation time outcome - trueGap <
        adaptiveConfidenceRadius time delta} ≤ delta / 2 := by
  apply adaptiveFiniteConfidence_union_failure_probability law cap
    (fun time outcome =>
      adaptiveCenteredEstimate observation time outcome - trueGap <
        adaptiveConfidenceRadius time delta) (delta / 2) (by linarith)
  intro time htime
  have htimePos : 0 < time := Nat.zero_lt_of_lt (Finset.mem_Icc.mp htime).1
  have htimeLeCap : time ≤ cap := (Finset.mem_Icc.mp htime).2
  calc
    law.real {outcome | ¬
        adaptiveCenteredEstimate observation time outcome - trueGap <
          adaptiveConfidenceRadius time delta} ≤
        Real.exp (-((time : ℝ) * adaptiveConfidenceRadius time delta) ^ 2 /
          (2 * (time : ℝ) * (1 / 4 : ℝ))) :=
      finiteBatchCenteredEstimate_upperTail_probability law observation cap time trueGap
        (adaptiveConfidenceRadius time delta) htimePos htimeLeCap (Real.sqrt_nonneg _)
        hindependent hmeasurable hbounded hmean
    _ = delta / (4 * (time : ℝ) ^ 2) :=
      adaptiveConfidenceRadius_oneSidedTail_eq time delta htimePos hdelta hdeltaLeOne
    _ = (delta / 2) / (2 * (time : ℝ) ^ 2) := by ring

/-- The symmetric finite-batch lower confidence sequence through all prefixes. -/
theorem finiteBatchAdaptiveUniformLowerConfidence_failure_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap : ℕ) (trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin cap => observation index.val) law)
    (hmeasurable : ∀ index < cap, Measurable (observation index))
    (hbounded : ∀ index < cap, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < cap,
      law[observation index] = 1 / 2 + trueGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ∃ time ∈ Finset.Icc 1 cap, ¬
      trueGap - adaptiveCenteredEstimate observation time outcome <
        adaptiveConfidenceRadius time delta} ≤ delta / 2 := by
  apply adaptiveFiniteConfidence_union_failure_probability law cap
    (fun time outcome =>
      trueGap - adaptiveCenteredEstimate observation time outcome <
        adaptiveConfidenceRadius time delta) (delta / 2) (by linarith)
  intro time htime
  have htimePos : 0 < time := Nat.zero_lt_of_lt (Finset.mem_Icc.mp htime).1
  have htimeLeCap : time ≤ cap := (Finset.mem_Icc.mp htime).2
  calc
    law.real {outcome | ¬
        trueGap - adaptiveCenteredEstimate observation time outcome <
          adaptiveConfidenceRadius time delta} ≤
        Real.exp (-((time : ℝ) * adaptiveConfidenceRadius time delta) ^ 2 /
          (2 * (time : ℝ) * (1 / 4 : ℝ))) :=
      finiteBatchCenteredEstimate_lowerTail_probability law observation cap time trueGap
        (adaptiveConfidenceRadius time delta) htimePos htimeLeCap (Real.sqrt_nonneg _)
        hindependent hmeasurable hbounded hmean
    _ = delta / (4 * (time : ℝ) ^ 2) :=
      adaptiveConfidenceRadius_oneSidedTail_eq time delta htimePos hdelta hdeltaLeOne
    _ = (delta / 2) / (2 * (time : ℝ) ^ 2) := by ring

/-- The finite-batch terminal upper error at the source's ceiling budget. -/
theorem finiteBatchAdaptiveTerminalUpperConfidence_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ¬
      adaptiveCenteredEstimate observation (fixedSampleBudget lower upper delta) outcome - trueGap <
        (upper - lower) / 2} ≤ delta / 2 := by
  have hcountReal := fixedSampleBudget_pos lower upper delta hseparation hdelta hdeltaLeOne
  have hcount : 0 < fixedSampleBudget lower upper delta := by exact_mod_cast hcountReal
  calc
    law.real {outcome | ¬
        adaptiveCenteredEstimate observation (fixedSampleBudget lower upper delta) outcome - trueGap <
          (upper - lower) / 2} ≤
        Real.exp (-((fixedSampleBudget lower upper delta : ℝ) *
          ((upper - lower) / 2)) ^ 2 /
          (2 * (fixedSampleBudget lower upper delta : ℝ) * (1 / 4 : ℝ))) :=
      finiteBatchCenteredEstimate_upperTail_probability law observation
        (fixedSampleBudget lower upper delta) (fixedSampleBudget lower upper delta) trueGap
        ((upper - lower) / 2) hcount le_rfl (by linarith [sub_pos.mpr hseparation])
        hindependent hmeasurable hbounded hmean
    _ ≤ delta / 2 := by
      have htail := fixedSampleCompare_tail_le_delta_of_ceilingBudget lower upper delta
        hseparation hdelta hdeltaLeOne
      nlinarith

/-- The finite-batch terminal lower error at the source's ceiling budget. -/
theorem finiteBatchAdaptiveTerminalLowerConfidence_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ¬
      trueGap - adaptiveCenteredEstimate observation (fixedSampleBudget lower upper delta) outcome <
        (upper - lower) / 2} ≤ delta / 2 := by
  have hcountReal := fixedSampleBudget_pos lower upper delta hseparation hdelta hdeltaLeOne
  have hcount : 0 < fixedSampleBudget lower upper delta := by exact_mod_cast hcountReal
  calc
    law.real {outcome | ¬
        trueGap - adaptiveCenteredEstimate observation (fixedSampleBudget lower upper delta) outcome <
          (upper - lower) / 2} ≤
        Real.exp (-((fixedSampleBudget lower upper delta : ℝ) *
          ((upper - lower) / 2)) ^ 2 /
          (2 * (fixedSampleBudget lower upper delta : ℝ) * (1 / 4 : ℝ))) :=
      finiteBatchCenteredEstimate_lowerTail_probability law observation
        (fixedSampleBudget lower upper delta) (fixedSampleBudget lower upper delta) trueGap
        ((upper - lower) / 2) hcount le_rfl (by linarith [sub_pos.mpr hseparation])
        hindependent hmeasurable hbounded hmean
    _ ≤ delta / 2 := by
      have htail := fixedSampleCompare_tail_le_delta_of_ceilingBudget lower upper delta
        hseparation hdelta hdeltaLeOne
      nlinarith

/-- Lemma 11's lower Compare conclusion for one finite fresh batch. -/
theorem finiteBatchAdaptiveCompare_lower_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : trueGap ≤ lower) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
      lower upper delta outcome ≠ .lower} ≤ delta := by
  let earlyBad : Set Ω := {outcome | ∃ time ∈
      Finset.Icc 1 (fixedSampleBudget lower upper delta), ¬
      adaptiveCenteredEstimate observation time outcome - trueGap <
        adaptiveConfidenceRadius time delta}
  let terminalBad : Set Ω := {outcome | ¬
      adaptiveCenteredEstimate observation (fixedSampleBudget lower upper delta) outcome - trueGap <
        (upper - lower) / 2}
  have hearly := finiteBatchAdaptiveUniformUpperConfidence_failure_probability law observation
    (fixedSampleBudget lower upper delta) trueGap delta hindependent hmeasurable hbounded hmean
    hdelta hdeltaLeOne
  have hterminal := finiteBatchAdaptiveTerminalUpperConfidence_failure_probability_of_ceilingBudget
    law observation lower upper trueGap delta hindependent hmeasurable hbounded hmean
    hseparation hdelta hdeltaLeOne
  have hsubset :
      {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≠ .lower} ⊆ earlyBad ∪ terminalBad := by
    intro outcome hfailure
    by_contra hnotUnion
    have hneither : outcome ∉ earlyBad ∧ outcome ∉ terminalBad :=
      not_or.mp (by simpa only [Set.mem_union] using hnotUnion)
    apply hfailure
    apply adaptiveCompare_lower_of_upperConfidence observation
      (fixedSampleBudget lower upper delta) lower upper trueGap delta outcome hgap hseparation
    · intro time htime
      by_contra hbad
      apply hneither.1
      exact ⟨time, htime, hbad⟩
    · by_contra hbad
      apply hneither.2
      exact hbad
  calc
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≠ .lower} ≤ law.real (earlyBad ∪ terminalBad) :=
      measureReal_mono hsubset
    _ ≤ law.real earlyBad + law.real terminalBad := measureReal_union_le _ _
    _ ≤ delta := by
      dsimp [earlyBad, terminalBad]
      linarith

/-- Lemma 12's upper Compare conclusion for one finite fresh batch. -/
theorem finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
      lower upper delta outcome ≠ .upper} ≤ delta := by
  let earlyBad : Set Ω := {outcome | ∃ time ∈
      Finset.Icc 1 (fixedSampleBudget lower upper delta), ¬
      trueGap - adaptiveCenteredEstimate observation time outcome <
        adaptiveConfidenceRadius time delta}
  let terminalBad : Set Ω := {outcome | ¬
      trueGap - adaptiveCenteredEstimate observation (fixedSampleBudget lower upper delta) outcome <
        (upper - lower) / 2}
  have hearly := finiteBatchAdaptiveUniformLowerConfidence_failure_probability law observation
    (fixedSampleBudget lower upper delta) trueGap delta hindependent hmeasurable hbounded hmean
    hdelta hdeltaLeOne
  have hterminal := finiteBatchAdaptiveTerminalLowerConfidence_failure_probability_of_ceilingBudget
    law observation lower upper trueGap delta hindependent hmeasurable hbounded hmean
    hseparation hdelta hdeltaLeOne
  have hsubset :
      {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≠ .upper} ⊆ earlyBad ∪ terminalBad := by
    intro outcome hfailure
    by_contra hnotUnion
    have hneither : outcome ∉ earlyBad ∧ outcome ∉ terminalBad :=
      not_or.mp (by simpa only [Set.mem_union] using hnotUnion)
    apply hfailure
    apply adaptiveCompare_upper_of_lowerConfidence observation
      (fixedSampleBudget lower upper delta) lower upper trueGap delta outcome hgap hseparation
    · intro time htime
      by_contra hbad
      apply hneither.1
      exact ⟨time, htime, hbad⟩
    · by_contra hbad
      apply hneither.2
      exact hbad
  calc
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≠ .upper} ≤ law.real (earlyBad ∪ terminalBad) :=
      measureReal_mono hsubset
    _ ≤ law.real earlyBad + law.real terminalBad := measureReal_union_le _ _
    _ ≤ delta := by
      dsimp [earlyBad, terminalBad]
      linarith

/-- A finite fresh Compare batch has the source Lemma 11/12 call failure bound. -/
theorem finiteBatchAdaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
    {Arm Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (law : PMF Outcome) (observation : Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (incumbent challenger : Arm)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget 0 epsilon eta) =>
      observation challenger incumbent index.val) law.toMeasure)
    (hmeasurable : ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
      ∀ᵐ outcome ∂law.toMeasure,
        observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
      law.toMeasure[observation challenger incumbent sampleIndex] =
        1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    pmfProbClassical law (fun outcome =>
      ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
        preferenceGap epsilon eta outcome incumbent challenger) ≤ eta := by
  classical
  by_cases hsmall : preferenceGap challenger incumbent ≤ 0
  · calc
      pmfProbClassical law (fun outcome =>
          ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
            preferenceGap epsilon eta outcome incumbent challenger) ≤
          pmfProbClassical law (fun outcome => adaptiveCompare
            (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
            0 epsilon eta outcome ≠ .lower) := by
              apply pmfProbClassical_le_of_imp
              intro outcome hinvalid
              by_contra hdecision
              have hdecision' : adaptiveCompare (observation challenger incumbent)
                  (fixedSampleBudget 0 epsilon eta) 0 epsilon eta outcome = .lower := hdecision
              apply hinvalid
              unfold AdaptiveCompareStepCallValid
              simp only [adaptiveCompareStep, hdecision']
              constructor
              · rw [hself]
              · rw [hantisymmetric challenger incumbent]
                linarith
      _ = law.toMeasure.real {outcome | adaptiveCompare
          (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
          0 epsilon eta outcome ≠ .lower} := by
        rw [pmfProbClassical_eq_pmfProb]
        exact AppliedModelingLib.pmfProb_eq_toMeasure_real law _
      _ ≤ eta := by
        apply finiteBatchAdaptiveCompare_lower_failure_probability_of_ceilingBudget law.toMeasure
          (observation challenger incumbent) 0 epsilon
          (preferenceGap challenger incumbent) eta
        · exact hindependent
        · exact hmeasurable
        · exact hbounded
        · exact hmean
        · exact hsmall
        · exact hepsilon
        · exact heta
        · exact hetaLeOne
  · have hpositive : 0 ≤ preferenceGap challenger incumbent :=
      le_of_lt (lt_of_not_ge hsmall)
    by_cases hlarge : epsilon ≤ preferenceGap challenger incumbent
    · calc
        pmfProbClassical law (fun outcome =>
            ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
              preferenceGap epsilon eta outcome incumbent challenger) ≤
            pmfProbClassical law (fun outcome => adaptiveCompare
              (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
              0 epsilon eta outcome ≠ .upper) := by
                apply pmfProbClassical_le_of_imp
                intro outcome hinvalid
                by_contra hdecision
                have hdecision' : adaptiveCompare (observation challenger incumbent)
                    (fixedSampleBudget 0 epsilon eta) 0 epsilon eta outcome = .upper := hdecision
                apply hinvalid
                unfold AdaptiveCompareStepCallValid
                simp only [adaptiveCompareStep, hdecision']
                constructor
                · exact hpositive
                · rw [hself]
                  linarith
        _ = law.toMeasure.real {outcome | adaptiveCompare
            (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
            0 epsilon eta outcome ≠ .upper} := by
          rw [pmfProbClassical_eq_pmfProb]
          exact AppliedModelingLib.pmfProb_eq_toMeasure_real law _
        _ ≤ eta := by
          apply finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget law.toMeasure
            (observation challenger incumbent) 0 epsilon
            (preferenceGap challenger incumbent) eta
          · exact hindependent
          · exact hmeasurable
          · exact hbounded
          · exact hmean
          · exact hlarge
          · exact hepsilon
          · exact heta
          · exact hetaLeOne
    · have hmiddle : preferenceGap challenger incumbent ≤ epsilon := le_of_not_ge hlarge
      have hallValid : ∀ outcome,
          AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
            preferenceGap epsilon eta outcome incumbent challenger := by
        intro outcome
        exact adaptiveCompareStepCallValid_of_middleGap observation
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome
          hantisymmetric hself incumbent challenger hpositive hmiddle
      have hzero : pmfProbClassical law (fun outcome =>
          ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
            preferenceGap epsilon eta outcome incumbent challenger) = 0 := by
        rw [pmfProbClassical_eq_pmfProb]
        apply pmfProb_eq_zero_of_no_mass
        intro outcome hinvalid
        exact (hinvalid (hallValid outcome)).elim
      rw [hzero]
      exact le_of_lt heta

/-- The paper's Bernoulli comparison batch satisfies the finite fresh-call bound. -/
theorem canonicalComparisonBatch_adaptiveCompareStepCallInvalid_probability_of_ceilingBudget
    {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ) (incumbent challenger : Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    pmfProbClassical
      (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent
        (fixedSampleBudget 0 epsilon eta))
      (fun outcome => ¬ AdaptiveCompareStepCallValid
        (fun _ _ sampleIndex batch =>
          canonicalComparisonBatchObservation (fixedSampleBudget 0 epsilon eta)
            sampleIndex batch)
        (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome incumbent challenger) ≤ eta := by
  apply finiteBatchAdaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
    (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent
      (fixedSampleBudget 0 epsilon eta))
    (fun _ _ sampleIndex batch =>
      canonicalComparisonBatchObservation (fixedSampleBudget 0 epsilon eta) sampleIndex batch)
    preferenceGap epsilon eta incumbent challenger
  · simpa using iIndepFun_canonicalComparisonBatchObservation preferenceGap hprobability
      challenger incumbent (fixedSampleBudget 0 epsilon eta)
  · intro sampleIndex hsampleIndex
    exact measurable_canonicalComparisonBatchObservation
      (fixedSampleBudget 0 epsilon eta) sampleIndex
  · intro sampleIndex hsampleIndex
    exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
      challenger incumbent (fixedSampleBudget 0 epsilon eta) sampleIndex
  · intro sampleIndex hsampleIndex
    exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
      challenger incumbent (fixedSampleBudget 0 epsilon eta) sampleIndex hsampleIndex
  · exact hantisymmetric
  · exact hself
  · exact hepsilon
  · exact heta
  · exact hetaLeOne

end FalahatgarEtAl2017MaxingRanking
