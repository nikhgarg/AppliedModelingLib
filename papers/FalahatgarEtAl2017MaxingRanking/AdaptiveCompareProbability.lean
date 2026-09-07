import FalahatgarEtAl2017MaxingRanking.AdaptiveCompare
import FalahatgarEtAl2017MaxingRanking.SampleBudget
import Mathlib.Analysis.PSeries

/-!
# Adaptive Compare: one-time confidence probability

This is the iid bridge for one fixed time in the Appendix A.1 confidence
sequence.  It converts the shared bounded-observation Hoeffding theorem into
the centered empirical estimate used by `adaptiveCompare`.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
At a fixed positive time, failure of the adaptive confidence interval has the
shared iid Hoeffding bound.  The remaining Appendix A.2 task is to specialize
the displayed radius and compose these events over all stopping times.
-/
theorem adaptiveCenteredEstimate_nonconcentration_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (trueGap delta : ℝ)
    (hcount : 0 < count)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      |adaptiveCenteredEstimate observation count outcome - trueGap| <
        adaptiveConfidenceRadius count delta} ≤
      2 * Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := iidBoundedObservation_centeredSum_abs_upperTail law observation count
    hindependent hmeasurable hbounded (adaptiveConfidenceRadius count delta)
    (Real.sqrt_nonneg _)
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
        exact hmean index (Finset.mem_range.mp hindex)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hmeans]
  have hevent :
      {outcome | ¬
        |adaptiveCenteredEstimate observation count outcome - trueGap| <
          adaptiveConfidenceRadius count delta} =
        {outcome | (count : ℝ) * adaptiveConfidenceRadius count delta ≤
          |∑ index ∈ Finset.range count,
            (observation index outcome - law[observation index])|} := by
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
    rw [hrewrite, abs_div, abs_of_pos hcountReal]
    constructor <;> intro h
    · have hdiv := (le_div_iff₀ hcountReal).mp h
      nlinarith
    · apply (le_div_iff₀ hcountReal).mpr
      nlinarith
  rw [hevent]
  exact htail

/--
At a fixed positive time, the upper-sided confidence failure has the one-sided
Hoeffding bound.  This is the error direction used under the lower hypothesis
in Appendix A.2.
-/
theorem adaptiveCenteredEstimate_upper_nonconcentration_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (trueGap delta : ℝ)
    (hcount : 0 < count)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      adaptiveCenteredEstimate observation count outcome - trueGap <
        adaptiveConfidenceRadius count delta} ≤
      Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := iidBoundedObservation_centeredSum_upperTail law observation count
    hindependent hmeasurable hbounded (adaptiveConfidenceRadius count delta)
    (Real.sqrt_nonneg _)
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
        exact hmean index (Finset.mem_range.mp hindex)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hmeans]
  have hevent :
      {outcome | ¬
        adaptiveCenteredEstimate observation count outcome - trueGap <
          adaptiveConfidenceRadius count delta} =
        {outcome | (count : ℝ) * adaptiveConfidenceRadius count delta ≤
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
  exact htail

/--
At a fixed positive time, the lower-sided confidence failure has the one-sided
Hoeffding bound.  This is the symmetric Appendix A.2 error direction.
-/
theorem adaptiveCenteredEstimate_lower_nonconcentration_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (trueGap delta : ℝ)
    (hcount : 0 < count)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      trueGap - adaptiveCenteredEstimate observation count outcome <
        adaptiveConfidenceRadius count delta} ≤
      Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := iidBoundedObservation_centeredSum_lowerTail law observation count
    hindependent hmeasurable hbounded (adaptiveConfidenceRadius count delta)
    (Real.sqrt_nonneg _)
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
        exact hmean index (Finset.mem_range.mp hindex)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hmeans]
  have hevent :
      {outcome | ¬
        trueGap - adaptiveCenteredEstimate observation count outcome <
          adaptiveConfidenceRadius count delta} =
        {outcome | ∑ index ∈ Finset.range count,
          (observation index outcome - law[observation index]) ≤
          -(count : ℝ) * adaptiveConfidenceRadius count delta} := by
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
            (count : ℝ) * (1 / 2 + trueGap)) / (count : ℝ) ≤
            -adaptiveConfidenceRadius count delta := by
        linarith
      have hmul := (div_le_iff₀ hcountReal).mp hdiv
      nlinarith
    · have hdiv :
          ((∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * (1 / 2 + trueGap)) / (count : ℝ) ≤
            -adaptiveConfidenceRadius count delta := by
        apply (div_le_iff₀ hcountReal).mpr
        nlinarith
      linarith
  rw [hevent]
  exact htail

/-- A reusable one-sided upper tail for a centered empirical comparison mean. -/
theorem centeredEstimate_upperTail_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (trueGap error : ℝ)
    (hcount : 0 < count) (herror : 0 ≤ error)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      adaptiveCenteredEstimate observation count outcome - trueGap < error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := iidBoundedObservation_centeredSum_upperTail law observation count
    hindependent hmeasurable hbounded error herror
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
        exact hmean index (Finset.mem_range.mp hindex)]
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
  exact htail

/-- A reusable one-sided lower tail for a centered empirical comparison mean. -/
theorem centeredEstimate_lowerTail_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (trueGap error : ℝ)
    (hcount : 0 < count) (herror : 0 ≤ error)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count,
      law[observation index] = 1 / 2 + trueGap) :
    law.real {outcome | ¬
      trueGap - adaptiveCenteredEstimate observation count outcome < error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := iidBoundedObservation_centeredSum_lowerTail law observation count
    hindependent hmeasurable hbounded error herror
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
        exact hmean index (Finset.mem_range.mp hindex)]
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
  exact htail

/--
The Appendix A.1 confidence radius makes the two-sided fixed-time Hoeffding
bound exactly `δ / (2 t²)`.  This is the algebraic summand used in the
supplement's confidence-sequence union bound.
-/
theorem adaptiveConfidenceRadius_tail_eq
    (count : ℕ) (delta : ℝ)
    (hcount : 0 < count) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    2 * Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) =
        delta / (2 * (count : ℝ) ^ 2) := by
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcountSq : 1 ≤ (count : ℝ) ^ 2 := by
    nlinarith [show (1 : ℝ) ≤ count by exact_mod_cast hcount]
  have hratio : 1 ≤ 4 * (count : ℝ) ^ 2 / delta := by
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hratioPos : 0 < 4 * (count : ℝ) ^ 2 / delta :=
    lt_of_lt_of_le zero_lt_one hratio
  have hinsidenonneg :
      0 ≤ Real.log (4 * (count : ℝ) ^ 2 / delta) / (2 * (count : ℝ)) := by
    exact div_nonneg (Real.log_nonneg hratio) (by positivity)
  have hradiusSq : adaptiveConfidenceRadius count delta ^ 2 =
      Real.log (4 * (count : ℝ) ^ 2 / delta) / (2 * (count : ℝ)) := by
    unfold adaptiveConfidenceRadius
    exact Real.sq_sqrt hinsidenonneg
  have htailExponent :
      -((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)) =
          -Real.log (4 * (count : ℝ) ^ 2 / delta) := by
    rw [show ((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 =
        (count : ℝ) ^ 2 * adaptiveConfidenceRadius count delta ^ 2 by ring,
      hradiusSq]
    field_simp [ne_of_gt hcountReal]
    ring
  have hlogExp : Real.exp (-Real.log (4 * (count : ℝ) ^ 2 / delta)) =
      delta / (4 * (count : ℝ) ^ 2) := by
    rw [Real.exp_neg, Real.exp_log hratioPos]
    field_simp [ne_of_gt hdelta, ne_of_gt hcountReal]
  calc
    2 * Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) =
        2 * Real.exp (-Real.log (4 * (count : ℝ) ^ 2 / delta)) := by
          rw [htailExponent]
    _ = delta / (2 * (count : ℝ) ^ 2) := by rw [hlogExp]; field_simp; ring

/--
The same Appendix A.1 radius gives the one-sided fixed-time summand
`δ / (4t²)`.  Appendix A.2 assigns these summands to the relevant direction
only, leaving `δ / 2` after the prefix union.
-/
theorem adaptiveConfidenceRadius_oneSidedTail_eq
    (count : ℕ) (delta : ℝ)
    (hcount : 0 < count) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) =
        delta / (4 * (count : ℝ) ^ 2) := by
  have htwoSided := adaptiveConfidenceRadius_tail_eq count delta hcount hdelta hdeltaLeOne
  calc
    Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) =
        (2 * Real.exp (-((count : ℝ) * adaptiveConfidenceRadius count delta) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) / 2 := by ring
    _ = (delta / (2 * (count : ℝ) ^ 2)) / 2 := by rw [htwoSided]
    _ = delta / (4 * (count : ℝ) ^ 2) := by ring

/--
The finite confidence-sequence union calculation in Appendix A.2.  If each
positive time `t ≤ count` has failure mass at most `δ/(2t²)`, then some such
failure has mass at most `δ`.  No independence between the time events is
needed for this composition.
-/
theorem adaptiveFiniteConfidence_union_failure_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) (count : ℕ) (good : ℕ → Ω → Prop) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hfailure : ∀ time ∈ Finset.Icc 1 count,
      law.real {outcome | ¬ good time outcome} ≤ delta / (2 * (time : ℝ) ^ 2)) :
    law.real {outcome | ∃ time ∈ Finset.Icc 1 count, ¬ good time outcome} ≤ delta := by
  classical
  let index : Finset ℕ := Finset.Icc 1 count
  let bad : ℕ → Set Ω := fun time => {outcome | ¬ good time outcome}
  have hunion : law.real (⋃ time ∈ index, bad time) ≤
      ∑ time ∈ index, law.real (bad time) := by
    simpa only [index, bad] using
      (measureReal_biUnion_finset_le (μ := law)
        (Finset.Icc 1 count) (fun time => {outcome | ¬ good time outcome}))
  have hsum : (∑ time ∈ index, law.real (bad time)) ≤ delta := by
    have hterms : ∀ time ∈ index,
        law.real (bad time) ≤ delta / (2 * (time : ℝ) ^ 2) := by
      intro time htime
      exact hfailure time (by simpa [index] using htime)
    calc
      (∑ time ∈ index, law.real (bad time)) ≤
          ∑ time ∈ index, delta / (2 * (time : ℝ) ^ 2) := by
            exact Finset.sum_le_sum fun time htime => hterms time htime
      _ = (delta / 2) * ∑ time ∈ index, ((time : ℝ) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro time htime
            have htimePos : 0 < (time : ℝ) := by
              exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Icc.mp htime).1)
            field_simp [ne_of_gt htimePos]
      _ ≤ (delta / 2) * 2 := by
            apply mul_le_mul_of_nonneg_left
            · have hindex : index = Finset.Ioo 0 (count + 1) := by
                ext time
                simp only [index, Finset.mem_Icc, Finset.mem_Ioo]
                omega
              rw [hindex]
              simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (count + 1))
            · linarith
      _ = delta := by ring
  calc
    law.real {outcome | ∃ time ∈ Finset.Icc 1 count, ¬ good time outcome} =
        law.real (⋃ time ∈ index, bad time) := by
          congr 1
          ext outcome
          simp [index, bad]
    _ ≤ ∑ time ∈ index, law.real (bad time) := hunion
    _ ≤ delta := hsum

/--
The full uniform iid confidence event for all positive prefixes up to a finite
cap.  This instantiates Appendix A.2's p-series union calculation with the
fixed-time bounded-observation theorem.
-/
theorem adaptiveUniformConfidence_failure_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap : ℕ) (trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < cap, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < cap,
      law[observation index] = 1 / 2 + trueGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ∃ time ∈ Finset.Icc 1 cap, ¬
      |adaptiveCenteredEstimate observation time outcome - trueGap| <
        adaptiveConfidenceRadius time delta} ≤ delta := by
  apply adaptiveFiniteConfidence_union_failure_probability law cap
    (fun time outcome =>
      |adaptiveCenteredEstimate observation time outcome - trueGap| <
        adaptiveConfidenceRadius time delta) delta (le_of_lt hdelta)
  intro time htime
  have htimePos : 0 < time := Nat.zero_lt_of_lt (Finset.mem_Icc.mp htime).1
  have htimeLeCap : time ≤ cap := (Finset.mem_Icc.mp htime).2
  calc
    law.real {outcome | ¬
        |adaptiveCenteredEstimate observation time outcome - trueGap| <
          adaptiveConfidenceRadius time delta} ≤
        2 * Real.exp (-((time : ℝ) * adaptiveConfidenceRadius time delta) ^ 2 /
          (2 * (time : ℝ) * (1 / 4 : ℝ))) :=
      adaptiveCenteredEstimate_nonconcentration_probability law observation time trueGap delta
        htimePos hindependent hmeasurable
        (fun index hindex => hbounded index (lt_of_lt_of_le hindex htimeLeCap))
        (fun index hindex => hmean index (lt_of_lt_of_le hindex htimeLeCap))
    _ = delta / (2 * (time : ℝ) ^ 2) :=
      adaptiveConfidenceRadius_tail_eq time delta htimePos hdelta hdeltaLeOne

/--
Appendix A.2's one-sided upper-prefix confidence calculation.  The p-series
union has probability at most `δ / 2`, exactly the allocation used under the
lower Compare hypothesis.
-/
theorem adaptiveUniformUpperConfidence_failure_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap : ℕ) (trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
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
      adaptiveCenteredEstimate_upper_nonconcentration_probability law observation time trueGap delta
        htimePos hindependent hmeasurable
        (fun index hindex => hbounded index (lt_of_lt_of_le hindex htimeLeCap))
        (fun index hindex => hmean index (lt_of_lt_of_le hindex htimeLeCap))
    _ = delta / (4 * (time : ℝ) ^ 2) :=
      adaptiveConfidenceRadius_oneSidedTail_eq time delta htimePos hdelta hdeltaLeOne
    _ = (delta / 2) / (2 * (time : ℝ) ^ 2) := by ring

/--
The symmetric one-sided lower-prefix confidence calculation in Appendix A.2.
-/
theorem adaptiveUniformLowerConfidence_failure_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (cap : ℕ) (trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
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
      adaptiveCenteredEstimate_lower_nonconcentration_probability law observation time trueGap delta
        htimePos hindependent hmeasurable
        (fun index hindex => hbounded index (lt_of_lt_of_le hindex htimeLeCap))
        (fun index hindex => hmean index (lt_of_lt_of_le hindex htimeLeCap))
    _ = delta / (4 * (time : ℝ) ^ 2) :=
      adaptiveConfidenceRadius_oneSidedTail_eq time delta htimePos hdelta hdeltaLeOne
    _ = (delta / 2) / (2 * (time : ℝ) ^ 2) := by ring

/--
At the source's ceiling cap, the upper-sided terminal confidence error has
probability at most `δ / 2`.
-/
theorem adaptiveTerminalUpperConfidence_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
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
      centeredEstimate_upperTail_probability law observation
        (fixedSampleBudget lower upper delta) trueGap ((upper - lower) / 2)
        hcount (by linarith [sub_pos.mpr hseparation]) hindependent hmeasurable hbounded hmean
    _ ≤ delta / 2 := by
      have htail := fixedSampleCompare_tail_le_delta_of_ceilingBudget lower upper delta
        hseparation hdelta hdeltaLeOne
      nlinarith

/--
At the source's ceiling cap, the lower-sided terminal confidence error has
probability at most `δ / 2`.
-/
theorem adaptiveTerminalLowerConfidence_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
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
      centeredEstimate_lowerTail_probability law observation
        (fixedSampleBudget lower upper delta) trueGap ((upper - lower) / 2)
        hcount (by linarith [sub_pos.mpr hseparation]) hindependent hmeasurable hbounded hmean
    _ ≤ delta / 2 := by
      have htail := fixedSampleCompare_tail_le_delta_of_ceilingBudget lower upper delta
        hseparation hdelta hdeltaLeOne
      nlinarith

/--
Lemma 11's adaptive Compare guarantee under the lower hypothesis, with the
source's ceiling cap.  The prefix and terminal one-sided failures each receive
`δ / 2` and are composed by a two-event union bound.
-/
theorem adaptiveCompare_lower_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
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
  have hearly := adaptiveUniformUpperConfidence_failure_probability law observation
    (fixedSampleBudget lower upper delta) trueGap delta hindependent hmeasurable hbounded hmean
    hdelta hdeltaLeOne
  have hterminal := adaptiveTerminalUpperConfidence_failure_probability_of_ceilingBudget
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

/--
Lemma 12's symmetric adaptive Compare guarantee under the upper hypothesis.
-/
theorem adaptiveCompare_upper_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
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
  have hearly := adaptiveUniformLowerConfidence_failure_probability law observation
    (fixedSampleBudget lower upper delta) trueGap delta hindependent hmeasurable hbounded hmean
    hdelta hdeltaLeOne
  have hterminal := adaptiveTerminalLowerConfidence_failure_probability_of_ceilingBudget
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

end FalahatgarEtAl2017MaxingRanking
