import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare

/-!
# Finite fixed-sample Compare budget

The source writes a real-valued comparison budget.  Lean keeps the executable
natural count and its ceiling explicit, then proves the exact tail inequality
for every positive count meeting the displayed real lower bound.
-/

namespace FalahatgarEtAl2017MaxingRanking

open MeasureTheory ProbabilityTheory

/-- The natural-number ceiling of Section 3.1.1's fixed-sample budget. -/
noncomputable def fixedSampleBudget (lower upper delta : ℝ) : ℕ :=
  ⌈2 / (upper - lower) ^ 2 * Real.log (2 / delta)⌉₊

/--
The fixed mean-estimation budget printed in Algorithms 6 and 8.  The PDF
coefficient is `1 / (2 * ε²)`, so this is the Compare ceiling with separation
`2 * ε`, not with separation `ε`.
-/
noncomputable def meanEstimateSampleBudget (epsilon delta : ℝ) : ℕ :=
  fixedSampleBudget 0 (2 * epsilon) delta

/-- Algorithm 6's paper-facing fixed pairwise-estimation count. -/
noncomputable def estimateProbabilitySampleBudget (epsilon delta : ℝ) : ℕ :=
  meanEstimateSampleBudget epsilon delta

/-- Algorithm 8's paper-facing fixed Borda-estimation count. -/
noncomputable def estimateBordaScoreSampleBudget (epsilon delta : ℝ) : ℕ :=
  meanEstimateSampleBudget epsilon delta

/-- The ceiling budget dominates the real-valued expression printed in the source. -/
theorem fixedSampleBudget_realTarget_le (lower upper delta : ℝ) :
    2 / (upper - lower) ^ 2 * Real.log (2 / delta) ≤
      (fixedSampleBudget lower upper delta : ℝ) :=
  Nat.le_ceil _

/-- The executable ceiling differs from the source's real Compare budget by less than one. -/
theorem fixedSampleBudget_lt_realTarget_add_one
    (lower upper delta : ℝ) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (fixedSampleBudget lower upper delta : ℝ) <
      2 / (upper - lower) ^ 2 * Real.log (2 / delta) + 1 := by
  unfold fixedSampleBudget
  apply Nat.ceil_lt_add_one
  apply mul_nonneg
  · exact div_nonneg (by norm_num) (sq_nonneg _)
  · apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    nlinarith

/-- The Algorithm-6/8 ceiling dominates the coefficient printed in the PDF. -/
theorem meanEstimateSampleBudget_realTarget_le
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon) :
    1 / (2 * epsilon ^ 2) * Real.log (2 / delta) ≤
      (meanEstimateSampleBudget epsilon delta : ℝ) := by
  have h := fixedSampleBudget_realTarget_le 0 (2 * epsilon) delta
  rw [meanEstimateSampleBudget]
  convert h using 1
  (field_simp [ne_of_gt hepsilon] ; ring)

/-- The executable Algorithm-6/8 count is less than the PDF target plus one. -/
theorem meanEstimateSampleBudget_lt_realTarget_add_one
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (meanEstimateSampleBudget epsilon delta : ℝ) <
      1 / (2 * epsilon ^ 2) * Real.log (2 / delta) + 1 := by
  have h := fixedSampleBudget_lt_realTarget_add_one
    0 (2 * epsilon) delta hdelta hdeltaLeOne
  rw [meanEstimateSampleBudget]
  convert h using 1
  (field_simp [ne_of_gt hepsilon] ; ring)

/-- A finite sequence of source Compare calls is bounded by its ceiling-corrected real budget. -/
theorem finiteCallCount_ceilingBudget_real_le_sourceBudget
    (callCount : ℕ) (lower upper delta : ℝ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    ((callCount * fixedSampleBudget lower upper delta : ℕ) : ℝ) ≤
      (callCount : ℝ) *
        (2 / (upper - lower) ^ 2 * Real.log (2 / delta) + 1) := by
  have hbudget := fixedSampleBudget_lt_realTarget_add_one lower upper delta hdelta hdeltaLeOne
  calc
    ((callCount * fixedSampleBudget lower upper delta : ℕ) : ℝ) =
        (callCount : ℝ) * (fixedSampleBudget lower upper delta : ℝ) := by norm_num
    _ ≤ (callCount : ℝ) *
        (2 / (upper - lower) ^ 2 * Real.log (2 / delta) + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hbudget) (Nat.cast_nonneg _)

/-- The source regime `0 < δ ≤ 1` and a positive comparison gap make the ceiling budget positive. -/
theorem fixedSampleBudget_pos
    (lower upper delta : ℝ)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    0 < (fixedSampleBudget lower upper delta : ℝ) := by
  have hgap : 0 < upper - lower := sub_pos.mpr hseparation
  have hratio : 1 < 2 / delta := by
    apply (lt_div_iff₀ hdelta).mpr
    nlinarith
  have hlog : 0 < Real.log (2 / delta) := Real.log_pos hratio
  have htarget : 0 < 2 / (upper - lower) ^ 2 * Real.log (2 / delta) := by
    apply mul_pos
    · exact div_pos (by norm_num) (sq_pos_of_pos hgap)
    · exact hlog
  have hceiling := fixedSampleBudget_realTarget_le lower upper delta
  linarith

/--
The source's finite Hoeffding calculation.  Any positive natural comparison
count meeting the real budget `2 / d² * log (2 / δ)` makes the fixed-sample
tail at half-width `d / 2` at most `δ`.
-/
theorem fixedSampleCompare_tail_le_delta_of_budget
    (count : ℕ) (separation delta : ℝ)
    (hcount : 0 < (count : ℝ))
    (hseparation : 0 < separation)
    (hdelta : 0 < delta)
    (hbudget : 2 / separation ^ 2 * Real.log (2 / delta) ≤ (count : ℝ)) :
    2 * Real.exp (-((count : ℝ) * (separation / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤ delta := by
  have hseparationSqPos : 0 < separation ^ 2 := sq_pos_of_pos hseparation
  have hseparationSqNe : separation ^ 2 ≠ 0 := ne_of_gt hseparationSqPos
  have hfactorPos : 0 < separation ^ 2 / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hbudget (le_of_lt hfactorPos)
  have hlogBound : Real.log (2 / delta) ≤ (count : ℝ) * separation ^ 2 / 2 := by
    calc
      Real.log (2 / delta) =
          (2 / separation ^ 2 * Real.log (2 / delta)) * (separation ^ 2 / 2) := by
            field_simp [hseparationSqNe]
      _ ≤ (count : ℝ) * (separation ^ 2 / 2) := hscaled
      _ = (count : ℝ) * separation ^ 2 / 2 := by ring
  have hexponent : -(count : ℝ) * separation ^ 2 / 2 ≤ -Real.log (2 / delta) := by
    linarith
  have hratioPos : 0 < 2 / delta := div_pos (by norm_num) hdelta
  have hnegativeLogExp : Real.exp (-Real.log (2 / delta)) = delta / 2 := by
    rw [Real.exp_neg, Real.exp_log hratioPos]
    field_simp [ne_of_gt hdelta]
  have htailFormula :
      -((count : ℝ) * (separation / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)) =
          -(count : ℝ) * separation ^ 2 / 2 := by
    have hcountNe : (count : ℝ) ≠ 0 := ne_of_gt hcount
    field_simp [hcountNe]
    ring
  calc
    2 * Real.exp (-((count : ℝ) * (separation / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) =
        2 * Real.exp (-(count : ℝ) * separation ^ 2 / 2) := by rw [htailFormula]
    _ ≤ 2 * Real.exp (-Real.log (2 / delta)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ = delta := by rw [hnegativeLogExp]; ring

/--
The executable ceiling budget discharges the numeric tail premise in the
source's fixed-sample Compare guarantee for `0 < δ ≤ 1`.
-/
theorem fixedSampleCompare_tail_le_delta_of_ceilingBudget
    (lower upper delta : ℝ)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    2 * Real.exp (-((fixedSampleBudget lower upper delta : ℝ) *
      ((upper - lower) / 2)) ^ 2 /
      (2 * (fixedSampleBudget lower upper delta : ℝ) * (1 / 4 : ℝ))) ≤ delta :=
  fixedSampleCompare_tail_le_delta_of_budget (fixedSampleBudget lower upper delta)
    (upper - lower) delta
    (fixedSampleBudget_pos lower upper delta hseparation hdelta hdeltaLeOne)
    (sub_pos.mpr hseparation) hdelta
    (by simpa using fixedSampleBudget_realTarget_le lower upper delta)

/-- Lemma 1's fixed-sample lower guarantee with the executable ceiling budget. -/
theorem fixedSampleCompare_lower_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : trueGap ≤ lower)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome |
      fixedSampleCompare observation (fixedSampleBudget lower upper delta) lower upper outcome ≠ .lower} ≤
      delta :=
  fixedSampleCompare_lower_failure_probability law observation
    (fixedSampleBudget lower upper delta) lower upper trueGap delta
    hindependent hmeasurable hbounded hmean hgap
    (by linarith [sub_pos.mpr hseparation])
    (fixedSampleCompare_tail_le_delta_of_ceilingBudget lower upper delta
      hseparation hdelta hdeltaLeOne)

/-- Lemma 1's fixed-sample upper guarantee with the executable ceiling budget. -/
theorem fixedSampleCompare_upper_failure_probability_of_ceilingBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome |
      fixedSampleCompare observation (fixedSampleBudget lower upper delta) lower upper outcome ≠ .upper} ≤
      delta :=
  fixedSampleCompare_upper_failure_probability law observation
    (fixedSampleBudget lower upper delta) lower upper trueGap delta
    hindependent hmeasurable hbounded hmean hgap
    (by linarith [sub_pos.mpr hseparation])
    (fixedSampleCompare_tail_le_delta_of_ceilingBudget lower upper delta
      hseparation hdelta hdeltaLeOne)

end FalahatgarEtAl2017MaxingRanking
