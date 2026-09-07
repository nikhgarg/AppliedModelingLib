import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration

/-!
# Fixed-sample Compare

Section 3.1.1 describes Compare at its maximum sample budget before the
supplement refines it with early stopping.  This file formalizes that
fixed-sample decision and the concentration event that makes its two promises
correct.  It is a source-faithful conservative execution surface for the
Lemma-1 proof route.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The two conclusions returned by `Compare(i, j, ε_l, ε_u, δ)`. -/
inductive CompareDecision where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The centered cumulative error of a fixed batch of binary comparison observations. -/
def fixedSampleCenteredError {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (mean : ℝ) (outcome : Ω) : ℝ :=
  ∑ index ∈ Finset.range count, (observation index outcome - mean)

/-- The strict terminal concentration event used by the fixed-sample Compare rule. -/
def FixedSampleConcentrated {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (mean error : ℝ) (outcome : Ω) : Prop :=
  |fixedSampleCenteredError observation count mean outcome| < (count : ℝ) * error

/--
The non-adaptive maximum-budget form described in Section 3.1.1: compare the
empirical win total with the midpoint of the two centered preference limits.
-/
noncomputable def fixedSampleCompare {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper : ℝ) (outcome : Ω) :
    CompareDecision :=
  if ∑ index ∈ Finset.range count, observation index outcome ≤
      (count : ℝ) * (1 / 2 + (lower + upper) / 2)
    then .lower
    else .upper

/-- Expanding a batch total into its centered error plus its mean. -/
theorem fixedSample_sum_eq_centeredError_add_mean {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (mean : ℝ) (outcome : Ω) :
    (∑ index ∈ Finset.range count, observation index outcome) =
      fixedSampleCenteredError observation count mean outcome + (count : ℝ) * mean := by
  rw [show (∑ index ∈ Finset.range count, observation index outcome) =
      ∑ index ∈ Finset.range count,
        ((observation index outcome - mean) + mean) by
      apply Finset.sum_congr rfl
      intro index _
      ring]
  rw [Finset.sum_add_distrib]
  simp [fixedSampleCenteredError]

/--
If the true centered preference is at most the lower limit, terminal
concentration makes the fixed-sample Compare return its lower conclusion.
-/
theorem fixedSampleCompare_lower_of_concentrated {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap : ℝ) (outcome : Ω)
    (hgap : trueGap ≤ lower)
    (hconcentrated : FixedSampleConcentrated observation count
      (1 / 2 + trueGap) ((upper - lower) / 2) outcome) :
    fixedSampleCompare observation count lower upper outcome = .lower := by
  unfold fixedSampleCompare
  apply if_pos
  have herrorUpper :
      fixedSampleCenteredError observation count (1 / 2 + trueGap) outcome <
        (count : ℝ) * ((upper - lower) / 2) :=
    lt_of_le_of_lt (le_abs_self _) hconcentrated
  have hscaledGap : (count : ℝ) * trueGap ≤ (count : ℝ) * lower :=
    mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg count)
  rw [fixedSample_sum_eq_centeredError_add_mean observation count (1 / 2 + trueGap) outcome]
  nlinarith

/--
If the true centered preference is at least the upper limit, terminal
concentration makes the fixed-sample Compare return its upper conclusion.
-/
theorem fixedSampleCompare_upper_of_concentrated {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap : ℝ) (outcome : Ω)
    (hgap : upper ≤ trueGap)
    (hconcentrated : FixedSampleConcentrated observation count
      (1 / 2 + trueGap) ((upper - lower) / 2) outcome) :
    fixedSampleCompare observation count lower upper outcome = .upper := by
  unfold fixedSampleCompare
  apply if_neg
  intro hdecision
  have herrorLower := (abs_lt.mp hconcentrated).1
  have hscaledGap : (count : ℝ) * upper ≤ (count : ℝ) * trueGap :=
    mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg count)
  rw [fixedSample_sum_eq_centeredError_add_mean observation count (1 / 2 + trueGap) outcome] at hdecision
  nlinarith

/--
The shared iid Hoeffding theorem bounds the complement of the terminal
concentration event.  This is the statistical input to the fixed-sample form
of Lemma 1; the source's adaptive stopping proof remains a separate layer.
-/
theorem fixedSample_nonconcentration_probability {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (mean error : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count, law[observation index] = mean)
    (herror : 0 ≤ error) :
    law.real {outcome | ¬ FixedSampleConcentrated observation count mean error outcome} ≤
      2 * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := iidBoundedObservation_centeredSum_abs_upperTail law observation count
    hindependent hmeasurable hbounded error herror
  have hsum : ∀ outcome,
      fixedSampleCenteredError observation count mean outcome =
        ∑ index ∈ Finset.range count,
          (observation index outcome - law[observation index]) := by
    intro outcome
    unfold fixedSampleCenteredError
    apply Finset.sum_congr rfl
    intro index hindex
    rw [hmean index (Finset.mem_range.mp hindex)]
  have hevent :
      {outcome | ¬ FixedSampleConcentrated observation count mean error outcome} =
        {outcome | (count : ℝ) * error ≤
          |∑ index ∈ Finset.range count,
            (observation index outcome - law[observation index])|} := by
    ext outcome
    simp only [Set.mem_setOf_eq, FixedSampleConcentrated, not_lt]
    rw [hsum outcome]
  rw [hevent]
  exact htail

/--
Lemma 1's lower-hypothesis guarantee for the fixed-budget Compare rule.  The
numeric `htail` premise is exactly the final Hoeffding-tail calculation that a
rounded source sample budget must discharge.
-/
theorem fixedSampleCompare_lower_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count, law[observation index] = 1 / 2 + trueGap)
    (hgap : trueGap ≤ lower)
    (hseparation : 0 ≤ (upper - lower) / 2)
    (htail : 2 * Real.exp (-((count : ℝ) * ((upper - lower) / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤ delta) :
    law.real {outcome |
      fixedSampleCompare observation count lower upper outcome ≠ .lower} ≤ delta := by
  calc
    law.real {outcome |
        fixedSampleCompare observation count lower upper outcome ≠ .lower} ≤
        law.real {outcome | ¬ FixedSampleConcentrated observation count
          (1 / 2 + trueGap) ((upper - lower) / 2) outcome} := by
          refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
          intro outcome hfailure
          by_contra hconcentrated
          apply hfailure
          exact fixedSampleCompare_lower_of_concentrated observation count lower upper trueGap
            outcome hgap (by simpa using hconcentrated)
    _ ≤ 2 * Real.exp (-((count : ℝ) * ((upper - lower) / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
      fixedSample_nonconcentration_probability law observation count (1 / 2 + trueGap)
        ((upper - lower) / 2) hindependent hmeasurable hbounded hmean hseparation
    _ ≤ delta := htail

/-- Lemma 1's symmetric upper-hypothesis guarantee for fixed-budget Compare. -/
theorem fixedSampleCompare_upper_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun observation law)
    (hmeasurable : ∀ index, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count, law[observation index] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap)
    (hseparation : 0 ≤ (upper - lower) / 2)
    (htail : 2 * Real.exp (-((count : ℝ) * ((upper - lower) / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤ delta) :
    law.real {outcome |
      fixedSampleCompare observation count lower upper outcome ≠ .upper} ≤ delta := by
  calc
    law.real {outcome |
        fixedSampleCompare observation count lower upper outcome ≠ .upper} ≤
        law.real {outcome | ¬ FixedSampleConcentrated observation count
          (1 / 2 + trueGap) ((upper - lower) / 2) outcome} := by
          refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
          intro outcome hfailure
          by_contra hconcentrated
          apply hfailure
          exact fixedSampleCompare_upper_of_concentrated observation count lower upper trueGap
            outcome hgap (by simpa using hconcentrated)
    _ ≤ 2 * Real.exp (-((count : ℝ) * ((upper - lower) / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) :=
      fixedSample_nonconcentration_probability law observation count (1 / 2 + trueGap)
        ((upper - lower) / 2) hindependent hmeasurable hbounded hmean hseparation
    _ ≤ delta := htail

end FalahatgarEtAl2017MaxingRanking
