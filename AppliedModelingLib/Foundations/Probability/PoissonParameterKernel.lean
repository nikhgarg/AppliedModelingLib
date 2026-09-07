import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

/-!
# Poisson kernels with a random nonnegative parameter

This module packages the Poisson distribution as a Markov kernel from its
nonnegative mean to its count.  It is the reusable measurability bridge for
mixing a Poissonized countable-state evolution over a random duration.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Draw a Poisson count whose mean is the nonnegative input parameter. -/
noncomputable def poissonParameterKernel : Kernel ℝ≥0 ℕ where
  toFun := poissonMeasure
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    change Measurable fun mean : ℝ≥0 => poissonMeasure mean s
    simp only [ProbabilityTheory.poissonMeasure, Measure.sum_apply _ hs]
    apply Measurable.ennreal_tsum
    intro count
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    by_cases hcount : count ∈ s
    · simp only [Set.indicator_of_mem hcount]
      fun_prop
    · simp only [Set.indicator_of_notMem hcount, mul_zero]
      exact measurable_const

instance : IsMarkovKernel poissonParameterKernel where
  isProbabilityMeasure _ := isProbabilityMeasure_poissonMeasure _

end AppliedModelingLib.Probability
