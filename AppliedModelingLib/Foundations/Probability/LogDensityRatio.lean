import AppliedModelingLib.Foundations.Probability.FiniteKL

/-!
# Finite PMF log-density-ratio bounds

This finite interface records a source distribution's pointwise log-density
ratio relative to a reference distribution, only at atoms with positive source
mass.  That support-aware formulation avoids treating Lean's totalized
`Real.log 0` as a statistical density-ratio convention.

## Main declarations

- `PMFLogDensityRatioUpperBound`
- `pmfLogDensityRatioUpperBound_atom_domination`
- `pmfLogDensityRatioUpperBound_expectation_domination`
-/

open scoped BigOperators

namespace AppliedModelingLib

/--
`source` has pointwise log-density ratio at most `logBound` relative to
`reference`, on the support of `source`.  Absolute continuity is explicit, so
the logarithm of the reference mass is only used where it is positive.
-/
def PMFLogDensityRatioUpperBound {α : Type*}
    (source reference : PMF α) (logBound : ℝ) : Prop :=
  PMFAbsoluteContinuous source reference ∧
    ∀ outcome, 0 < (source outcome).toReal →
      Real.log (source outcome).toReal - Real.log (reference outcome).toReal ≤ logBound

/-- A distribution has log-density ratio zero relative to itself. -/
theorem pmfLogDensityRatioUpperBound_self {α : Type*}
    (law : PMF α) :
    PMFLogDensityRatioUpperBound law law 0 := by
  constructor
  · intro outcome hpositive
    exact hpositive
  · intro outcome _
    simp

/-- A log-density-ratio upper bound remains valid after increasing its bound. -/
theorem PMFLogDensityRatioUpperBound.mono {α : Type*}
    {source reference : PMF α} {firstBound secondBound : ℝ}
    (hbound : PMFLogDensityRatioUpperBound source reference firstBound)
    (hle : firstBound ≤ secondBound) :
    PMFLogDensityRatioUpperBound source reference secondBound := by
  constructor
  · exact hbound.1
  · intro outcome hsource
    exact (hbound.2 outcome hsource).trans hle

/--
A finite log-density-ratio upper bound gives pointwise multiplicative
domination by the reference mass.
-/
theorem pmfLogDensityRatioUpperBound_atom_domination
    {α : Type*} (source reference : PMF α) (logBound : ℝ)
    (hbound : PMFLogDensityRatioUpperBound source reference logBound)
    (outcome : α) :
    (source outcome).toReal ≤ Real.exp logBound * (reference outcome).toReal := by
  by_cases hsource_zero : (source outcome).toReal = 0
  · rw [hsource_zero]
    exact mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  · have hsource : 0 < (source outcome).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hsource_zero)
    have href : 0 < (reference outcome).toReal := hbound.1 outcome hsource
    have hlog := hbound.2 outcome hsource
    have hexp :
        Real.exp (Real.log (source outcome).toReal) ≤
          Real.exp (logBound + Real.log (reference outcome).toReal) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      (source outcome).toReal = Real.exp (Real.log (source outcome).toReal) :=
        (Real.exp_log hsource).symm
      _ ≤ Real.exp (logBound + Real.log (reference outcome).toReal) := hexp
      _ = Real.exp logBound * (reference outcome).toReal := by
        rw [Real.exp_add, Real.exp_log href]

/--
Every nonnegative finite expectation under a log-density-ratio-bounded source
law is at most `exp logBound` times the reference expectation.
-/
theorem pmfLogDensityRatioUpperBound_expectation_domination
    {α : Type*} [Fintype α] [DecidableEq α]
    (source reference : PMF α) (logBound : ℝ)
    (hbound : PMFLogDensityRatioUpperBound source reference logBound)
    (score : α → ℝ) (hscore : ∀ outcome, 0 ≤ score outcome) :
    pmfExp source score ≤ Real.exp logBound * pmfExp reference score := by
  unfold pmfExp
  calc
    ∑ outcome : α, (source outcome).toReal * score outcome ≤
        ∑ outcome : α,
          (Real.exp logBound * (reference outcome).toReal) * score outcome := by
            refine Finset.sum_le_sum fun outcome _ => ?_
            exact mul_le_mul_of_nonneg_right
              (pmfLogDensityRatioUpperBound_atom_domination source reference logBound
                hbound outcome)
              (hscore outcome)
    _ = ∑ outcome : α,
          Real.exp logBound * ((reference outcome).toReal * score outcome) := by
            refine Finset.sum_congr rfl fun outcome _ => ?_
            ring
    _ = Real.exp logBound * ∑ outcome : α,
          (reference outcome).toReal * score outcome := by
            rw [Finset.mul_sum]

end AppliedModelingLib
