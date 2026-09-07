import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Gradients of finite PMF expectations

For a finite probability mass function, differentiation commutes with the
finite expectation of a real-valued, pointwise differentiable objective.  The
result is the finite analogue of the gradient/expectation interchange needed
by stochastic-gradient analyses, with no unproved dominated-convergence or
regularity boundary.

## Upstream formalization credit

The proof directly uses Mathlib's `HasFDerivAt.const_smul` and
`HasFDerivAt.fun_sum` from
[`Mathlib/Analysis/Calculus/FDeriv/Add.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/FDeriv/Add.lean)
at the repository-pinned revision
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
Mathlib is Apache-2.0 licensed. No upstream proof or code is copied or ported.
-/

namespace AppliedModelingLib

open scoped BigOperators InnerProductSpace

variable {Sample Parameter : Type*}
variable [Fintype Sample] [DecidableEq Sample]
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]

/-- A finite PMF expectation has the finite PMF expectation of pointwise gradients. -/
theorem hasGradientAt_pmfExp
    (sampleLaw : PMF Sample) (objective : Parameter → Sample → ℝ)
    (gradient : Parameter → Sample → Parameter)
    (hgradientAt : ∀ parameter sample,
      HasGradientAt (fun other => objective other sample) (gradient parameter sample) parameter)
    (parameter : Parameter) :
    HasGradientAt (fun other => pmfExp sampleLaw (objective other))
      (pmfVectorExp sampleLaw (gradient parameter)) parameter := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsum : HasFDerivAt
      (fun other => ∑ sample : Sample, (sampleLaw sample).toReal * objective other sample)
      (∑ sample : Sample, (sampleLaw sample).toReal •
        (InnerProductSpace.toDual ℝ Parameter) (gradient parameter sample)) parameter := by
    apply HasFDerivAt.fun_sum
    intro sample _
    simpa using (hgradientAt parameter sample).hasFDerivAt.const_smul
      (sampleLaw sample).toReal
  simpa [pmfExp, pmfVectorExp] using hsum

/--
The finite expectation of uniformly Lipschitz vector statistics is Lipschitz
with the same constant.  This is the finite aggregation step for gradients of
per-sample smooth objectives.
-/
theorem norm_pmfVectorExp_sub_le_of_forall_lipschitz
    {Index : Type*} [NormedAddCommGroup Index]
    (sampleLaw : PMF Sample) (statistic : Index → Sample → Parameter)
    (constant : ℝ)
    (first second : Index)
    (hlipschitz : ∀ sample,
      ‖statistic first sample - statistic second sample‖ ≤ constant * ‖first - second‖) :
    ‖pmfVectorExp sampleLaw (statistic first) -
        pmfVectorExp sampleLaw (statistic second)‖ ≤ constant * ‖first - second‖ := by
  rw [← pmfVectorExp_sub]
  calc
    ‖pmfVectorExp sampleLaw (fun sample => statistic first sample - statistic second sample)‖ ≤
        pmfExp sampleLaw (fun sample => ‖statistic first sample - statistic second sample‖) :=
      norm_pmfVectorExp_le_pmfExp_norm sampleLaw _
    _ ≤ pmfExp sampleLaw (fun _ => constant * ‖first - second‖) :=
      pmfExp_le_pmfExp_of_forall_le sampleLaw _ _ hlipschitz
    _ = constant * ‖first - second‖ := pmfExp_const sampleLaw _

/--
The inner product of a fixed vector with a centered finite-PMF statistic has
the corresponding centered inner product.  This is the finite unbiasedness
identity used by stochastic-gradient arguments.
-/
theorem pmfExp_inner_sub_eq_inner_sub_pmfVectorExp
    (sampleLaw : PMF Sample) (statistic : Sample → Parameter) (point : Parameter) :
    pmfExp sampleLaw (fun sample => ⟪point, point - statistic sample⟫_ℝ) =
      ⟪point, point - pmfVectorExp sampleLaw statistic⟫_ℝ := by
  rw [show (fun sample => ⟪point, point - statistic sample⟫_ℝ) =
      (fun sample => ⟪point, point⟫_ℝ - ⟪point, statistic sample⟫_ℝ) by
    funext sample
    rw [inner_sub_right]]
  rw [pmfExp_sub, pmfExp_const]
  simp [pmfExp, pmfVectorExp, inner_sub_right, inner_sum, real_inner_smul_right]

/-- A finite-PMF gradient estimator is unbiased against its own expectation. -/
theorem pmfExp_inner_pmfVectorExp_sub_eq_zero
    (sampleLaw : PMF Sample) (statistic : Sample → Parameter) :
    pmfExp sampleLaw (fun sample =>
      ⟪pmfVectorExp sampleLaw statistic,
        pmfVectorExp sampleLaw statistic - statistic sample⟫_ℝ) = 0 := by
  simpa using
    (pmfExp_inner_sub_eq_inner_sub_pmfVectorExp sampleLaw statistic
      (pmfVectorExp sampleLaw statistic))

/-- A fixed linear functional commutes with a finite vector expectation. -/
theorem pmfExp_inner_eq_inner_pmfVectorExp
    (sampleLaw : PMF Sample) (statistic : Sample → Parameter) (point : Parameter) :
    pmfExp sampleLaw (fun sample => ⟪point, statistic sample⟫_ℝ) =
      ⟪point, pmfVectorExp sampleLaw statistic⟫_ℝ := by
  simp [pmfExp, pmfVectorExp, inner_sum, real_inner_smul_right]

/-- A fixed linear functional of a finite-PMF sample has zero mean after
subtracting that sample's vector expectation.  This is the unbiasedness
identity used when a proper randomized prediction is compared with its
convex-mixture representative. -/
theorem pmfExp_inner_sub_pmfVectorExp_eq_zero
    (sampleLaw : PMF Sample) (statistic : Sample → Parameter) (point : Parameter) :
    pmfExp sampleLaw (fun sample =>
      ⟪point, statistic sample - pmfVectorExp sampleLaw statistic⟫_ℝ) = 0 := by
  rw [show (fun sample => ⟪point, statistic sample - pmfVectorExp sampleLaw statistic⟫_ℝ) =
      (fun sample => ⟪point, statistic sample⟫_ℝ -
        ⟪point, pmfVectorExp sampleLaw statistic⟫_ℝ) by
      funext sample
      rw [inner_sub_right]]
  rw [pmfExp_sub, pmfExp_const, pmfExp_inner_eq_inner_pmfVectorExp]
  ring

end AppliedModelingLib
