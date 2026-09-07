import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.FiniteSimplex

/-!
# Optimization over finite KL balls

This module proves attainment for linear objectives on a finite probability
simplex intersected with a finite Kullback--Leibler sublevel set.  It works
through the real standard simplex, where compactness and continuity are
transparent, and converts the resulting maximizer back to a finite `PMF`.

## Main declarations

- `finiteKLBall`
- `finiteKLBall_zero_eq_singleton`
- `exists_finiteKL_maximizer`
-/

namespace AppliedModelingLib

open scoped BigOperators

noncomputable section

/-- The finite-PMF KL ball centered at `reference` with radius `radius`. -/
def finiteKLBall {α : Type*} [Fintype α] [DecidableEq α]
    (reference : PMF α) (radius : ℝ) : Set (PMF α) :=
  {policy | finiteKLDivergence policy reference ≤ radius}

/--
With a full-support reference PMF, a zero-radius finite KL ball contains only
the reference.  This is the finite simplex boundary corresponding to an
infinite KL-regularization weight.
-/
theorem finiteKLBall_zero_eq_singleton
    {α : Type*} [Fintype α] [DecidableEq α]
    (reference : PMF α) (hreference : PMFFullSupport reference) :
    finiteKLBall reference 0 = {reference} := by
  ext policy
  simp only [finiteKLBall, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact finiteKLDivergence_le_zero_iff_eq policy reference hreference

/-- The finite KL expression is continuous in real-simplex coordinates. -/
theorem continuous_finiteKLDivergence_stdSimplexToPMF
    {α : Type*} [Fintype α] [DecidableEq α] (reference : PMF α) :
    Continuous (fun mass : stdSimplex ℝ α =>
      finiteKLDivergence (stdSimplexToPMF mass) reference) := by
  simp only [finiteKLDivergence, stdSimplexToPMF_apply_toReal]
  apply continuous_finset_sum
  intro outcome _
  have hmass : Continuous (fun mass : stdSimplex ℝ α => mass.1 outcome) :=
    (continuous_apply outcome).comp continuous_subtype_val
  have href : Continuous (fun _mass : stdSimplex ℝ α =>
      Real.log (reference outcome).toReal) := continuous_const
  simpa only [Function.comp_apply, mul_sub] using
    (Real.continuous_mul_log.comp hmass).sub (hmass.mul href)

/-- A finite PMF expectation is continuous in real-simplex coordinates. -/
theorem continuous_pmfExp_stdSimplexToPMF
    {α : Type*} [Fintype α] [DecidableEq α] (score : α → ℝ) :
    Continuous (fun mass : stdSimplex ℝ α =>
      pmfExp (stdSimplexToPMF mass) score) := by
  simp only [pmfExp, stdSimplexToPMF_apply_toReal]
  apply continuous_finset_sum
  intro outcome _
  exact ((continuous_apply outcome).comp continuous_subtype_val).mul continuous_const

/--
A linear finite-PMF objective attains a maximum on every nonnegative-radius
finite KL ball.  The conclusion supplies the policy, its KL feasibility, and
the global comparison property used by constrained policy definitions.
-/
theorem exists_finiteKL_maximizer
    {α : Type*} [Fintype α] [DecidableEq α]
    (reference : PMF α) (radius : ℝ) (hradius : 0 ≤ radius)
    (score : α → ℝ) :
    ∃ policy : PMF α, policy ∈ finiteKLBall reference radius ∧
      ∀ other : PMF α, other ∈ finiteKLBall reference radius →
        pmfExp other score ≤ pmfExp policy score := by
  let feasible : Set (stdSimplex ℝ α) :=
    {mass | finiteKLDivergence (stdSimplexToPMF mass) reference ≤ radius}
  have hclosed : IsClosed feasible := by
    dsimp [feasible]
    exact isClosed_le
      (continuous_finiteKLDivergence_stdSimplexToPMF reference) continuous_const
  have hcompact : IsCompact feasible :=
    isCompact_univ.of_isClosed_subset hclosed (Set.subset_univ _)
  have hnonempty : feasible.Nonempty := by
    refine ⟨pmfToStdSimplex reference, ?_⟩
    dsimp [feasible]
    rw [stdSimplexToPMF_pmfToStdSimplex, finiteKLDivergence_self]
    exact hradius
  obtain ⟨mass, hmass_feasible, hmass_max⟩ := hcompact.exists_isMaxOn hnonempty
    (continuous_pmfExp_stdSimplexToPMF score).continuousOn
  refine ⟨stdSimplexToPMF mass, ?_, ?_⟩
  · exact hmass_feasible
  · intro other hother_feasible
    have hother_mem : pmfToStdSimplex other ∈ feasible := by
      dsimp [feasible]
      change finiteKLDivergence other reference ≤ radius at hother_feasible
      rw [stdSimplexToPMF_pmfToStdSimplex]
      exact hother_feasible
    have hmax := hmass_max hother_mem
    change pmfExp (stdSimplexToPMF (pmfToStdSimplex other)) score ≤
      pmfExp (stdSimplexToPMF mass) score at hmax
    rw [stdSimplexToPMF_pmfToStdSimplex] at hmax
    exact hmax

end

end AppliedModelingLib
