import PRPKG24AccuracyDiversity.Uniform

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/-!
# A finite counterexample to the printed Proposition 2 constant

The likelihood vector below is the square of a positive rational unit vector.
Consequently it is an exact probability distribution and its square-root
profile is rational.  The allocation is globally optimal by the reusable
discrete shadow-price certificate in `AppliedModelingLib.Allocation`.

This file is deliberately a source-fidelity artifact rather than a paper-facing
replacement theorem: it records a concrete instance refuting the printed
`(m + 1) / n` finite error coefficient under the paper's stated hypotheses.
-/

noncomputable def proposition2CounterexampleRoot : ItemType 10 → ℝ :=
  ![(65600000 : ℝ) / 10000999614,
    (65400000 : ℝ) / 10000999614,
    (63600000 : ℝ) / 10000999614,
    (76200000 : ℝ) / 10000999614,
    (9999000386 : ℝ) / 10000999614,
    (65200000 : ℝ) / 10000999614,
    (63600000 : ℝ) / 10000999614,
    (64800000 : ℝ) / 10000999614,
    (70800000 : ℝ) / 10000999614,
    (63600000 : ℝ) / 10000999614]

noncomputable def proposition2CounterexampleLikelihood : ItemType 10 → ℝ :=
  fun t => proposition2CounterexampleRoot t ^ 2

def proposition2CounterexampleAllocation : CountAllocation 10 where
  count := ![11, 11, 11, 13, 1898, 11, 11, 11, 12, 11]

noncomputable def proposition2CounterexampleShadowPrice : ℝ :=
  proposition2CounterexampleLikelihood (4 : ItemType 10) /
    ((1899 : ℝ) * 1900)

private theorem proposition2CounterexampleRoot_nonnegative (t : ItemType 10) :
    0 ≤ proposition2CounterexampleRoot t := by
  fin_cases t <;> norm_num [proposition2CounterexampleRoot]

theorem proposition2Counterexample_root_sum_sq :
    ∑ t : ItemType 10, proposition2CounterexampleRoot t ^ 2 = 1 := by
  norm_num [proposition2CounterexampleRoot, Fin.sum_univ_succ]

theorem proposition2Counterexample_likelihood_is_probability :
    ∑ t : ItemType 10, proposition2CounterexampleLikelihood t = 1 := by
  simpa [proposition2CounterexampleLikelihood] using
    proposition2Counterexample_root_sum_sq

theorem sqrt_proposition2CounterexampleLikelihood (t : ItemType 10) :
    Real.sqrt (proposition2CounterexampleLikelihood t) =
      proposition2CounterexampleRoot t := by
  rw [proposition2CounterexampleLikelihood, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (proposition2CounterexampleRoot_nonnegative t)

private theorem proposition2Counterexample_root_sum :
    ∑ t : ItemType 10, proposition2CounterexampleRoot t =
      (10597800386 : ℝ) / 10000999614 := by
  norm_num [proposition2CounterexampleRoot, Fin.sum_univ_succ]

private theorem proposition2Counterexample_sqrt_sum :
    ∑ t : ItemType 10, Real.sqrt (proposition2CounterexampleLikelihood t) =
      (10597800386 : ℝ) / 10000999614 := by
  calc
    ∑ t : ItemType 10, Real.sqrt (proposition2CounterexampleLikelihood t) =
        ∑ t : ItemType 10, proposition2CounterexampleRoot t := by
          apply Finset.sum_congr rfl
          intro t _
          exact sqrt_proposition2CounterexampleLikelihood t
    _ = (10597800386 : ℝ) / 10000999614 :=
      proposition2Counterexample_root_sum

/-- The source's `k = 1` minimum-share hypothesis holds for this exact PMF. -/
theorem proposition2Counterexample_source_eligibility :
    (1 : ℝ) + 1 ≤ 2000 *
      uniformSqrtMinShare proposition2CounterexampleLikelihood - 10 := by
  have hfloor : (3 : ℝ) / 500 ≤
      uniformSqrtMinShare proposition2CounterexampleLikelihood := by
    unfold uniformSqrtMinShare
    apply AppliedModelingLib.le_finiteMin
    intro t
    rw [sqrt_proposition2CounterexampleLikelihood, proposition2Counterexample_sqrt_sum]
    fin_cases t <;> norm_num [proposition2CounterexampleRoot]
  nlinarith

private theorem proposition2CounterexampleAllocation_total :
    AppliedModelingLib.Allocation.HasTotal proposition2CounterexampleAllocation 2000 := by
  norm_num [AppliedModelingLib.Allocation.HasTotal,
    AppliedModelingLib.Allocation.total, proposition2CounterexampleAllocation,
    Fin.sum_univ_succ]

theorem proposition2Counterexample_is_optimal :
    (uniformTopOneConsumptionModel proposition2CounterexampleLikelihood).IsOptimalAtTotal
      2000 proposition2CounterexampleAllocation := by
  change AppliedModelingLib.Allocation.IsOptimalAtTotal
    proposition2CounterexampleLikelihood (fun _ q => uniformTopOneValue q)
    2000 proposition2CounterexampleAllocation
  apply AppliedModelingLib.Allocation.isOptimalAtTotal_of_shadowPrice
    proposition2CounterexampleAllocation proposition2CounterexampleLikelihood
    (fun _ q => uniformTopOneValue q) 2000 proposition2CounterexampleShadowPrice
  · exact proposition2CounterexampleAllocation_total
  · exact uniformTopOneConsumptionModel_has_diminishing_returns
      proposition2CounterexampleLikelihood
  · intro t
    change 0 ≤ proposition2CounterexampleRoot t ^ 2
    positivity
  · intro t
    fin_cases t <;>
      simp [proposition2CounterexampleShadowPrice,
        proposition2CounterexampleLikelihood, proposition2CounterexampleRoot,
        proposition2CounterexampleAllocation,
        AppliedModelingLib.Allocation.weightedForwardMarginal,
        AppliedModelingLib.Allocation.marginal, uniformTopOneValue] <;>
      norm_num [proposition2CounterexampleShadowPrice,
        proposition2CounterexampleLikelihood, proposition2CounterexampleRoot,
        proposition2CounterexampleAllocation,
        AppliedModelingLib.Allocation.weightedForwardMarginal,
        AppliedModelingLib.Allocation.marginal, uniformTopOneValue]
  · intro t ht
    fin_cases t <;>
      simp [proposition2CounterexampleShadowPrice,
        proposition2CounterexampleLikelihood, proposition2CounterexampleRoot,
        proposition2CounterexampleAllocation,
        AppliedModelingLib.Allocation.weightedBackwardMarginal,
        uniformTopOneValue] at ht ⊢ <;>
      norm_num [proposition2CounterexampleShadowPrice,
        proposition2CounterexampleLikelihood, proposition2CounterexampleRoot,
        proposition2CounterexampleAllocation,
        AppliedModelingLib.Allocation.weightedBackwardMarginal,
        uniformTopOneValue] at ht ⊢

/-- At type four, the exact optimal allocation exceeds the printed error bound. -/
theorem proposition2Counterexample_sharp_error_exceeds_printed_bound :
    (11 : ℝ) / 2000 <
      |AppliedModelingLib.Allocation.share proposition2CounterexampleAllocation
          (4 : ItemType 10) -
        Real.sqrt (proposition2CounterexampleLikelihood (4 : ItemType 10)) /
          ∑ i : ItemType 10, Real.sqrt (proposition2CounterexampleLikelihood i)| := by
  rw [sqrt_proposition2CounterexampleLikelihood,
    proposition2Counterexample_sqrt_sum]
  simp [AppliedModelingLib.Allocation.share,
    AppliedModelingLib.Allocation.total, proposition2CounterexampleAllocation,
    Fin.sum_univ_succ, proposition2CounterexampleRoot]
  norm_num

/--
The printed Proposition 2 conclusion with coefficient `(m + 1) / n` is false
even for `m = 10`, `n = 2000`, and a strictly positive exact probability
distribution satisfying its `k = 1` eligibility condition.
-/
theorem proposition2Counterexample_violates_printed_constant :
    ¬ ∀ t : ItemType 10,
      |AppliedModelingLib.Allocation.share proposition2CounterexampleAllocation t -
        Real.sqrt (proposition2CounterexampleLikelihood t) /
          ∑ i : ItemType 10, Real.sqrt (proposition2CounterexampleLikelihood i)| ≤
        (10 + 1 : ℝ) / 2000 := by
  intro h
  have hfour := h (4 : ItemType 10)
  exact (not_le_of_gt proposition2Counterexample_sharp_error_exceeds_printed_bound)
    (by norm_num at hfour ⊢; exact hfour)

end PRPKG24AccuracyDiversity
