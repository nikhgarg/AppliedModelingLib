import MBJG25ProducerFairness.PaperInterface

/-!
# Proof Interface: Prior-Weighted Rating Fairness

The two public endpoints prove the complete named source theorems. The final
three lemmas are narrowly scoped mathematical support for the documented
printed-source corrections.
-/

namespace MBJG25ProducerFairness

theorem paper_theorem3_1_proof
    {alpha beta q etaLow etaHigh : ℝ} {t : ℕ}
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hetaLow : 0 ≤ etaLow)
    (hetaOrder : etaLow ≤ etaHigh) :
    paper_theorem3_1Spec halpha hbeta ht hq0 hq1 hetaLow hetaOrder := by
  have hshape : 0 < alpha + beta := by linarith
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  constructor
  · simpa [paper_conditional_squared_bias, paper_conditional_bias,
      paper_expected_posterior_mean,
      AppliedModelingLib.Statistics.priorWeightedSquaredBias,
      AppliedModelingLib.Statistics.priorWeightedBias,
      AppliedModelingLib.Statistics.priorWeightedPosteriorMean] using
      paper_theorem3_1_squared_bias_nondecreasing
        (alpha := alpha) (beta := beta) (t := (t : ℝ)) (q := q)
        (etaLow := etaLow) (etaHigh := etaHigh) hshape htR hetaLow hetaOrder
  constructor
  · simpa [paper_conditional_variance, AppliedModelingLib.Statistics.priorWeightedVariance] using
      paper_theorem3_1_variance_weak_decrease
        (alpha := alpha) (beta := beta) (t := (t : ℝ)) (q := q)
        (etaLow := etaLow) (etaHigh := etaHigh) hshape htR hq0 hq1 hetaLow hetaOrder
  · intro hqInterior0 hqInterior1 hetaStrict
    simpa [paper_conditional_variance, AppliedModelingLib.Statistics.priorWeightedVariance] using
      paper_theorem3_1_variance_strict_decrease_interior
        (alpha := alpha) (beta := beta) (t := (t : ℝ)) (q := q)
        (etaLow := etaLow) (etaHigh := etaHigh) hshape htR hqInterior0 hqInterior1
        hetaLow hetaStrict

theorem paper_theorem3_2_proof
    {alpha beta eta : ℝ} {t : ℕ}
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (heta : 0 ≤ eta)
    (ht : 0 < t) :
    paper_theorem3_2Spec halpha hbeta heta ht := by
  have hshape : 0 < alpha + beta := by linarith
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hdenPos : 0 < eta * alpha + eta * beta + (t : ℝ) := by
    calc
      0 < eta * (alpha + beta) + (t : ℝ) :=
        add_pos_of_nonneg_of_pos (mul_nonneg heta hshape.le) htR
      _ = eta * alpha + eta * beta + (t : ℝ) := by ring
  have hconv := paper_theorem3_2_squared_bias_convex_in_quality
    (alpha := alpha) (beta := beta) (eta := eta) (t := (t : ℝ)) (ne_of_gt hdenPos)
  have hmin := paper_theorem3_2_squared_bias_global_min_at_prior_mean
    (alpha := alpha) (beta := beta) (eta := eta) (t := (t : ℝ)) hshape heta htR
  have hconc := paper_theorem3_2_variance_concave_in_quality
    (alpha := alpha) (beta := beta) (eta := eta) (t := (t : ℝ)) htR.le
  have hmax := paper_theorem3_2_variance_global_max_at_half
    (alpha := alpha) (beta := beta) (eta := eta) (t := (t : ℝ)) htR.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y lam _ _ _ _ hlam0 hlam1
    simpa [paper_conditional_squared_bias, paper_conditional_bias,
      paper_expected_posterior_mean,
      AppliedModelingLib.Statistics.priorWeightedSquaredBias,
      AppliedModelingLib.Statistics.priorWeightedBias,
      AppliedModelingLib.Statistics.priorWeightedPosteriorMean] using
      hconv x y lam hlam0 hlam1
  · refine ⟨?_, ?_, ?_⟩
    · exact div_nonneg halpha.le hshape.le
    · rw [div_le_iff₀ hshape]
      linarith
    · intro q _ _
      simpa [paper_conditional_squared_bias, paper_conditional_bias,
        paper_expected_posterior_mean,
        AppliedModelingLib.Statistics.priorWeightedSquaredBias,
        AppliedModelingLib.Statistics.priorWeightedBias,
        AppliedModelingLib.Statistics.priorWeightedPosteriorMean] using hmin q
  · intro x y lam _ _ _ _ hlam0 hlam1
    simpa [paper_conditional_variance, AppliedModelingLib.Statistics.priorWeightedVariance] using
      hconc x y lam hlam0 hlam1
  · intro q _ _
    simpa [paper_conditional_variance, AppliedModelingLib.Statistics.priorWeightedVariance] using hmax q

/-- At either Bernoulli endpoint, the variance is independent of prior strength. -/
theorem paper_theorem3_1_variance_endpoint_zero
    (alpha beta etaLow etaHigh : ℝ) (t : ℕ) :
    ¬ paper_conditional_variance alpha beta etaHigh t 0 <
      paper_conditional_variance alpha beta etaLow t 0 := by
  simpa [paper_conditional_variance, AppliedModelingLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
      alpha beta (t : ℝ) etaLow etaHigh

/-- Appendix D's displayed weighted average has the indicated Beta pseudo-counts. -/
theorem paper_eq20_bayesian_rating_equivalence
    (n k : ℕ) (m C : ℝ) (hn : 0 < n) :
    let nR := (n : ℝ)
    let kR := (k : ℝ)
    nR / (nR + m) * (kR / nR) + m / (nR + m) * C =
        (kR + m * C) / (nR + m) ∧
      paper_posterior_rating (m * C) (m * (1 - C)) k n =
        (kR + m * C) / (nR + m) := by
  dsimp
  constructor
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    by_cases hden : (n : ℝ) + m = 0
    · simp [hden]
    · field_simp [hnR, hden]
  · simp only [paper_posterior_rating]
    congr 1 <;> ring

/-- The printed ordinal expression is the prior-inclusive formula at zero prior mass. -/
theorem paper_eq21_zero_prior_comparison
    {K : Type*} [Fintype K]
    (ratingValue observedCount : K → ℝ) :
    paper_ordinal_posterior_rating ratingValue (fun _ => 0) observedCount =
      (∑ j : K, observedCount j * ratingValue j) /
        (∑ j : K, observedCount j) := by
  simp [paper_ordinal_posterior_rating]

/-- Appendix E's corrected prior-inclusive ordinal posterior formula. -/
theorem paper_eq21_ordinal_posterior_formula
    {K : Type*} [Fintype K]
    (ratingValue priorPseudoCount observedCount : K → ℝ)
    (htotal : (∑ j : K, (priorPseudoCount j + observedCount j)) ≠ 0) :
    paper_ordinal_posterior_rating ratingValue priorPseudoCount observedCount =
      (∑ j : K, (priorPseudoCount j + observedCount j) * ratingValue j) /
        (∑ j : K, (priorPseudoCount j + observedCount j)) := by
  rfl

end MBJG25ProducerFairness
