import MBJG25ProducerFairness.MainTheorems

/-!
# Paper Interface: Prior-Weighted Rating Fairness

This is the source-facing interface for the two named fixed-model results in
*Balancing Producer Fairness and Efficiency via Prior-Weighted Rating System
Design* (Theorems 3.1 and 3.2). The source model runs over a discrete,
nondegenerate review horizon. `paper_fixed_binary_model_formulaSpec` makes
that domain explicit before the two theorem targets use its formulas.
-/

namespace MBJG25ProducerFairness

open scoped BigOperators

/-! ## Fixed binary-rating model -/

/-- The conditional expectation of the posterior mean after a fixed number of reviews. -/
noncomputable def paper_expected_posterior_mean
    (alpha beta eta : ℝ) (t : ℕ) (q : ℝ) : ℝ :=
  (eta * alpha + (t : ℝ) * q) / (eta * alpha + eta * beta + (t : ℝ))

/-- Conditional bias of the posterior-mean estimator after `t` fixed reviews. -/
noncomputable def paper_conditional_bias
    (alpha beta eta : ℝ) (t : ℕ) (q : ℝ) : ℝ :=
  paper_expected_posterior_mean alpha beta eta t q - q

/-- Conditional variance of the posterior-mean estimator after `t` fixed reviews. -/
noncomputable def paper_conditional_variance
    (alpha beta eta : ℝ) (t : ℕ) (q : ℝ) : ℝ :=
  (t : ℝ) * q * (1 - q) / (eta * alpha + eta * beta + (t : ℝ)) ^ 2

/-- Squared conditional bias of the posterior-mean estimator after `t` fixed reviews. -/
noncomputable def paper_conditional_squared_bias
    (alpha beta eta : ℝ) (t : ℕ) (q : ℝ) : ℝ :=
  paper_conditional_bias alpha beta eta t q ^ 2

/--
The source's fixed Beta--Bernoulli formula family on its discrete,
nondegenerate review domain. The random posterior estimator in Equation (1)
is summarized here by its conditional expectation, exactly as Appendix A does
when it defines conditional bias and variance.
-/
def paper_fixed_binary_model_formulaSpec
    {alpha beta eta q : ℝ} {t : ℕ}
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (heta : 0 ≤ eta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : Prop :=
  paper_expected_posterior_mean alpha beta eta t q =
      (eta * alpha + (t : ℝ) * q) /
        (eta * alpha + eta * beta + (t : ℝ)) ∧
    paper_conditional_bias alpha beta eta t q =
      paper_expected_posterior_mean alpha beta eta t q - q ∧
    paper_conditional_variance alpha beta eta t q =
      (t : ℝ) * q * (1 - q) /
        (eta * alpha + eta * beta + (t : ℝ)) ^ 2 ∧
    paper_conditional_squared_bias alpha beta eta t q =
      paper_conditional_bias alpha beta eta t q ^ 2

/-! ## Theorem 3.1 -/

/--
Theorem 3.1 with the source-model Beta-shape and positive-time conditions
made explicit. The source's strict variance wording has the standard Bernoulli
endpoint qualification: variance is weakly decreasing on `0 ≤ q ≤ 1`, and
strictly decreasing for `0 < q < 1` when prior strength strictly increases.
-/
def paper_theorem3_1Spec
    {alpha beta q etaLow etaHigh : ℝ} {t : ℕ}
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hetaLow : 0 ≤ etaLow)
    (hetaOrder : etaLow ≤ etaHigh) : Prop :=
  paper_conditional_squared_bias alpha beta etaLow t q ≤
      paper_conditional_squared_bias alpha beta etaHigh t q ∧
    paper_conditional_variance alpha beta etaHigh t q ≤
      paper_conditional_variance alpha beta etaLow t q ∧
    (0 < q → q < 1 → etaLow < etaHigh →
      paper_conditional_variance alpha beta etaHigh t q <
        paper_conditional_variance alpha beta etaLow t q)

/-! ## Theorem 3.2 -/

/--
Theorem 3.2 on the source model's true-quality domain `0 ≤ q ≤ 1`.
Convexity and concavity are written directly as the two-point inequalities, so
the source domain and every theorem conclusion are visible in one bounded
review target.
-/
def paper_theorem3_2Spec
    {alpha beta eta : ℝ} {t : ℕ}
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (heta : 0 ≤ eta)
    (ht : 0 < t) : Prop :=
  (∀ x y lam : ℝ,
      0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ lam → lam ≤ 1 →
        paper_conditional_squared_bias alpha beta eta t (lam * x + (1 - lam) * y) ≤
          lam * paper_conditional_squared_bias alpha beta eta t x +
            (1 - lam) * paper_conditional_squared_bias alpha beta eta t y) ∧
  (0 ≤ alpha / (alpha + beta) ∧ alpha / (alpha + beta) ≤ 1 ∧
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paper_conditional_squared_bias alpha beta eta t (alpha / (alpha + beta)) ≤
        paper_conditional_squared_bias alpha beta eta t q) ∧
  (∀ x y lam : ℝ,
      0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ lam → lam ≤ 1 →
        lam * paper_conditional_variance alpha beta eta t x +
          (1 - lam) * paper_conditional_variance alpha beta eta t y ≤
            paper_conditional_variance alpha beta eta t (lam * x + (1 - lam) * y)) ∧
  ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
    paper_conditional_variance alpha beta eta t q ≤
      paper_conditional_variance alpha beta eta t (1 / 2)

/-! ## Supplementary correction support -/

/-- The binary posterior-rating formula used to check Appendix D's Equation 20. -/
noncomputable def paper_posterior_rating
    (alphaHat betaHat : ℝ) (positiveRatings totalRatings : ℕ) : ℝ :=
  (alphaHat + positiveRatings) / (alphaHat + betaHat + totalRatings)

/-- The prior-inclusive ordinal posterior mean used to check Appendix E's Equation 21. -/
noncomputable def paper_ordinal_posterior_rating
    {K : Type*} [Fintype K]
  (ratingValue priorPseudoCount observedCount : K → ℝ) : ℝ :=
  (∑ j : K, (priorPseudoCount j + observedCount j) * ratingValue j) /
    (∑ j : K, (priorPseudoCount j + observedCount j))

end MBJG25ProducerFairness
