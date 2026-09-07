import AppliedModelingLib.Applications.RatingSystems.BinaryRating

/-!
# Paper-Facing Theorems: Balancing Producer Fairness and Efficiency

This file records the checked theorem endpoints for the prior-weighted
rating-system paper. The source's strict-variance clause in Theorem 3.1 has a
minor endpoint slip: Lean proves the full closed-interval weak statement, the
strict interior statement, and the two endpoint counterexamples. This is a
formalized source correction, not a remaining proof caveat.
-/

namespace MBJG25ProducerFairness

/--
Correct weak version of Theorem 3.1's variance-decrease clause.

Across the full Bernoulli quality interval `0 ≤ q_v ≤ 1`, increasing prior
strength weakly decreases the posterior-mean variance term.
-/
theorem paper_theorem3_1_variance_weak_decrease
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaHigh t q ≤
      AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaLow t q := by
  exact AppliedModelingLib.Statistics.priorWeightedVariance_weak_decrease
    hshape ht hq0 hq1 hetaLow_nonneg heta_le

/--
Corrected interior-quality version of the strict variance-decrease clause of
Theorem 3.1.

The paper-facing statement is intentionally close to the theorem claim: in the
binary-rating posterior mean model, increasing prior strength strictly decreases
the variance term when true quality is interior, the review count is positive,
the prior-shape total mass is positive, and the lower prior strength is
nonnegative.
-/
theorem paper_theorem3_1_variance_strict_decrease_interior
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaHigh t q <
      AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaLow t q := by
  exact AppliedModelingLib.Statistics.priorWeightedVariance_strict_decrease_of_interior_quality
    hshape ht hq0 hq1 hetaLow_nonneg heta_lt

/--
Theorem 3.1, squared-bias clause.

For the fixed binary-rating model, squared posterior-mean bias is nondecreasing
as prior strength increases.
-/
theorem paper_theorem3_1_squared_bias_nondecreasing
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    AppliedModelingLib.Statistics.priorWeightedSquaredBias alpha beta etaLow t q ≤
      AppliedModelingLib.Statistics.priorWeightedSquaredBias alpha beta etaHigh t q := by
  exact AppliedModelingLib.Statistics.priorWeightedSquaredBias_mono
    hshape ht hetaLow_nonneg heta_le

/--
Theorem 3.2, squared-bias convexity clause.

As a function of true quality, squared posterior-mean bias is Jensen-convex.
-/
theorem paper_theorem3_2_squared_bias_convex_in_quality
    {alpha beta eta t : ℝ}
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    AppliedModelingLib.Statistics.JensenConvex
      (fun q => AppliedModelingLib.Statistics.priorWeightedSquaredBias
        alpha beta eta t q) := by
  exact AppliedModelingLib.Statistics.priorWeightedSquaredBias_jensenConvex_quality
    hden

/--
Theorem 3.2, squared-bias minimizer clause.

As a function of true quality, squared posterior-mean bias has a global minimum
at the prior mean `alpha / (alpha + beta)`.
-/
theorem paper_theorem3_2_squared_bias_global_min_at_prior_mean
    {alpha beta eta t : ℝ}
    (hshape : 0 < alpha + beta)
    (heta_nonneg : 0 ≤ eta)
    (ht : 0 < t) :
    AppliedModelingLib.Statistics.GlobalMinAt
      (fun q => AppliedModelingLib.Statistics.priorWeightedSquaredBias
        alpha beta eta t q)
      (alpha / (alpha + beta)) := by
  have hden_pos : 0 < eta * alpha + eta * beta + t := by
    calc
      0 < eta * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg heta_nonneg hshape.le) ht
      _ = eta * alpha + eta * beta + t := by ring
  exact AppliedModelingLib.Statistics.priorWeightedSquaredBias_globalMin_priorMean
    (hshape := ne_of_gt hshape)
    (hden := ne_of_gt hden_pos)

/--
Theorem 3.2, variance concavity clause.

As a function of true quality, posterior-mean variance is Jensen-concave.
-/
theorem paper_theorem3_2_variance_concave_in_quality
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    AppliedModelingLib.Statistics.JensenConcave
      (fun q => AppliedModelingLib.Statistics.priorWeightedVariance
        alpha beta eta t q) := by
  exact AppliedModelingLib.Statistics.priorWeightedVariance_jensenConcave_quality ht

/--
Theorem 3.2, variance maximizer clause.

As a function of true quality, posterior-mean variance has a global maximum at
`1/2`.
-/
theorem paper_theorem3_2_variance_global_max_at_half
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    AppliedModelingLib.Statistics.GlobalMaxAt
      (fun q => AppliedModelingLib.Statistics.priorWeightedVariance
        alpha beta eta t q)
      (1 / 2) := by
  exact AppliedModelingLib.Statistics.priorWeightedVariance_globalMax_half ht

/--
Boundary counterexample to the strict variance-decrease clause of Theorem 3.1.

At true quality `q_v = 0`, the Bernoulli variance term is zero for every prior
strength, so the variance cannot be strictly decreasing as prior strength
increases.
-/
theorem paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaHigh t 0 <
      AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaLow t 0 := by
  exact AppliedModelingLib.Statistics.not_strictly_decreasing_priorWeightedVariance_quality_zero
    alpha beta t etaLow etaHigh

/--
Boundary counterexample to the strict variance-decrease clause of Theorem 3.1.

At true quality `q_v = 1`, the Bernoulli variance term is zero for every prior
strength, so the variance cannot be strictly decreasing as prior strength
increases.
-/
theorem paper_theorem3_1_variance_strict_decrease_counterexample_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaHigh t 1 <
      AppliedModelingLib.Statistics.priorWeightedVariance alpha beta etaLow t 1 := by
  exact AppliedModelingLib.Statistics.not_strictly_decreasing_priorWeightedVariance_quality_one
    alpha beta t etaLow etaHigh

end MBJG25ProducerFairness
