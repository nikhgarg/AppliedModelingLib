import PRPKG24AccuracyDiversity.Pareto

namespace PRPKG24AccuracyDiversity

/--
Source Lemma D.4's fixed-rank value asymptotic for the concrete scale-one iid
Pareto law.  The bottom-indexed rank `q - r` is valid eventually, so the
concrete order-statistic mean agrees with the gamma-ratio sequence on a tail.
-/
theorem lemmaD4_pareto_iid_fixed_rank_value_asymptoticEquivalent
    {alpha : ℝ} (halpha : 1 < alpha) (r : ℕ) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q - r) q)
      (fun q : ℕ =>
        paretoRankValueCoeff alpha r * ((q : ℝ) ^ (1 / alpha))) := by
  refine AppliedModelingLib.Math.AsymptoticEquivalent.congr_left_eventually ?_
    (paretoRankGammaRatioMean_value_asymptoticEquivalent halpha r)
  filter_upwards [Filter.eventually_atTop.2 ⟨r + 1, fun q hq => hq⟩] with q hq
  have hrq : r < q := by omega
  exact paretoIidSampleMeasure_rank_eq_rankGammaRatio halpha hrq

/--
The concrete iid Pareto fixed-rank means have strictly decreasing forward
marginals once the bottom-indexed rank is valid.  The eventual qualifier is
essential because the totalized order-statistic interface also has invalid
small ranks.
-/
theorem lemmaD4_pareto_iid_fixed_rank_forward_marginal_strict_antitone_eventually
    {alpha : ℝ} (halpha : 1 < alpha) (r : ℕ) :
    ∀ᶠ q in Filter.atTop,
      expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 2 - r) (q + 2) -
          expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 1 - r) (q + 1) <
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 1 - r) (q + 1) -
          expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q - r) q := by
  filter_upwards [Filter.eventually_atTop.2 ⟨r + 1, fun q hq => hq⟩] with q hq
  have hrq : r < q := by omega
  have hrq_succ : r < q + 1 := by omega
  have hrq_succ_succ : r < q + 2 := by omega
  rw [paretoIidSampleMeasure_rank_eq_rankGammaRatio halpha hrq_succ_succ,
    paretoIidSampleMeasure_rank_eq_rankGammaRatio halpha hrq_succ,
    paretoIidSampleMeasure_rank_eq_rankGammaRatio halpha hrq]
  exact paretoRankGammaRatioMean_forward_marginal_strict_antitone halpha r q

end PRPKG24AccuracyDiversity
