import AppliedModelingLib.Foundations.Probability.OrderStatistics

/-!
# PRPKG Definition 3 IID Source Bridge

Definition 3 defines `mu_D(i, a)` from the `i`-th order statistic of `a`
independent draws from one base distribution `D`.  The generic
`expectedOrderStatisticMeanSeq` interface permits an unrelated sample law for
each cardinality; this module records the literal iid specialization used by
the paper.

The expectation identities derive the finite family of order-statistic
integrability obligations from the source's finite-mean condition. Probability
normalization alone would not suffice.
-/

open MeasureTheory
open scoped BigOperators

namespace PRPKG24AccuracyDiversity

noncomputable section

/-- The law of `a` independent draws from the source base distribution `D`. -/
def definition3IidSampleMeasure (D : Measure ℝ) (a : ℕ) : Measure (Fin a → ℝ) :=
  Measure.pi (fun _ : Fin a => D)

/--
The source's bottom-indexed expected order-statistic table `mu_D(i, a)`,
formed from `a` iid draws from one common base distribution `D`.
-/
def definition3IidOrderStatisticMean (D : Measure ℝ) : ℕ → ℕ → ℝ :=
  AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq
    (definition3IidSampleMeasure D)

/-- A finite iid sample of a probability law is again a probability law. -/
theorem definition3IidSampleMeasure_isProbabilityMeasure
    (D : Measure ℝ) [IsProbabilityMeasure D] (a : ℕ) :
    IsProbabilityMeasure (definition3IidSampleMeasure D a) := by
  dsimp [definition3IidSampleMeasure]
  infer_instance

/-- A finite order statistic is bounded in absolute value by all sample norms. -/
private theorem sampleOrderStatisticValue_norm_le_sum_norm
    {a : ℕ} (sample : Fin a → ℝ) (rank : ℕ) :
    ‖AppliedModelingLib.Probability.sampleOrderStatisticValue sample rank‖ ≤
      ∑ i : Fin a, ‖sample i‖ := by
  classical
  by_cases hrank : 0 < rank ∧ rank ≤ a
  · rw [AppliedModelingLib.Probability.sampleOrderStatisticValue, dif_pos hrank]
    change ‖sample (Tuple.sort sample ⟨rank - 1, by omega⟩)‖ ≤
      ∑ i : Fin a, ‖sample i‖
    exact Finset.single_le_sum
      (fun i _ => norm_nonneg (sample i)) (Finset.mem_univ _)
  · simp [AppliedModelingLib.Probability.sampleOrderStatisticValue, hrank,
      Finset.sum_nonneg]

/--
A finite iid sample from an integrable base law has integrable valid and
out-of-range order-statistic values.  This is the finite-mean obligation
implicit in the source's Definition 3.
-/
theorem definition3Iid_sampleOrderStatisticValue_integrable
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (a rank : ℕ) :
    Integrable
      (fun sample : Fin a → ℝ =>
        AppliedModelingLib.Probability.sampleOrderStatisticValue sample rank)
      (definition3IidSampleMeasure D a) := by
  have hsum_integrable :
      Integrable (fun sample : Fin a → ℝ => ∑ i : Fin a, ‖sample i‖)
        (definition3IidSampleMeasure D a) := by
    change Integrable (fun sample : Fin a → ℝ => ∑ i : Fin a, ‖sample i‖)
      (Measure.pi (fun _ : Fin a => D))
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro i _hi
    exact (MeasureTheory.integrable_eval hfinite_mean).norm
  refine hsum_integrable.mono'
    (AppliedModelingLib.Probability.sampleOrderStatisticValue_measurable rank).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall
    (fun sample => sampleOrderStatisticValue_norm_le_sum_norm sample rank)

/-- Every order statistic used by a finite iid top-`k` sum is integrable. -/
theorem definition3Iid_topKRange_orderStatistic_integrable
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (k a : ℕ) :
    ∀ i ∈ Finset.range (min k a),
      Integrable
        (fun sample : Fin a → ℝ =>
          AppliedModelingLib.Probability.sampleOrderStatisticValue sample (a - i))
        (definition3IidSampleMeasure D a) := by
  intro i _hi
  exact definition3Iid_sampleOrderStatisticValue_integrable
    D hfinite_mean a (a - i)

/--
Literal iid form of Definition 3 / Proposition 5's top-`k` identity.

The left side is the sum of the expected upper order statistics of `a` iid
draws from `D`; the right side is the expectation of their realized top-`k`
sum.  Integrability is stated rank-by-rank because it is the exact condition
needed to exchange the finite sum and expectation.
-/
theorem definition3_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (k a : ℕ) :
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (definition3IidOrderStatisticMean D) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure D a) k := by
  simpa [definition3IidOrderStatisticMean] using
    AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
      (definition3IidSampleMeasure D) k a
      (definition3Iid_topKRange_orderStatistic_integrable D hfinite_mean k a)

/--
The Proposition 5 spelling of the same iid order-statistic identity.

Keeping this as a theorem rather than an abbreviation ensures that either
source anchor reaches the same explicit iid law and integrability obligations.
-/
theorem proposition5_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (k a : ℕ) :
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (definition3IidOrderStatisticMean D) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure D a) k :=
  definition3_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
    D hfinite_mean k a

end

end PRPKG24AccuracyDiversity
