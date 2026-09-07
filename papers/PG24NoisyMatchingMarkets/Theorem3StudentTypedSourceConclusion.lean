import PG24NoisyMatchingMarkets.Theorem3ActualProof
import PG24NoisyMatchingMarkets.Theorem4StudentTypedSourceAdapter

/-!
# PG24 Theorem 3 Student-Typed Source Conclusion

This transports the checked finite-cutoff attenuation theorem to literal
extended-model data.  Preferences factor through the source student state and
the reported coalition subset is carried on the actual global-college type.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

namespace PG24StudentTypedSourceStableData

/--
Theorem 3 for literal source data with student-typed preferences.  The
underlying cutoff-vector result is applied only to the selected coalition
cutoffs; both endpoint probabilities are then reported through containment
checked actual-coalition subsets.
-/
theorem theorem3_studentTyped_source_coalition_attenuation_of_iid_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ (StudentType : Type u) [MeasurableSpace StudentType]
        (Outcome : Type v) [MeasurableSpace Outcome]
        (GlobalCollege : Type w) [Fintype GlobalCollege]
        (Cutoff : Type x)
        {eta : Measure ℝ} {totalSupply : ℝ}
        (data :
          PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
            StudentType Outcome GlobalCollege Cutoff),
        ∃ threshold : ℝ,
        ∃ actualCoalition : Finset GlobalCollege,
        ∃ actualLargeSubset :
          Theorem4ActualCoalitionSubset data.coalitionEmbedding,
          actualCoalition = theorem4ActualCoalition data.coalitionEmbedding ∧
            CoalitionLargeSubset actualCoalition actualLargeSubset.actualSubset epsilon ∧
            (∀ value : ℝ, value < threshold - epsilon →
              data.pMuOnActualCoalitionSubset value actualLargeSubset < epsilon) ∧
            (∀ value : ℝ, threshold + epsilon < value →
              1 - epsilon <
                data.pMuOnActualCoalitionSubset value
                  (Theorem4ActualCoalitionSubset.ofIndexed
                    data.coalitionEmbedding Finset.univ)) := by
  have hcutoff := theorem3_attenuation_in_coalitions_of_iid_beta
    noiseLaw hbeta hvariance hepsilon
  filter_upwards [hcutoff] with C hcutoffC StudentType _ Outcome _
      GlobalCollege _ Cutoff eta totalSupply data
  let inst := data.toLiteralSourceStableData.toExtendedCoalitionSourceStableInstance
  rcases hcutoffC inst.localCutoff with
    ⟨threshold, indexedLargeSubset, hlarge, hlow, hhigh⟩
  refine ⟨threshold, theorem4ActualCoalition data.coalitionEmbedding,
    Theorem4ActualCoalitionSubset.ofIndexed data.coalitionEmbedding
      indexedLargeSubset, rfl, ?_, ?_, ?_⟩
  · simpa [Theorem4ActualCoalitionSubset.ofIndexed, theorem4ActualCoalition]
      using
        (coalitionLargeSubset_embedded_of_indexed data.coalitionEmbedding
          indexedLargeSubset hlarge)
  · intro value hvalue
    rw [pMuOnActualCoalitionSubset_ofIndexed_eq_indexed]
    simpa [inst, PG24ExtendedCoalitionSourceStableInstance.pMu] using
      hlow value hvalue
  · intro value hvalue
    rw [pMuOnActualCoalitionSubset_ofIndexed_eq_indexed]
    simpa [inst, PG24ExtendedCoalitionSourceStableInstance.pMu] using
      hhigh value hvalue

/--
Threshold form of the source-typed Theorem 3 conclusion.  The numerical
threshold is chosen before the arbitrary source state and broader market, and
the strict coalition-size condition is stated on the actual carrier.
-/
theorem theorem3_studentTyped_source_coalition_attenuation_threshold_of_iid_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
      ∀ (StudentType : Type u) [MeasurableSpace StudentType]
        (Outcome : Type v) [MeasurableSpace Outcome]
        (GlobalCollege : Type w) [Fintype GlobalCollege]
        (Cutoff : Type x)
        {eta : Measure ℝ} {totalSupply : ℝ}
        (data :
          PG24StudentTypedSourceStableData C noiseLaw eta totalSupply
            StudentType Outcome GlobalCollege Cutoff),
        ∃ threshold : ℝ,
        ∃ actualCoalition : Finset GlobalCollege,
        ∃ actualLargeSubset :
          Theorem4ActualCoalitionSubset data.coalitionEmbedding,
          actualCoalition = theorem4ActualCoalition data.coalitionEmbedding ∧
            N < actualCoalition.card ∧
            CoalitionLargeSubset actualCoalition actualLargeSubset.actualSubset epsilon ∧
            (∀ value : ℝ, value < threshold - epsilon →
              data.pMuOnActualCoalitionSubset value actualLargeSubset < epsilon) ∧
            (∀ value : ℝ, threshold + epsilon < value →
              1 - epsilon <
                data.pMuOnActualCoalitionSubset value
                  (Theorem4ActualCoalitionSubset.ofIndexed
                    data.coalitionEmbedding Finset.univ)) := by
  rcases Filter.eventually_atTop.1
      (theorem3_studentTyped_source_coalition_attenuation_of_iid_beta
        noiseLaw hbeta hvariance hepsilon) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hthreshold StudentType _ Outcome _ GlobalCollege _ Cutoff eta totalSupply data
  rcases hN C hthreshold StudentType Outcome GlobalCollege Cutoff data with
    ⟨threshold, actualCoalition, actualLargeSubset, hcoalition, hlarge,
      hlow, hhigh⟩
  refine ⟨threshold, actualCoalition, actualLargeSubset, hcoalition, ?_,
    hlarge, hlow, hhigh⟩
  rw [hcoalition]
  exact theorem4EmbeddedCoalition_card_gt_of_threshold_le
    data.coalitionEmbedding hthreshold

end PG24StudentTypedSourceStableData

end

end PG24NoisyMatchingMarkets
