import AppliedModelingLib.SocialChoice.Ranking.Payoff
import AppliedModelingLib.SocialChoice.Ranking.Probability
import AppliedModelingLib.SocialChoice.Ranking.Sequential
import AppliedModelingLib.SocialChoice.Ranking.Score

/-!
# Sequential Payoffs for Ranking Laws

Expected values for the best candidate in a finite feasible set.  This is the
PMF/payoff companion to `Ranking.Sequential`, which keeps the deterministic
best-in-set operations probability-free.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- Expected value of the best remaining candidate under a ranking law. -/
def expectedBestInSet {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (remaining : Finset (Candidate n)) : ℝ :=
  pmfExp μ (fun π => value (bestInSet π remaining))

/-- The value of the best remaining candidate is bounded by the total absolute
value over the finite candidate set. -/
theorem norm_value_bestInSet_le_sum_norm_value {n : ℕ}
    (value : Candidate n → ℝ) (π : Ranking n)
    (remaining : Finset (Candidate n)) :
    ‖value (bestInSet π remaining)‖ ≤ ∑ c : Candidate n, ‖value c‖ := by
  classical
  exact Finset.single_le_sum
    (fun c _ => norm_nonneg (value c))
    (Finset.mem_univ (bestInSet π remaining))

/-- Source-level best-in-set payoffs are integrable under finite measures. -/
theorem integrable_value_bestInSet_comp {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n)) :
    MeasureTheory.Integrable
      (fun ω => value (bestInSet (rank ω) remaining)) μ := by
  classical
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const
      (μ := μ) (c := ∑ c : Candidate n, ‖value c‖)) ?_ ?_
  · have hpayoff :
        Measurable (fun π : Ranking n => value (bestInSet π remaining)) :=
      measurable_of_finite _
    exact (hpayoff.comp hrank).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω =>
      norm_value_bestInSet_le_sum_norm_value value (rank ω) remaining)

/--
The expected best-in-set payoff of a ranking law induced by a source measure is
the source integral of the corresponding pointwise payoff.
-/
theorem expectedBestInSet_rankingPMFOfMeasure_eq_integral
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n)) :
    expectedBestInSet (rankingPMFOfMeasure μ rank hrank) value remaining =
      ∫ ω, value (bestInSet (rank ω) remaining) ∂μ := by
  exact rankingPMFOfMeasure_pmfExp_eq_integral μ rank hrank
    (fun π => value (bestInSet π remaining))

/--
Pointwise source domination transfers to the induced finite ranking laws'
best-in-set expectations.
-/
theorem expectedBestInSet_rankingPMFOfMeasure_le_of_forall
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (worse better : Ω → Ranking n)
    (hworse : Measurable worse) (hbetter : Measurable better)
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n))
    (hpoint :
      ∀ ω,
        value (bestInSet (worse ω) remaining) ≤
          value (bestInSet (better ω) remaining)) :
    expectedBestInSet (rankingPMFOfMeasure μ worse hworse) value remaining ≤
      expectedBestInSet (rankingPMFOfMeasure μ better hbetter) value remaining := by
  rw [expectedBestInSet_rankingPMFOfMeasure_eq_integral μ worse hworse value remaining]
  rw [expectedBestInSet_rankingPMFOfMeasure_eq_integral μ better hbetter value remaining]
  exact MeasureTheory.integral_mono
    (integrable_value_bestInSet_comp μ worse hworse value remaining)
    (integrable_value_bestInSet_comp μ better hbetter value remaining)
    hpoint

/--
Strict source domination transfers to the induced finite ranking laws'
best-in-set expectations when the strict-improvement region has positive
source measure.
-/
theorem expectedBestInSet_rankingPMFOfMeasure_lt_of_forall_le_of_measure_setOf_lt_pos
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (worse better : Ω → Ranking n)
    (hworse : Measurable worse) (hbetter : Measurable better)
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n))
    (hpoint :
      ∀ ω,
        value (bestInSet (worse ω) remaining) ≤
          value (bestInSet (better ω) remaining))
    (hstrict :
      0 < μ {ω |
        value (bestInSet (worse ω) remaining) <
          value (bestInSet (better ω) remaining)}) :
    expectedBestInSet (rankingPMFOfMeasure μ worse hworse) value remaining <
      expectedBestInSet (rankingPMFOfMeasure μ better hbetter) value remaining := by
  rw [expectedBestInSet_rankingPMFOfMeasure_eq_integral μ worse hworse value remaining]
  rw [expectedBestInSet_rankingPMFOfMeasure_eq_integral μ better hbetter value remaining]
  exact AppliedModelingLib.integral_lt_integral_of_forall_le_of_measure_setOf_lt_pos
    μ
    (integrable_value_bestInSet_comp μ worse hworse value remaining)
    (integrable_value_bestInSet_comp μ better hbetter value remaining)
    hpoint hstrict

/--
Continuous-source expectation lift of score-contraction monotonicity.

The only measure-theoretic obligations are measurability of the two ranking
maps induced by sorting raw and contracted scores.
-/
theorem expectedBestInSet_rankingPMFOfMeasure_rankByScore_le_contract
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (value : Candidate n → ℝ) (raw : Ω → Candidate n → ℝ)
    {t : ℝ}
    (hrawRank : Measurable (fun ω => rankByScore (raw ω)))
    (hcontractRank :
      Measurable (fun ω =>
        rankByScore
          (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i))))
    {remaining : Finset (Candidate n)}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    expectedBestInSet
        (rankingPMFOfMeasure μ (fun ω => rankByScore (raw ω)) hrawRank)
        value remaining ≤
      expectedBestInSet
        (rankingPMFOfMeasure μ
          (fun ω =>
            rankByScore
              (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i)))
          hcontractRank)
        value remaining :=
  expectedBestInSet_rankingPMFOfMeasure_le_of_forall μ
    (fun ω => rankByScore (raw ω))
    (fun ω =>
      rankByScore
        (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i)))
    hrawRank hcontractRank value remaining
    (fun ω =>
      value_bestInSet_le_of_rankByScore_rumContractScore
        (value := value) (raw := raw ω) ht0 htlt1 hremaining)

/--
Strict continuous-source expectation lift of score-contraction monotonicity.
The deterministic contraction lemma gives pointwise weak improvement; strict
expected improvement follows from positive source mass of strict pointwise
improvement.
-/
theorem expectedBestInSet_rankingPMFOfMeasure_rankByScore_lt_contract_of_strict_improvement_pos
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (value : Candidate n → ℝ) (raw : Ω → Candidate n → ℝ)
    {t : ℝ}
    (hrawRank : Measurable (fun ω => rankByScore (raw ω)))
    (hcontractRank :
      Measurable (fun ω =>
        rankByScore
          (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i))))
    {remaining : Finset (Candidate n)}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty)
    (hstrict :
      0 < μ {ω |
        value (bestInSet (rankByScore (raw ω)) remaining) <
          value
            (bestInSet
              (rankByScore
                (fun i =>
                  AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i)))
              remaining)}) :
    expectedBestInSet
        (rankingPMFOfMeasure μ (fun ω => rankByScore (raw ω)) hrawRank)
        value remaining <
      expectedBestInSet
        (rankingPMFOfMeasure μ
          (fun ω =>
            rankByScore
              (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i)))
          hcontractRank)
        value remaining :=
  expectedBestInSet_rankingPMFOfMeasure_lt_of_forall_le_of_measure_setOf_lt_pos μ
    (fun ω => rankByScore (raw ω))
    (fun ω =>
      rankByScore
        (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i)))
    hrawRank hcontractRank value remaining
    (fun ω =>
      value_bestInSet_le_of_rankByScore_rumContractScore
        (value := value) (raw := raw ω) ht0 htlt1 hremaining)
    hstrict

/-- Expected value of the best candidate after removing one candidate. -/
def expectedBestAfterRemoval {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (c : Candidate n) : ℝ :=
  pmfExp μ (fun π => value (bestRemainingAfter π c))

/--
Finite-source expectation lift of score-contraction monotonicity.

If both ranking laws are obtained by pushing the same finite source PMF through
raw-score sorting and contracted-score sorting, then every nonempty remaining
set has weakly higher expected top value under the contracted ranking law.
-/
theorem expectedBestInSet_map_rankByScore_le_map_contractRankByScore
    {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (value : Candidate n → ℝ) (raw : Ω → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ} (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    expectedBestInSet (μ.map (fun ω => rankByScore (raw ω))) value remaining ≤
      expectedBestInSet
        (μ.map (fun ω =>
          rankByScore
            (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw ω i))))
        value remaining := by
  rw [expectedBestInSet, expectedBestInSet, pmfExp_map, pmfExp_map]
  exact pmfExp_le_pmfExp_of_forall_le μ _ _ (fun ω =>
    value_bestInSet_le_of_rankByScore_rumContractScore
      (value := value) (raw := raw ω) ht0 htlt1 hremaining)

/-- In a three-candidate ranking law, after removing candidate `0`, the best
remaining candidate is either `1` or `2`. -/
theorem expectedBestAfterRemoval_fin3_remove0_eq_prob_mul_add
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    expectedBestAfterRemoval μ value (0 : Candidate 1) =
      pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) =
          (1 : Candidate 1)) * value (1 : Candidate 1) +
        (1 - pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) =
          (1 : Candidate 1))) * value (2 : Candidate 1) := by
  classical
  unfold expectedBestAfterRemoval
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => value (bestRemainingAfter π (0 : Candidate 1)))
    (value (1 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h]
  · have hne0 : bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

/-- In a three-candidate ranking law, after removing candidate `1`, the best
remaining candidate is either `0` or `2`. -/
theorem expectedBestAfterRemoval_fin3_remove1_eq_prob_mul_add
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    expectedBestAfterRemoval μ value (1 : Candidate 1) =
      pmfProb μ (fun π => bestRemainingAfter π (1 : Candidate 1) =
          (0 : Candidate 1)) * value (0 : Candidate 1) +
        (1 - pmfProb μ (fun π => bestRemainingAfter π (1 : Candidate 1) =
          (0 : Candidate 1))) * value (2 : Candidate 1) := by
  classical
  unfold expectedBestAfterRemoval
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (1 : Candidate 1)))
    (value (0 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne1 : bestRemainingAfter π (1 : Candidate 1) ≠ (1 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (1 : Candidate 1)
    have h2 : bestRemainingAfter π (1 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (1 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact hne1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (1 : Candidate 1)).isLt
      omega
    simp [h2]

/-- In a three-candidate ranking law, after removing candidate `2`, the best
remaining candidate is either `0` or `1`. -/
theorem expectedBestAfterRemoval_fin3_remove2_eq_prob_mul_add
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    expectedBestAfterRemoval μ value (2 : Candidate 1) =
      pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) =
          (0 : Candidate 1)) * value (0 : Candidate 1) +
        (1 - pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) =
          (0 : Candidate 1))) * value (1 : Candidate 1) := by
  classical
  unfold expectedBestAfterRemoval
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (2 : Candidate 1)))
    (value (0 : Candidate 1)) (value (1 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne2 : bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem expectedBestAfterRemoval_fin3_remove0_le_of_prob_le
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue : value (2 : Candidate 1) ≤ value (1 : Candidate 1))
    (hprob :
      pmfProb μWorse (fun π => bestRemainingAfter π (0 : Candidate 1) =
          (1 : Candidate 1)) ≤
        pmfProb μBetter (fun π => bestRemainingAfter π (0 : Candidate 1) =
          (1 : Candidate 1))) :
    expectedBestAfterRemoval μWorse value (0 : Candidate 1) ≤
      expectedBestAfterRemoval μBetter value (0 : Candidate 1) := by
  rw [expectedBestAfterRemoval_fin3_remove0_eq_prob_mul_add]
  rw [expectedBestAfterRemoval_fin3_remove0_eq_prob_mul_add]
  nlinarith

theorem expectedBestAfterRemoval_fin3_remove1_le_of_prob_le
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue : value (2 : Candidate 1) ≤ value (0 : Candidate 1))
    (hprob :
      pmfProb μWorse (fun π => bestRemainingAfter π (1 : Candidate 1) =
          (0 : Candidate 1)) ≤
        pmfProb μBetter (fun π => bestRemainingAfter π (1 : Candidate 1) =
          (0 : Candidate 1))) :
    expectedBestAfterRemoval μWorse value (1 : Candidate 1) ≤
      expectedBestAfterRemoval μBetter value (1 : Candidate 1) := by
  rw [expectedBestAfterRemoval_fin3_remove1_eq_prob_mul_add]
  rw [expectedBestAfterRemoval_fin3_remove1_eq_prob_mul_add]
  nlinarith

theorem expectedBestAfterRemoval_fin3_remove2_le_of_prob_le
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (hvalue : value (1 : Candidate 1) ≤ value (0 : Candidate 1))
    (hprob :
      pmfProb μWorse (fun π => bestRemainingAfter π (2 : Candidate 1) =
          (0 : Candidate 1)) ≤
        pmfProb μBetter (fun π => bestRemainingAfter π (2 : Candidate 1) =
          (0 : Candidate 1))) :
    expectedBestAfterRemoval μWorse value (2 : Candidate 1) ≤
      expectedBestAfterRemoval μBetter value (2 : Candidate 1) := by
  rw [expectedBestAfterRemoval_fin3_remove2_eq_prob_mul_add]
  rw [expectedBestAfterRemoval_fin3_remove2_eq_prob_mul_add]
  nlinarith

@[simp] theorem expectedBestInSet_univ {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedBestInSet μ value Finset.univ =
      expectedFirstMoverUtility μ value := by
  unfold expectedBestInSet expectedFirstMoverUtility
  exact pmfExp_congr μ (fun π => by simp)

theorem expectedBestInSet_univ_sdiff_singleton {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) :
    expectedBestInSet μ value
        (Finset.univ \ ({c} : Finset (Candidate n))) =
      expectedBestAfterRemoval μ value c := by
  unfold expectedBestInSet expectedBestAfterRemoval
  exact pmfExp_congr μ (fun π => by
    rw [bestInSet_univ_sdiff_singleton])

@[simp] theorem expectedBestInSet_singleton {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (c : Candidate n) :
    expectedBestInSet μ value ({c} : Finset (Candidate n)) =
      value c := by
  unfold expectedBestInSet
  simp [pmfExp_const]

end

end Ranking
end SocialChoice
end AppliedModelingLib
