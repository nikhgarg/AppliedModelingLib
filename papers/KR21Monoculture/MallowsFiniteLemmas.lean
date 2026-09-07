import AppliedModelingLib.Foundations.Math.PositiveDenominator
import AppliedModelingLib.SocialChoice.Ranking.MallowsPayoff
import KR21Monoculture.MallowsCenterCertificate

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
Unnormalised first-choice fiber gap mass.

This is the Mallows-weight numerator corresponding to
`firstChoiceGapMass M.law value c`.  Keeping this numerator explicit lets the
main theorem use finite Mallows sum inequalities without imposing false
candidatewise sign assumptions.
-/
noncomputable def firstChoiceGapWeight
    (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  (M.toShared).firstChoiceGapWeight value c

/-- First-choice gap mass reduces to an unnormalised Mallows-weight numerator. -/
theorem firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition
    (value : Candidate n → ℝ) (c : Candidate n) :
    firstChoiceGapMass M.law value c =
      M.firstChoiceGapWeight value c / M.partition := by
  simpa [firstChoiceGapWeight,
    firstChoiceGapMass, AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using
    (M.toShared).firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition
      value c

/-- First-choice miss probability with the positive Mallows denominator exposed. -/
theorem firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition
    (c : Candidate n) :
    firstChoiceMissProb M.law c =
      (M.partition - M.firstWeight c) / M.partition := by
  simpa [firstChoiceMissProb,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb] using
    (M.toShared).firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition
      c

/--
The independent-reranking candidate sum with all positive Mallows denominators
cleared.
-/
theorem firstChoice_miss_gap_sum_eq_weight_sum_div
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c) =
      (∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight value c) /
        (M.partition * M.partition) := by
  simpa [firstChoiceGapWeight,
    firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoiceGapMass, AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using
    (M.toShared).firstChoice_miss_gap_sum_eq_weight_sum_div value

/-- Positive cleared finite Mallows sum implies positive independent-reranking sum. -/
theorem firstChoice_miss_gap_sum_pos_of_weight_sum_pos
    {value : Candidate n → ℝ}
    (hsum :
      0 < ∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight value c) :
    0 < ∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c := by
  simpa [firstChoiceGapWeight,
    firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoiceGapMass, AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using
    (M.toShared).firstChoice_miss_gap_sum_pos_of_weight_sum_pos
      (value := value) hsum

/-- Positivity of the normalized first-choice sum is equivalent to its cleared form. -/
theorem firstChoice_miss_gap_sum_pos_iff_weight_sum_pos
    (value : Candidate n → ℝ) :
    (0 < ∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c) ↔
      0 < ∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight value c := by
  simpa [firstChoiceGapWeight,
    firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoiceGapMass, AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using
    (M.toShared).firstChoice_miss_gap_sum_pos_iff_weight_sum_pos value

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/--
Cross-multiplied first-choice weight comparisons imply normalized first-choice
probability comparisons.  This is the algebraic form usually easiest to obtain
from finite Mallows sums, because the positive partition functions have been
cleared.
-/
theorem firstWeight_div_le_of_cross_mul_le
    (c : Candidate n)
    (hcross :
      C.human.firstWeight c * C.algorithm.partition ≤
        C.algorithm.firstWeight c * C.human.partition) :
    C.human.firstWeight c / C.human.partition ≤
      C.algorithm.firstWeight c / C.algorithm.partition :=
   AppliedModelingLib.PositiveDenominator.div_le_div_of_cross_mul_le
    C.human.partition_pos C.algorithm.partition_pos hcross

/--
Strict cross-multiplied center-weight improvement implies strict normalized
center first-choice improvement.
-/
theorem centerFirstWeight_div_lt_of_cross_mul_lt
    (hcross :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition) :
    C.human.firstWeight C.human.centerFirst / C.human.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst / C.algorithm.partition :=
   AppliedModelingLib.PositiveDenominator.div_lt_div_of_cross_mul_lt
    C.human.partition_pos C.algorithm.partition_pos hcross

/--
Cross-multiplied first-choice weight differences imply the normalized
weaker-competition product sign.  This form keeps the sign on the whole product,
which is necessary because non-center candidates need not have either factor
nonnegative by itself.
-/
theorem collisionDiff_mul_gap_nonneg_of_cross_mul_gap_nonneg
    (value : Candidate n → ℝ) (c : Candidate n)
    (hcross : 0 ≤
      (C.algorithm.firstWeight c * C.human.partition -
        C.human.firstWeight c * C.algorithm.partition) *
          firstChoiceGapMass C.human.law value c) :
    0 ≤ firstChoiceCollisionDiff C.algorithm.law C.human.law c *
      firstChoiceGapMass C.human.law value c := by
  have halg :
      AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb C.algorithm.law c =
        C.algorithm.firstWeight c / C.algorithm.partition := by
    simpa [firstChoiceProb] using
      C.algorithm.firstChoiceProb_eq_firstWeight_div_partition c
  have hhuman :
      AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb C.human.law c =
        C.human.firstWeight c / C.human.partition := by
    simpa [firstChoiceProb] using
      C.human.firstChoiceProb_eq_firstWeight_div_partition c
  unfold firstChoiceCollisionDiff
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceCollisionDiff
  rw [halg, hhuman]
  exact AppliedModelingLib.PositiveDenominator.sub_div_mul_nonneg_of_cross_sub_mul_nonneg
    C.algorithm.partition_pos C.human.partition_pos hcross

/--
The weaker-competition candidate sum with all positive Mallows denominators
cleared.
-/
theorem firstChoice_collision_gap_sum_eq_cross_weight_sum_div
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c) =
      (∑ c : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          C.human.firstChoiceGapWeight value c) /
        (C.algorithm.partition * C.human.partition * C.human.partition) := by
  classical
  calc
    ∑ c : Candidate n,
      firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c
        = ∑ c : Candidate n,
            ((C.algorithm.firstWeight c * C.human.partition -
                C.human.firstWeight c * C.algorithm.partition) *
              C.human.firstChoiceGapWeight value c) /
              (C.algorithm.partition * C.human.partition *
                C.human.partition) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          have halg :
              AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb C.algorithm.law c =
                C.algorithm.firstWeight c / C.algorithm.partition := by
            simpa [firstChoiceProb] using
              C.algorithm.firstChoiceProb_eq_firstWeight_div_partition c
          have hhuman :
              AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb C.human.law c =
                C.human.firstWeight c / C.human.partition := by
            simpa [firstChoiceProb] using
              C.human.firstChoiceProb_eq_firstWeight_div_partition c
          unfold firstChoiceCollisionDiff
            AppliedModelingLib.SocialChoice.Ranking.firstChoiceCollisionDiff
          rw [halg, hhuman]
          rw [C.human.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition value c]
          field_simp [C.algorithm.partition_ne_zero, C.human.partition_ne_zero]
    _ = (∑ c : Candidate n,
          (C.algorithm.firstWeight c * C.human.partition -
              C.human.firstWeight c * C.algorithm.partition) *
            C.human.firstChoiceGapWeight value c) /
        (C.algorithm.partition * C.human.partition * C.human.partition) := by
          rw [Finset.sum_div]

/--
Positive cleared finite Mallows cross-weight sum implies the positive
weaker-competition candidate sum.
-/
theorem firstChoice_collision_gap_sum_pos_of_cross_weight_sum_pos
    {value : Candidate n → ℝ}
    (hsum :
      0 < ∑ c : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          C.human.firstChoiceGapWeight value c) :
    0 < ∑ c : Candidate n,
      firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c := by
  rw [C.firstChoice_collision_gap_sum_eq_cross_weight_sum_div value]
  exact div_pos hsum
    (mul_pos (mul_pos C.algorithm.partition_pos C.human.partition_pos)
      C.human.partition_pos)

/-- Positivity of the normalized weaker-competition sum is equivalent to its cleared form. -/
theorem firstChoice_collision_gap_sum_pos_iff_cross_weight_sum_pos
    (value : Candidate n → ℝ) :
    (0 < ∑ c : Candidate n,
      firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c) ↔
      0 < ∑ c : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          C.human.firstChoiceGapWeight value c := by
  rw [C.firstChoice_collision_gap_sum_eq_cross_weight_sum_div value]
  constructor
  · intro h
    by_contra hnot
    have hsum_nonpos :
        (∑ c : Candidate n,
          (C.algorithm.firstWeight c * C.human.partition -
              C.human.firstWeight c * C.algorithm.partition) *
            C.human.firstChoiceGapWeight value c) ≤ 0 := le_of_not_gt hnot
    have hden_nonneg :
        0 ≤ C.algorithm.partition * C.human.partition * C.human.partition :=
      le_of_lt
        (mul_pos
          (mul_pos C.algorithm.partition_pos C.human.partition_pos)
          C.human.partition_pos)
    have hdiv_nonpos :
        (∑ c : Candidate n,
          (C.algorithm.firstWeight c * C.human.partition -
              C.human.firstWeight c * C.algorithm.partition) *
            C.human.firstChoiceGapWeight value c) /
          (C.algorithm.partition * C.human.partition *
            C.human.partition) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hsum_nonpos hden_nonneg
    linarith
  · intro h
    exact div_pos h
      (mul_pos
        (mul_pos C.algorithm.partition_pos C.human.partition_pos)
        C.human.partition_pos)

/--
Sum-level finite Mallows certificate.

This is the preferred paper-facing target: the finite inequalities are stated
after clearing the positive Mallows partition denominators, but no candidatewise
sign assumption is imposed.  Non-center first-choice fibers may have negative
gap mass, so the theorem should be driven by these total finite sums.
-/
structure CenterMallowsFiniteSumCertificate
    (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_weight_sum_pos :
    0 < ∑ c : Candidate n,
      (C.algorithm.partition - C.algorithm.firstWeight c) *
        C.algorithm.firstChoiceGapWeight value c
  human_weight_sum_pos :
    0 < ∑ c : Candidate n,
      (C.human.partition - C.human.firstWeight c) *
        C.human.firstChoiceGapWeight value c
  weaker_cross_weight_sum_pos :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c

/--
Cleared sum-level Mallows inequalities instantiate the candidate-sum certificate
used by the monoculture model.
-/
theorem candidateSumCertificate_of_centerMallowsFiniteSumCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsFiniteSumCertificate value) :
    C.CandidateSumCertificate value := by
  constructor
  · exact C.algorithm.firstChoice_miss_gap_sum_pos_of_weight_sum_pos
      cert.algorithm_weight_sum_pos
  · exact C.human.firstChoice_miss_gap_sum_pos_of_weight_sum_pos
      cert.human_weight_sum_pos
  · exact C.firstChoice_collision_gap_sum_pos_of_cross_weight_sum_pos
      cert.weaker_cross_weight_sum_pos

/--
The normalized candidate-sum certificate is equivalent to the cleared finite
Mallows sum certificate, once the strict center ordering hypothesis is supplied.
-/
theorem centerMallowsFiniteSumCertificate_of_candidateSumCertificate
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (cert : C.CandidateSumCertificate value) :
    C.CenterMallowsFiniteSumCertificate value := by
  constructor
  · exact hstrict
  · exact (C.algorithm.firstChoice_miss_gap_sum_pos_iff_weight_sum_pos value).mp
      cert.algorithm_firstChoiceSum_pos
  · exact (C.human.firstChoice_miss_gap_sum_pos_iff_weight_sum_pos value).mp
      cert.human_firstChoiceSum_pos
  · exact (C.firstChoice_collision_gap_sum_pos_iff_cross_weight_sum_pos value).mp
      cert.weaker_competition_firstChoiceSum_pos

/--
Paper-facing finite-sum Mallows theorem for the monoculture formalization.

The assumptions are exactly positive denominator-cleared finite Mallows sums for
the two independent-reranking preferences and the weaker-competition preference.
-/
theorem theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsFiniteSumCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_candidateSumCertificate
    (C.candidateSumCertificate_of_centerMallowsFiniteSumCertificate cert)

/--
The strong finite Mallows inequality certificate with partition denominators
cleared.

This is useful as a convenience bridge for normalized first-weight comparisons.
The sharper paper-facing target below records weaker-competition signs directly
as products.
-/
structure CenterMallowsCrossWeightCertificate (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_gap_nonneg :
    ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.algorithm.law value c
  human_gap_nonneg :
    ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.human.law value c
  collision_firstWeight_cross_le :
    ∀ c : Candidate n,
      C.human.firstWeight c * C.algorithm.partition ≤
        C.algorithm.firstWeight c * C.human.partition
  center_firstWeight_cross_lt :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition

/--
Cleared-denominator Mallows inequalities instantiate the normalized weight
certificate used by the main Mallows route.
-/
theorem centerMallowsWeightCertificate_of_crossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsCrossWeightCertificate value) :
    C.CenterMallowsWeightCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · exact cert.algorithm_gap_nonneg
  · exact cert.human_gap_nonneg
  · intro c
    exact C.firstWeight_div_le_of_cross_mul_le c
      (cert.collision_firstWeight_cross_le c)
  · exact C.centerFirstWeight_div_lt_of_cross_mul_lt
      cert.center_firstWeight_cross_lt

/-- Cleared-denominator finite Mallows inequalities instantiate the Mallows certificate. -/
theorem centerMallowsCertificate_of_crossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsCrossWeightCertificate value) :
    C.CenterMallowsCertificate value :=
   C.centerMallowsCertificate_of_weightCertificate
    (C.centerMallowsWeightCertificate_of_crossWeightCertificate cert)

/-- Normalized weight-level Mallows inequalities imply the paper hypotheses. -/
theorem paperHypotheses_of_centerMallowsWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_centerMallowsCertificate
    (C.centerMallowsCertificate_of_weightCertificate cert)

/-- Cleared-denominator finite Mallows inequalities imply the paper hypotheses. -/
theorem paperHypotheses_of_centerMallowsCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_centerMallowsWeightCertificate
    (C.centerMallowsWeightCertificate_of_crossWeightCertificate cert)

/-- The algorithm law's center first-choice summand is strictly positive. -/
theorem algorithm_center_summand_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value) :
    0 < firstChoiceMissProb C.algorithm.law C.algorithm.centerFirst *
      firstChoiceGapMass C.algorithm.law value C.algorithm.centerFirst :=
   mul_pos C.algorithm.centerFirstMissProb_pos
    (C.algorithm_centerGapMass_pos_of_strictlyCenterOrdered hvalue)

/-- The human law's center first-choice summand is strictly positive. -/
theorem human_center_summand_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value) :
    0 < firstChoiceMissProb C.human.law C.human.centerFirst *
      firstChoiceGapMass C.human.law value C.human.centerFirst :=
   mul_pos C.human.centerFirstMissProb_pos
    (C.human_centerGapMass_pos_of_strictlyCenterOrdered hvalue)

/--
Strict cross-multiplied center first-choice improvement makes the
weaker-competition center product strictly positive.
-/
theorem weaker_center_cross_product_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value)
    (hcenter :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      firstChoiceGapMass C.human.law value C.human.centerFirst := by
  have hcenter' :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.human.centerFirst * C.human.partition := by
    simpa [C.algorithm_centerFirst_eq_human_centerFirst] using hcenter
  exact mul_pos (sub_pos.mpr hcenter')
    (C.human_centerGapMass_pos_of_strictlyCenterOrdered hvalue)

/--
Product-sign finite Mallows certificate with partition denominators cleared.

This is the sharp paper-facing finite-inequality target for the current
formalization: the weaker-competition term is recorded as a product sign rather
than as separate signs for the probability and value-gap factors.
-/
structure CenterMallowsProductCrossWeightCertificate
    (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_cross_product_nonneg :
    ∀ c : Candidate n,
      0 ≤ (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        firstChoiceGapMass C.human.law value c
  center_firstWeight_cross_lt :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition

/--
Reduced product-sign Mallows certificate.

The center-candidate positivity obligations are discharged by generic support
lemmas, so this certificate only asks for non-center finite Mallows inequalities.
-/
structure CenterMallowsReducedProductCrossWeightCertificate
    (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_noncenter_nonneg :
    ∀ c : Candidate n, c ≠ C.algorithm.centerFirst →
      0 ≤ firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_noncenter_nonneg :
    ∀ c : Candidate n, c ≠ C.human.centerFirst →
      0 ≤ firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_noncenter_cross_product_nonneg :
    ∀ c : Candidate n, c ≠ C.human.centerFirst →
      0 ≤ (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        firstChoiceGapMass C.human.law value c
  center_firstWeight_cross_lt :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition

/--
The product-sign finite Mallows certificate instantiates the main Mallows
certificate without requiring over-strong candidatewise probability monotonicity.
-/
theorem centerMallowsCertificate_of_productCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsProductCrossWeightCertificate value) :
    C.CenterMallowsCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · exact cert.algorithm_nonneg
  · exact cert.human_nonneg
  · intro c
    exact C.collisionDiff_mul_gap_nonneg_of_cross_mul_gap_nonneg value c
      (cert.weaker_cross_product_nonneg c)
  · exact C.centerFirstProb_lt_of_centerFirstWeight_div_lt
      (C.centerFirstWeight_div_lt_of_cross_mul_lt
        cert.center_firstWeight_cross_lt)

/--
The reduced product-sign certificate instantiates the full product-sign
certificate; only non-center Mallows finite inequalities remain as assumptions.
-/
theorem centerMallowsProductCrossWeightCertificate_of_reduced
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsReducedProductCrossWeightCertificate value) :
    C.CenterMallowsProductCrossWeightCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · intro c
    by_cases hc : c = C.algorithm.centerFirst
    · subst c
      exact le_of_lt
        (C.algorithm_center_summand_pos_of_strictlyCenterOrdered
          cert.strictly_center_ordered)
    · exact cert.algorithm_noncenter_nonneg c hc
  · intro c
    by_cases hc : c = C.human.centerFirst
    · subst c
      exact le_of_lt
        (C.human_center_summand_pos_of_strictlyCenterOrdered
          cert.strictly_center_ordered)
    · exact cert.human_noncenter_nonneg c hc
  · intro c
    by_cases hc : c = C.human.centerFirst
    · subst c
      exact le_of_lt
        (C.weaker_center_cross_product_pos_of_strictlyCenterOrdered
          cert.strictly_center_ordered cert.center_firstWeight_cross_lt)
    · exact cert.weaker_noncenter_cross_product_nonneg c hc
  · exact cert.center_firstWeight_cross_lt

/--
Product-sign finite Mallows inequalities imply the paper hypotheses for the
pointwise-value monoculture model.
-/
theorem paperHypotheses_of_centerMallowsProductCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsProductCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_centerMallowsCertificate
    (C.centerMallowsCertificate_of_productCrossWeightCertificate cert)

/--
Reduced product-sign finite Mallows inequalities imply the paper hypotheses for
the pointwise-value monoculture model.
-/
theorem paperHypotheses_of_centerMallowsReducedProductCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsReducedProductCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_centerMallowsProductCrossWeightCertificate
    (C.centerMallowsProductCrossWeightCertificate_of_reduced cert)

/--
Paper-facing pointwise Mallows theorem for the monoculture formalization.  The
remaining assumptions are exactly the non-center finite Mallows product
inequalities plus strict center first-choice improvement.
-/
theorem theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsReducedProductCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=  C.paperHypotheses_of_centerMallowsReducedProductCrossWeightCertificate cert

end MallowsComparison
end KR21Monoculture
