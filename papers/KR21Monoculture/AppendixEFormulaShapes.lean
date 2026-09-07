import KR21Monoculture.MallowsFamily
import KR21Monoculture.ConditionalForm
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# KR21 Appendix E formula audit surface

Appendix E proves Theorem 3's Definition 2 condition by three displayed
steps.  This module keeps those steps in their literal finite-probability
form:

* (E.1) is the first-minus-second value gap conditional on iid top-choice
  disagreement;
* (E.2) compares the two ordered top-two events after that same conditioning;
* (E.3) clears the shared conditional denominator and factors the iid event
  probability into an ordered-top-two probability times a top-miss probability.

The source theorem is not valid with only two candidates: the strict (E.1)
conclusion is then zero even for a nondegenerate Mallows law and a strict value
order.  The proved strict endpoint below consequently has `0 < n`, which
means that `Candidate n` has at least three elements.  No arbitrary
candidate-distribution or tie-handling claim is made here; the finite result
assumes the strict center/value order used by the Appendix E calculation.
-/

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
The literal Appendix E (E.1) conditional expression.  The first coordinate is
the ranking called `π` in the paper and the second is its independent draw
`τ`; conditioning is on their first choices differing.
-/
noncomputable def appendixE1SourceGap (value : Candidate n → ℝ) : ℝ :=
  AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
    (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1))

/--
The literal conditional probability occurring in Appendix E (E.2): the first
draw begins with the ordered pair `(c,d)`, conditional on iid top-choice
disagreement.
-/
noncomputable def appendixE2ConditionalTopTwoProbability
    (c d : Candidate n) : ℝ :=
  AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
    (fun pair =>
      if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0)

/--
The exact difference displayed in Appendix E (E.3), before division by the
common disagreement probability.  Independent draws make each term a product
of an ordered-top-two probability and a top-miss probability.
-/
noncomputable def appendixE3CrossDifference (c d : Candidate n) : ℝ :=
  M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
    M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d

/-- The formula-shape of Appendix E (E.2), indexed by the center's value order. -/
def AppendixE2PairwiseComparison : Prop :=
  ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
    M.appendixE2ConditionalTopTwoProbability d c ≤
      M.appendixE2ConditionalTopTwoProbability c d

/-- The strict-witness clause following (E.2) in the source. -/
def AppendixE2StrictWitness : Prop :=
  ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
    M.appendixE2ConditionalTopTwoProbability d c <
      M.appendixE2ConditionalTopTwoProbability c d

/-- The formula-shape of Appendix E (E.3), indexed by the center's value order. -/
def AppendixE3PairwiseCrossInequality : Prop :=
  ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
    0 ≤ M.appendixE3CrossDifference c d

/-- Every positive-parameter finite Mallows law has a non-null iid
top-disagreement event. -/
theorem appendixE_disagreementProb_pos :
    0 < disagreementProb M.law := by
  change 0 < AppliedModelingLib.pmfPairExp M.law M.law
    (fun pi tau => if disagreementEvent (pi, tau) then 1 else 0)
  rw [← AppliedModelingLib.pmfExp_pmfProd_eq_pairExp M.law M.law
    (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)]
  refine AppliedModelingLib.pmfProb_pos_of_mass (AppliedModelingLib.pmfProd M.law M.law)
    disagreementEvent (M.center, swapTopTwo M.center) ?_ ?_
  · exact (swapTopTwo_firstChoice_ne M.center).symm
  · rw [AppliedModelingLib.pmfProd_apply_toReal]
    exact mul_pos (M.law_apply_toReal_pos M.center)
      (M.law_apply_toReal_pos (swapTopTwo M.center))

/--
The actual conditional event in (E.2) factors exactly as the source claims.
The first factor is the probability of the ordered top-two event and the
second is the independent draw's probability of missing that first candidate.
-/
theorem appendixE2ConditionalTopTwoProbability_eq_source_product_div
    (c d : Candidate n) :
    M.appendixE2ConditionalTopTwoProbability c d =
      (M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c) /
        disagreementProb M.law := by
  classical
  rw [appendixE2ConditionalTopTwoProbability,
    AppliedModelingLib.pmfPairConditionalExp_eq_div_of_pos]
  · congr 1
    unfold AppliedModelingLib.pmfPairIndicatorExp
    calc
      AppliedModelingLib.pmfPairExp M.law M.law
          (fun pi tau =>
            if disagreementEvent (pi, tau) then
              if c = firstChoice pi ∧ d = secondChoice pi then (1 : ℝ) else 0
            else 0)
          = AppliedModelingLib.pmfPairExp M.law M.law
              (fun pi tau =>
                if (c = firstChoice pi ∧ d = secondChoice pi) ∧
                    c ≠ firstChoice tau then (1 : ℝ) else 0) := by
            unfold AppliedModelingLib.pmfPairExp
            refine AppliedModelingLib.pmfExp_congr M.law ?_
            intro pi
            refine AppliedModelingLib.pmfExp_congr M.law ?_
            intro tau
            by_cases htop : c = firstChoice pi ∧ d = secondChoice pi
            · have htopraw : c = pi 0 ∧ d = pi 1 := by
                simpa [firstChoice, secondChoice] using htop
              by_cases hmiss : c ≠ firstChoice tau
              · have hmissraw : c ≠ tau 0 := by
                  simpa [firstChoice] using hmiss
                have hdisraw : pi 0 ≠ tau 0 := by
                  intro heq
                  exact hmissraw (htopraw.1.trans heq)
                simp [disagreementEvent, firstChoice, secondChoice,
                  htopraw, hdisraw]
              · push Not at hmiss
                have hmissraw : c = tau 0 := by
                  simpa [firstChoice] using hmiss
                have hdisraw : pi 0 = tau 0 :=
                  htopraw.1.symm.trans hmissraw
                simp [disagreementEvent, firstChoice, secondChoice,
                  htopraw, hdisraw]
            · have hraw : ¬(c = pi 0 ∧ d = pi 1) := by
                simpa [firstChoice, secondChoice] using htop
              by_cases hdisagreement : disagreementEvent (pi, tau) <;>
                simp [hraw, hdisagreement]
      _ = M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c := by
            rw [firstChoiceMissProb_eq_pmfProb_ne]
            simpa [MallowsSpec.firstSecondChoiceProb] using
              (AppliedModelingLib.pmfPairExp_indicator_and_eq_mul_pmfProb M.law M.law
                (fun pi => c = firstChoice pi ∧ d = secondChoice pi)
                (fun tau => c ≠ firstChoice tau))
  · exact M.appendixE_disagreementProb_pos

/--
The literal conditional expectation (E.1) is exactly the library's
top-disagreement gain, not merely an implication to a downstream payoff
predicate.
-/
theorem appendixE1SourceGap_eq_disagreementConditionalGain
    (value : Candidate n → ℝ) :
    M.appendixE1SourceGap value = disagreementConditionalGain M.law value := by
  change
    AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
        (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) =
      AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
        (fun pair => rerankingGainOnPair value pair.1 pair.2)
  have hindicator :
      AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
          (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) =
        AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
          (fun pair => rerankingGainOnPair value pair.1 pair.2) := by
    unfold AppliedModelingLib.pmfPairIndicatorExp AppliedModelingLib.pmfPairExp
    refine AppliedModelingLib.pmfExp_congr M.law ?_
    intro pi
    refine AppliedModelingLib.pmfExp_congr M.law ?_
    intro tau
    by_cases hdisagreement : disagreementEvent (pi, tau)
    · have hfirst : firstChoice pi ≠ firstChoice tau := hdisagreement
      have hfistraw : pi 0 ≠ tau 0 := by
        simpa [firstChoice] using hfirst
      simp [hdisagreement, rerankingGainOnPair, hfistraw]
    · have hfirst : firstChoice pi = firstChoice tau := by
        simpa [disagreementEvent] using not_not.mp hdisagreement
      simp [hdisagreement]
  unfold AppliedModelingLib.pmfPairConditionalExp
  rw [hindicator]

/--
The literal Appendix E (E.1) conclusion holds for a strictly center-ordered
value profile once the source has at least three candidates.
-/
theorem appendixE1SourceGap_pos_of_rankFactorization
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy M.center value) :
    0 < M.appendixE1SourceGap value := by
  rw [M.appendixE1SourceGap_eq_disagreementConditionalGain]
  rw [disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos]
  · exact div_pos
      (by
        rw [expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass]
        exact M.firstChoice_miss_gap_sum_pos_of_weight_sum_pos
          (M.independent_weight_sum_pos_of_rankFactorization fac hn hq_lt_one hvalue))
      M.appendixE_disagreementProb_pos
  · exact M.appendixE_disagreementProb_pos

/--
Appendix E (E.3) is precisely the existing unnormalised top-two bracket after
clearing the positive Mallows partition square.
-/
theorem appendixE3CrossDifference_eq_independentPairBracket_div_partition_sq
    (c d : Candidate n) :
    M.appendixE3CrossDifference c d =
      M.independentPairBracket c d / (M.partition * M.partition) := by
  unfold appendixE3CrossDifference
  rw [M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition c d,
    M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition d c,
    M.firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition c,
    M.firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition d]
  unfold independentPairBracket
  field_simp [M.partition_ne_zero]

/-- The source E.3 inequality is proved for every center-ordered pair. -/
theorem appendixE3CrossDifference_nonneg_of_rankFactorization
    (fac : M.RankFactorization) (hq_le_one : M.q ≤ 1)
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    0 ≤ M.appendixE3CrossDifference c d := by
  rw [M.appendixE3CrossDifference_eq_independentPairBracket_div_partition_sq c d]
  exact div_nonneg
    (M.independentPairBracket_nonneg_of_rankFactorization fac hq_le_one hcd)
    (le_of_lt (mul_pos M.partition_pos M.partition_pos))

/--
The source has a strict E.3 witness once there are at least three candidates:
the center's first two candidates.
-/
theorem appendixE3CrossDifference_centerTopTwo_pos_of_rankFactorization
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1) :
    0 < M.appendixE3CrossDifference M.centerFirst M.centerSecond := by
  rw [M.appendixE3CrossDifference_eq_independentPairBracket_div_partition_sq]
  exact div_pos
    (M.independentPairBracket_centerTopTwo_pos_of_rankFactorization fac hn hq_lt_one)
    (mul_pos M.partition_pos M.partition_pos)

/--
The literal E.3 comparison implies the literal E.2 conditional comparison,
with the same quantification over ordered candidate pairs.
-/
theorem appendixE2PairwiseComparison_of_appendixE3
    (hE3 : M.AppendixE3PairwiseCrossInequality) :
    M.AppendixE2PairwiseComparison := by
  intro c d hcd
  rw [M.appendixE2ConditionalTopTwoProbability_eq_source_product_div d c,
    M.appendixE2ConditionalTopTwoProbability_eq_source_product_div c d]
  apply sub_nonneg.mp
  rw [← sub_div]
  refine div_nonneg ?_ (le_of_lt M.appendixE_disagreementProb_pos)
  simpa [appendixE3CrossDifference] using hE3 c d hcd

/-- The rank-factorized Mallows calculation proves every E.2 weak comparison. -/
theorem appendixE2PairwiseComparison_of_rankFactorization
    (fac : M.RankFactorization) (hq_le_one : M.q ≤ 1) :
    M.AppendixE2PairwiseComparison :=
  M.appendixE2PairwiseComparison_of_appendixE3
    (fun c d hcd =>
      M.appendixE3CrossDifference_nonneg_of_rankFactorization fac hq_le_one hcd)

/--
For at least three candidates, the source's strict E.2 witness is supplied by
the center's first two candidates.
-/
theorem appendixE2StrictWitness_of_rankFactorization
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1) :
    M.AppendixE2StrictWitness := by
  refine ⟨M.centerFirst, M.centerSecond, ?_, ?_⟩
  · simp [MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf]
  · rw [M.appendixE2ConditionalTopTwoProbability_eq_source_product_div
      M.centerSecond M.centerFirst,
      M.appendixE2ConditionalTopTwoProbability_eq_source_product_div
      M.centerFirst M.centerSecond]
    apply sub_pos.mp
    rw [← sub_div]
    refine div_pos ?_ M.appendixE_disagreementProb_pos
    simpa [appendixE3CrossDifference] using
      M.appendixE3CrossDifference_centerTopTwo_pos_of_rankFactorization
        fac hn hq_lt_one

end MallowsSpec

/--
Concrete source-parameter endpoint for all three Appendix E displays.  The
paper's convention is `theta = phi - 1`, so `hθ` supplies the strict
inverse-accuracy inequality required by the finite Mallows calculation.
-/
theorem concreteMallows_appendixE_source_endpoints
    {n : ℕ} (center : Ranking n) {θ : ℝ} (hθ : 0 < θ) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center θ
    0 < M.appendixE1SourceGap value ∧
      M.AppendixE2PairwiseComparison ∧ M.AppendixE2StrictWitness ∧
      M.AppendixE3PairwiseCrossInequality ∧
      0 < M.appendixE3CrossDifference M.centerFirst M.centerSecond := by
  let M : MallowsSpec n := concreteMallowsSpec center θ
  have hq_lt_one : M.q < 1 := by
    simpa [M, concreteMallowsSpec, MallowsSpec.ofQ] using
      mallowsAccuracyQ_lt_one hθ
  have hE3 : M.AppendixE3PairwiseCrossInequality := by
    intro c d hcd
    exact M.appendixE3CrossDifference_nonneg_of_rankFactorization
      M.rankFactorization (le_of_lt hq_lt_one) hcd
  change
    0 < M.appendixE1SourceGap value ∧
      M.AppendixE2PairwiseComparison ∧ M.AppendixE2StrictWitness ∧
      M.AppendixE3PairwiseCrossInequality ∧
      0 < M.appendixE3CrossDifference M.centerFirst M.centerSecond
  exact ⟨M.appendixE1SourceGap_pos_of_rankFactorization
      M.rankFactorization hn hq_lt_one hvalue,
    M.appendixE2PairwiseComparison_of_appendixE3 hE3,
    M.appendixE2StrictWitness_of_rankFactorization
      M.rankFactorization hn hq_lt_one,
    hE3,
    M.appendixE3CrossDifference_centerTopTwo_pos_of_rankFactorization
      M.rankFactorization hn hq_lt_one⟩

end KR21Monoculture
