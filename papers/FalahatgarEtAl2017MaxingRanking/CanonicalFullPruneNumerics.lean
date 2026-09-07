import FalahatgarEtAl2017MaxingRanking.CanonicalFullPruneBatches
import FalahatgarEtAl2017MaxingRanking.PruneSourceNumerics

/-!
# Full-arm canonical Prune-round arithmetic

This exposes the Lemma 15 contraction tail for the full-arm coupling used to
compose fresh, history-selected Prune rounds.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
For any current active set, the full-arm canonical coupling contracts its
threshold-nonbetter survivors by `delta` except at the Lemma 15 Chernoff tail.
The full batch has unused coordinates, but its decision is restricted to the
current active set.
-/
theorem canonicalFullPruneRound_badSurvivor_contraction_failure_le_exp
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper delta eta : ℝ)
    (hseparation : lower < upper) (hdelta : 0 < delta)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1) (hetaBound : eta ≤ delta / 4) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        delta * ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) <
        (((pruneRound active
          (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
        delta / 2) := by
  let badCount : ℝ :=
    ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)
  have hbadNonneg : 0 ≤ badCount := by positivity
  have hetaNonneg : 0 ≤ eta := heta.le
  have hterm : badCount * ((Real.exp 1 - 1) * eta) ≤ badCount * (delta / 2) := by
    apply mul_le_mul_of_nonneg_left _ hbadNonneg
    calc
      (Real.exp 1 - 1) * eta ≤ (2 : ℝ) * eta := by
        exact mul_le_mul_of_nonneg_right exp_one_sub_one_le_two hetaNonneg
      _ ≤ (2 : ℝ) * (delta / 4) := by
        exact mul_le_mul_of_nonneg_left hetaBound (by norm_num)
      _ = delta / 2 := by ring
  have hexponent :
      - (delta * badCount) + badCount * ((Real.exp 1 - 1) * eta) ≤
        -badCount * delta / 2 := by
    nlinarith [hterm]
  have htail := canonicalFullPruneRound_badSurvivorCard_probability_exponential
    preferenceGap hprobability active anchor lower upper eta (delta * badCount) 1
    hseparation heta hetaLeOne (by norm_num : (0 : ℝ) ≤ 1)
  change (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
    (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
      delta * badCount <
      (((pruneRound active
        (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
        fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-badCount * delta / 2)
  calc
    (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        delta * badCount <
        (((pruneRound active
          (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
        (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
          (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
            delta * badCount ≤
            (((pruneRound active
              (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
              fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro batchTable hstrict
          simp only [Set.mem_setOf_eq] at hstrict ⊢
          exact hstrict.le
    _ ≤ Real.exp (-(1 : ℝ) * (delta * badCount) + badCount *
        ((Real.exp (1 : ℝ) - 1) * eta)) := by
      simpa [badCount] using htail
    _ = Real.exp (- (delta * badCount) + badCount * ((Real.exp 1 - 1) * eta)) := by ring_nf
    _ ≤ Real.exp (-badCount * delta / 2) := Real.exp_le_exp.mpr hexponent

end FalahatgarEtAl2017MaxingRanking
