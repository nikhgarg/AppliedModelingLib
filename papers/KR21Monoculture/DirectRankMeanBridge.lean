import KR21Monoculture.QuantitativeWitnesses

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Direct finite rank-mean bridge

This module relates the collapsed three-firm arithmetic in
`QuantitativeWitnesses` to direct finite product-law expectations of the
sequential `sourceFocalUtility`.  It remains a rank-mean model: it does not
claim a bridge to the paper's cardinal Uniform-value experiment.
-/

/-- The six equiprobable firm-arrival atoms have total mass one. -/
theorem sourceUniformFirmOrderMass_sum :
    (∑ order : SourceFirmOrder, sourceUniformFirmOrderMass) = 1 := by
  rw [SourceFirmOrder.sum_six]
  norm_num [sourceUniformFirmOrderMass]

/-- The declared shared-algorithm ranking law has total mass one. -/
theorem sourceAlgorithmMallowsMass_sum :
    (∑ algorithm : SourceFourRanking, sourceAlgorithmMallowsMass algorithm) = 1 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceAlgorithmMallowsMass]

/-- Joint mass of three independent human-ranking coordinates. -/
def sourceHumanTripleProductMass
    (h0 h1 h2 : SourceFourRanking) : ℚ :=
  sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1 *
    sourceHumanMallowsMass h2

/-- The declared three-human finite product mass is normalized. -/
theorem sourceHumanTripleProductMass_sum :
    (∑ h0 : SourceFourRanking,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          sourceHumanTripleProductMass h0 h1 h2) = 1 := by
  unfold sourceHumanTripleProductMass
  calc
    (∑ h0 : SourceFourRanking,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1 *
            sourceHumanMallowsMass h2) =
        ∑ h0 : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            (sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1) *
              (∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2) := by
      apply Finset.sum_congr rfl
      intro h0 _
      apply Finset.sum_congr rfl
      intro h1 _
      rw [Finset.mul_sum]
    _ = ∑ h0 : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1 := by
      rw [sourceHumanMallowsMass_sum]
      simp
    _ = (∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0) *
          (∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h0 _
      rw [Finset.mul_sum]
    _ = 1 := by
      rw [sourceHumanMallowsMass_sum]
      norm_num

/--
Direct all-human rank-mean expectation conditional on a firm order.  Each
branch lists all three independent human-ranking coordinates once; its nesting
order follows the sequential arrival order so the existing finite transition
lemmas can discharge the corresponding conditional expectation.
-/
def sourceDirectRankMeanConditionalHHH : SourceFirmOrder → ℚ
  | .f012 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
            sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) .f012
  | .f021 =>
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
            sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) .f021
  | .f102 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
            sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) .f102
  | .f120 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
            sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) .f120
  | .f201 =>
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
            sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) .f201
  | .f210 =>
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
            sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) .f210

/-- Direct all-human finite product-law rank-mean expectation. -/
def sourceDirectRankMeanExpectedHHH : ℚ :=
  ∑ order : SourceFirmOrder,
    sourceUniformFirmOrderMass * sourceDirectRankMeanConditionalHHH order

/-- Canonical `h0,h1,h2` nesting of the same direct all-human product expectation. -/
def sourceCanonicalDirectRankMeanConditionalHHH
    (order : SourceFirmOrder) : ℚ :=
  ∑ h0 : SourceFourRanking,
    ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        sourceHumanTripleProductMass h0 h1 h2 *
          sourceFocalUtility sourceProfileHHH .r0123
            (sourceHumanRankings h0 h1 h2) order

/-- Canonically nested direct all-human finite product-law rank-mean expectation. -/
def sourceCanonicalDirectRankMeanExpectedHHH : ℚ :=
  ∑ order : SourceFirmOrder,
    sourceUniformFirmOrderMass *
      sourceCanonicalDirectRankMeanConditionalHHH order

/-! ## Direct sequential reduction by order -/

private theorem sourceHumanTripleProductMass_rotate_h1_h2_h0
    (f : SourceFourRanking → SourceFourRanking → SourceFourRanking → ℚ) :
    (∑ h0 : SourceFourRanking,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          sourceHumanTripleProductMass h0 h1 h2 * f h0 h1 h2) =
      ∑ h1 : SourceFourRanking,
        sourceHumanMallowsMass h1 *
          (∑ h2 : SourceFourRanking,
            sourceHumanMallowsMass h2 *
              (∑ h0 : SourceFourRanking,
                sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
  unfold sourceHumanTripleProductMass
  calc
    (∑ h0 : SourceFourRanking,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1 *
            sourceHumanMallowsMass h2 * f h0 h1 h2) =
        ∑ h1 : SourceFourRanking,
          ∑ h0 : SourceFourRanking,
            ∑ h2 : SourceFourRanking,
              sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1 *
                sourceHumanMallowsMass h2 * f h0 h1 h2 := by
      rw [Finset.sum_comm]
    _ = ∑ h1 : SourceFourRanking,
          ∑ h2 : SourceFourRanking,
            ∑ h0 : SourceFourRanking,
              sourceHumanMallowsMass h0 * sourceHumanMallowsMass h1 *
                sourceHumanMallowsMass h2 * f h0 h1 h2 := by
      apply Finset.sum_congr rfl
      intro h1 _
      rw [Finset.sum_comm]
    _ = ∑ h1 : SourceFourRanking,
          ∑ h2 : SourceFourRanking,
            ∑ h0 : SourceFourRanking,
              sourceHumanMallowsMass h1 *
                (sourceHumanMallowsMass h2 *
                  (sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
      apply Finset.sum_congr rfl
      intro h1 _
      apply Finset.sum_congr rfl
      intro h2 _
      apply Finset.sum_congr rfl
      intro h0 _
      ring
    _ = ∑ h1 : SourceFourRanking,
          sourceHumanMallowsMass h1 *
            (∑ h2 : SourceFourRanking,
              sourceHumanMallowsMass h2 *
                (∑ h0 : SourceFourRanking,
                  sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
      simp_rw [Finset.mul_sum]

private theorem sourceHumanTripleProductMass_reverse_h2_h1_h0
    (f : SourceFourRanking → SourceFourRanking → SourceFourRanking → ℚ) :
    (∑ h0 : SourceFourRanking,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          sourceHumanTripleProductMass h0 h1 h2 * f h0 h1 h2) =
      ∑ h2 : SourceFourRanking,
        sourceHumanMallowsMass h2 *
          (∑ h1 : SourceFourRanking,
            sourceHumanMallowsMass h1 *
              (∑ h0 : SourceFourRanking,
                sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
  rw [sourceHumanTripleProductMass_rotate_h1_h2_h0]
  calc
    (∑ h1 : SourceFourRanking,
      sourceHumanMallowsMass h1 *
        (∑ h2 : SourceFourRanking,
          sourceHumanMallowsMass h2 *
            (∑ h0 : SourceFourRanking,
              sourceHumanMallowsMass h0 * f h0 h1 h2))) =
        ∑ h2 : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            ∑ h0 : SourceFourRanking,
              sourceHumanMallowsMass h1 *
                (sourceHumanMallowsMass h2 *
                  (sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ h2 : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            ∑ h0 : SourceFourRanking,
              sourceHumanMallowsMass h2 *
                (sourceHumanMallowsMass h1 *
                  (sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
      apply Finset.sum_congr rfl
      intro h2 _
      apply Finset.sum_congr rfl
      intro h1 _
      apply Finset.sum_congr rfl
      intro h0 _
      ring
    _ = ∑ h2 : SourceFourRanking,
          sourceHumanMallowsMass h2 *
            (∑ h1 : SourceFourRanking,
              sourceHumanMallowsMass h1 *
                (∑ h0 : SourceFourRanking,
                  sourceHumanMallowsMass h0 * f h0 h1 h2)) := by
      simp_rw [Finset.mul_sum]

/-- Push a human-ranking expectation through its first selected candidate. -/
private theorem sourceHuman_expectation_of_top
    (f : SourceFourCandidate → ℚ) :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        f (sourceBestAvailable human ∅)) =
      ∑ candidate : SourceFourCandidate,
        sourceHumanTopCandidateMass candidate * f candidate := by
  have hindicator (human : SourceFourRanking) :
      f (sourceBestAvailable human ∅) =
        ∑ candidate : SourceFourCandidate,
          (if sourceBestAvailable human ∅ = candidate then 1 else 0) *
            f candidate := by
    symm
    simpa [ite_mul] using
      (Fintype.sum_ite_eq (i := sourceBestAvailable human ∅) f)
  have htop (candidate : SourceFourCandidate) :
      (∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          (if sourceBestAvailable human ∅ = candidate then 1 else 0)) =
        sourceHumanTopCandidateMass candidate := by
    simpa only [sourceBestAvailable_empty] using
      (sourceHumanTopCandidateMass_eq_ranking_sum candidate).symm
  calc
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        f (sourceBestAvailable human ∅)) =
        ∑ human : SourceFourRanking,
          sourceHumanMallowsMass human *
            (∑ candidate : SourceFourCandidate,
              (if sourceBestAvailable human ∅ = candidate then 1 else 0) *
                f candidate) := by
      simp_rw [hindicator]
    _ = ∑ human : SourceFourRanking,
          ∑ candidate : SourceFourCandidate,
            sourceHumanMallowsMass human *
              ((if sourceBestAvailable human ∅ = candidate then 1 else 0) *
                f candidate) := by
      apply Finset.sum_congr rfl
      intro human _
      rw [Finset.mul_sum]
    _ = ∑ candidate : SourceFourCandidate,
          ∑ human : SourceFourRanking,
            sourceHumanMallowsMass human *
              ((if sourceBestAvailable human ∅ = candidate then 1 else 0) *
                f candidate) := by
      rw [Finset.sum_comm]
    _ = ∑ candidate : SourceFourCandidate,
          (∑ human : SourceFourRanking,
            sourceHumanMallowsMass human *
              (if sourceBestAvailable human ∅ = candidate then 1 else 0)) *
            f candidate := by
      apply Finset.sum_congr rfl
      intro candidate _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro human _
      ring
    _ = ∑ candidate : SourceFourCandidate,
          sourceHumanTopCandidateMass candidate * f candidate := by
      simp_rw [htop]

/-- Push a human-ranking expectation through its choice after one selection. -/
private theorem sourceHuman_expectation_after_one
    (selected : SourceFourCandidate) (f : SourceFourCandidate → ℚ) :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        f (sourceBestAvailable human {selected})) =
      ∑ next : SourceFourCandidate,
        sourceHumanNextCandidateMass selected next * f next := by
  have hindicator (human : SourceFourRanking) :
      f (sourceBestAvailable human {selected}) =
        ∑ next : SourceFourCandidate,
          (if sourceBestAvailable human {selected} = next then 1 else 0) *
            f next := by
    symm
    simpa [ite_mul] using
      (Fintype.sum_ite_eq (i := sourceBestAvailable human {selected}) f)
  have hnext (next : SourceFourCandidate) :
      (∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          (if sourceBestAvailable human {selected} = next then 1 else 0)) =
        sourceHumanNextCandidateMass selected next := by
    simpa only [sourceBestAvailable_singleton] using
      (sourceHumanNextCandidateMass_eq_ranking_sum selected next).symm
  calc
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        f (sourceBestAvailable human {selected})) =
        ∑ human : SourceFourRanking,
          sourceHumanMallowsMass human *
            (∑ next : SourceFourCandidate,
              (if sourceBestAvailable human {selected} = next then 1 else 0) *
                f next) := by
      simp_rw [hindicator]
    _ = ∑ human : SourceFourRanking,
          ∑ next : SourceFourCandidate,
            sourceHumanMallowsMass human *
              ((if sourceBestAvailable human {selected} = next then 1 else 0) *
                f next) := by
      apply Finset.sum_congr rfl
      intro human _
      rw [Finset.mul_sum]
    _ = ∑ next : SourceFourCandidate,
          ∑ human : SourceFourRanking,
            sourceHumanMallowsMass human *
              ((if sourceBestAvailable human {selected} = next then 1 else 0) *
                f next) := by
      rw [Finset.sum_comm]
    _ = ∑ next : SourceFourCandidate,
          (∑ human : SourceFourRanking,
            sourceHumanMallowsMass human *
              (if sourceBestAvailable human {selected} = next then 1 else 0)) *
            f next := by
      apply Finset.sum_congr rfl
      intro next _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro human _
      ring
    _ = ∑ next : SourceFourCandidate,
          sourceHumanNextCandidateMass selected next * f next := by
      simp_rw [hnext]

private theorem sourceFocalUtility_HHH_f012
    (h0 h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) .f012 =
      sourceExpectedOrderStatisticValue (sourceBestAvailable h0 ∅) := by
  simp [sourceFocalUtility, sourceProfileHHH, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HHH_f021
    (h0 h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) .f021 =
      sourceExpectedOrderStatisticValue (sourceBestAvailable h0 ∅) := by
  simp [sourceFocalUtility, sourceProfileHHH, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HHH_f102
    (h0 h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) .f102 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0 {sourceBestAvailable h1 ∅}) := by
  simp [sourceFocalUtility, sourceProfileHHH, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HHH_f201
    (h0 h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) .f201 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0 {sourceBestAvailable h2 ∅}) := by
  simp [sourceFocalUtility, sourceProfileHHH, sourceHumanRankings,
    sourceFirmOrderAt, Fin.ext_iff]

private theorem sourceFocalUtility_HHH_f120
    (h0 h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) .f120 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0
          {sourceBestAvailable h1 ∅,
            sourceBestAvailable h2 {sourceBestAvailable h1 ∅}}) := by
  simp [sourceFocalUtility, sourceProfileHHH, sourceHumanRankings,
    sourceFirmOrderAt, Fin.ext_iff]

private theorem sourceFocalUtility_HHH_f210
    (h0 h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) .f210 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0
          {sourceBestAvailable h2 ∅,
            sourceBestAvailable h1 {sourceBestAvailable h2 ∅}}) := by
  simp [sourceFocalUtility, sourceProfileHHH, sourceHumanRankings,
    sourceFirmOrderAt, Fin.ext_iff]

/-- Direct conditioning for an arrival order in which the focal human is first. -/
theorem sourceDirectRankMeanConditionalHHH_f012 :
    sourceDirectRankMeanConditionalHHH .f012 = sourceConditionalHHH .f012 := by
  unfold sourceDirectRankMeanConditionalHHH sourceConditionalHHH
  simp_rw [sourceFocalUtility_HHH_f012]
  rw [← sourceHumanExpectedFirstValue_eq_ranking_sum]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  simp
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning for the other arrival order in which the focal human is first. -/
theorem sourceDirectRankMeanConditionalHHH_f021 :
    sourceDirectRankMeanConditionalHHH .f021 = sourceConditionalHHH .f021 := by
  unfold sourceDirectRankMeanConditionalHHH sourceConditionalHHH
  simp_rw [sourceFocalUtility_HHH_f021]
  rw [← sourceHumanExpectedFirstValue_eq_ranking_sum]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  simp
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning when the focal human arrives second after firm `1`. -/
theorem sourceDirectRankMeanConditionalHHH_f102 :
    sourceDirectRankMeanConditionalHHH .f102 = sourceConditionalHHH .f102 := by
  unfold sourceDirectRankMeanConditionalHHH sourceConditionalHHH
  simp_rw [sourceFocalUtility_HHH_f102]
  simp_rw [← sourceHumanExpectedAfterOneValue_eq_ranking_sum]
  have hunused (first : SourceFourRanking) :
      (∑ unused : SourceFourRanking,
        sourceHumanMallowsMass unused *
          sourceHumanExpectedAfterOneValue
            (sourceBestAvailable first ∅)) =
        sourceHumanExpectedAfterOneValue
          (sourceBestAvailable first ∅) := by
    rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
    norm_num
  simp_rw [hunused]
  rw [sourceHuman_expectation_of_top]

/-- Direct conditioning when the focal human arrives second after firm `2`. -/
theorem sourceDirectRankMeanConditionalHHH_f201 :
    sourceDirectRankMeanConditionalHHH .f201 = sourceConditionalHHH .f201 := by
  unfold sourceDirectRankMeanConditionalHHH sourceConditionalHHH
  simp_rw [sourceFocalUtility_HHH_f201]
  simp_rw [← sourceHumanExpectedAfterOneValue_eq_ranking_sum]
  have hunused (first : SourceFourRanking) :
      (∑ unused : SourceFourRanking,
        sourceHumanMallowsMass unused *
          sourceHumanExpectedAfterOneValue
            (sourceBestAvailable first ∅)) =
        sourceHumanExpectedAfterOneValue
          (sourceBestAvailable first ∅) := by
    rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
    norm_num
  simp_rw [hunused]
  rw [sourceHuman_expectation_of_top]

/-- Direct conditioning when the focal human arrives third after firms `1,2`. -/
theorem sourceDirectRankMeanConditionalHHH_f120 :
    sourceDirectRankMeanConditionalHHH .f120 = sourceConditionalHHH .f120 := by
  unfold sourceDirectRankMeanConditionalHHH sourceConditionalHHH
  simp_rw [sourceFocalUtility_HHH_f120]
  simp_rw [← sourceHumanExpectedAfterTwoValue_eq_ranking_sum]
  simp_rw [sourceHuman_expectation_after_one]
  simpa using
    (sourceHuman_expectation_of_top
      (fun first =>
        ∑ next : SourceFourCandidate,
          sourceHumanNextCandidateMass first next *
            sourceHumanExpectedAfterTwoValue first next))

/-- Direct conditioning when the focal human arrives third after firms `2,1`. -/
theorem sourceDirectRankMeanConditionalHHH_f210 :
    sourceDirectRankMeanConditionalHHH .f210 = sourceConditionalHHH .f210 := by
  unfold sourceDirectRankMeanConditionalHHH sourceConditionalHHH
  simp_rw [sourceFocalUtility_HHH_f210]
  simp_rw [← sourceHumanExpectedAfterTwoValue_eq_ranking_sum]
  simp_rw [sourceHuman_expectation_after_one]
  simpa using
    (sourceHuman_expectation_of_top
      (fun first =>
        ∑ next : SourceFourCandidate,
          sourceHumanNextCandidateMass first next *
            sourceHumanExpectedAfterTwoValue first next))

/-- Every direct all-human conditional product expectation is its collapsed evaluator. -/
theorem sourceDirectRankMeanConditionalHHH_eq_collapsed
    (order : SourceFirmOrder) :
    sourceDirectRankMeanConditionalHHH order = sourceConditionalHHH order := by
  cases order
  · exact sourceDirectRankMeanConditionalHHH_f012
  · exact sourceDirectRankMeanConditionalHHH_f021
  · exact sourceDirectRankMeanConditionalHHH_f102
  · exact sourceDirectRankMeanConditionalHHH_f120
  · exact sourceDirectRankMeanConditionalHHH_f201
  · exact sourceDirectRankMeanConditionalHHH_f210

/-- The sequentially convenient nesting is a finite-Fubini rearrangement of the canonical product law. -/
theorem sourceCanonicalDirectRankMeanConditionalHHH_eq_direct
    (order : SourceFirmOrder) :
    sourceCanonicalDirectRankMeanConditionalHHH order =
      sourceDirectRankMeanConditionalHHH order := by
  cases order
  · unfold sourceCanonicalDirectRankMeanConditionalHHH
      sourceDirectRankMeanConditionalHHH
    exact sourceHumanTripleProductMass_rotate_h1_h2_h0
      (fun h0 h1 h2 =>
        sourceFocalUtility sourceProfileHHH .r0123
          (sourceHumanRankings h0 h1 h2) .f012)
  · unfold sourceCanonicalDirectRankMeanConditionalHHH
      sourceDirectRankMeanConditionalHHH
    exact sourceHumanTripleProductMass_reverse_h2_h1_h0
      (fun h0 h1 h2 =>
        sourceFocalUtility sourceProfileHHH .r0123
          (sourceHumanRankings h0 h1 h2) .f021)
  · unfold sourceCanonicalDirectRankMeanConditionalHHH
      sourceDirectRankMeanConditionalHHH
    exact sourceHumanTripleProductMass_rotate_h1_h2_h0
      (fun h0 h1 h2 =>
        sourceFocalUtility sourceProfileHHH .r0123
          (sourceHumanRankings h0 h1 h2) .f102)
  · unfold sourceCanonicalDirectRankMeanConditionalHHH
      sourceDirectRankMeanConditionalHHH
    exact sourceHumanTripleProductMass_rotate_h1_h2_h0
      (fun h0 h1 h2 =>
        sourceFocalUtility sourceProfileHHH .r0123
          (sourceHumanRankings h0 h1 h2) .f120)
  · unfold sourceCanonicalDirectRankMeanConditionalHHH
      sourceDirectRankMeanConditionalHHH
    exact sourceHumanTripleProductMass_reverse_h2_h1_h0
      (fun h0 h1 h2 =>
        sourceFocalUtility sourceProfileHHH .r0123
          (sourceHumanRankings h0 h1 h2) .f201)
  · unfold sourceCanonicalDirectRankMeanConditionalHHH
      sourceDirectRankMeanConditionalHHH
    exact sourceHumanTripleProductMass_reverse_h2_h1_h0
      (fun h0 h1 h2 =>
        sourceFocalUtility sourceProfileHHH .r0123
          (sourceHumanRankings h0 h1 h2) .f210)

/--
The direct all-human finite rank-mean product expectation equals the collapsed
six-order evaluator.
-/
theorem sourceDirectRankMeanExpectedHHH_eq_executable :
    sourceDirectRankMeanExpectedHHH = sourceExecutableExpectedHHH := by
  unfold sourceDirectRankMeanExpectedHHH sourceExecutableExpectedHHH
  simp_rw [sourceDirectRankMeanConditionalHHH_eq_collapsed]

/-- The canonical all-human product-law expectation equals its sequentially nested form. -/
theorem sourceCanonicalDirectRankMeanExpectedHHH_eq_direct :
    sourceCanonicalDirectRankMeanExpectedHHH =
      sourceDirectRankMeanExpectedHHH := by
  unfold sourceCanonicalDirectRankMeanExpectedHHH sourceDirectRankMeanExpectedHHH
  simp_rw [sourceCanonicalDirectRankMeanConditionalHHH_eq_direct]

/-- The canonical direct all-human finite product expectation is the collapsed evaluator. -/
theorem sourceCanonicalDirectRankMeanExpectedHHH_eq_executable :
    sourceCanonicalDirectRankMeanExpectedHHH = sourceExecutableExpectedHHH := by
  rw [sourceCanonicalDirectRankMeanExpectedHHH_eq_direct,
    sourceDirectRankMeanExpectedHHH_eq_executable]

/-- Exact rational evaluation of the direct all-human finite rank-mean expectation. -/
theorem sourceDirectRankMeanExpectedHHH_eq :
    sourceDirectRankMeanExpectedHHH =
      8730423441013 / 15807166464375 := by
  rw [sourceDirectRankMeanExpectedHHH_eq_executable,
    source_executable_expectedHHH_eq]

/-! ## One-human/two-algorithm direct product bridge -/

/--
Direct HAA expectation conditional on the shared algorithm ranking and the
firm-arrival order.  The focal firm is the human-ranked firm `0`; firms `1`
and `2` use the same sampled algorithm ranking.  Thus this is a true
three-coordinate product law over one algorithm rank, one focal human rank,
and one uniform order, rather than a re-use of a collapsed value table.
-/
def sourceDirectRankMeanConditionalHAA
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  ∑ human : SourceFourRanking,
    sourceHumanMallowsMass human *
      sourceFocalUtility sourceProfileHAA algorithm
        (sourceHumanRankings human .r0123 .r0123) order

/-- Canonically nested direct finite product expectation for the HAA profile. -/
def sourceDirectRankMeanExpectedHAA : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceDirectRankMeanConditionalHAA algorithm order)

/-- The product-law mass used by the direct HAA expectation is normalized. -/
theorem sourceDirectRankMeanHAAMass_sum :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        (∑ order : SourceFirmOrder,
          sourceUniformFirmOrderMass *
            (∑ human : SourceFourRanking, sourceHumanMallowsMass human))) = 1 := by
  rw [sourceHumanMallowsMass_sum]
  simp only [mul_one]
  rw [sourceUniformFirmOrderMass_sum]
  simp only [mul_one]
  exact sourceAlgorithmMallowsMass_sum

/-- The shared algorithm's second choice is its second-ranked candidate. -/
private theorem sourceAlgorithmBestAvailable_after_first
    (algorithm : SourceFourRanking) :
    sourceBestAvailable algorithm {algorithm 0} = algorithm 1 := by
  cases algorithm <;> decide

private theorem sourceFocalUtility_HAA_f012
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) .f012 =
      sourceExpectedOrderStatisticValue (sourceBestAvailable human ∅) := by
  simp [sourceFocalUtility, sourceProfileHAA, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HAA_f021
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) .f021 =
      sourceExpectedOrderStatisticValue (sourceBestAvailable human ∅) := by
  simp [sourceFocalUtility, sourceProfileHAA, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HAA_f102
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) .f102 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable human {algorithm 0}) := by
  simp [sourceFocalUtility, sourceProfileHAA, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_HAA_f201
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) .f201 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable human {algorithm 0}) := by
  simp [sourceFocalUtility, sourceProfileHAA, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_HAA_f120
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) .f120 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable human {algorithm 0, algorithm 1}) := by
  simp [sourceFocalUtility, sourceProfileHAA, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first]

private theorem sourceFocalUtility_HAA_f210
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) .f210 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable human {algorithm 0, algorithm 1}) := by
  simp [sourceFocalUtility, sourceProfileHAA, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first]

/-- Direct conditioning when the focal human arrives first. -/
theorem sourceDirectRankMeanConditionalHAA_f012
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAA algorithm .f012 =
      sourceConditionalHAA algorithm .f012 := by
  unfold sourceDirectRankMeanConditionalHAA sourceConditionalHAA
  simp_rw [sourceFocalUtility_HAA_f012]
  exact sourceHumanExpectedFirstValue_eq_ranking_sum.symm

/-- Direct conditioning for the other arrival order in which the focal human is first. -/
theorem sourceDirectRankMeanConditionalHAA_f021
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAA algorithm .f021 =
      sourceConditionalHAA algorithm .f021 := by
  unfold sourceDirectRankMeanConditionalHAA sourceConditionalHAA
  simp_rw [sourceFocalUtility_HAA_f021]
  exact sourceHumanExpectedFirstValue_eq_ranking_sum.symm

/-- Direct conditioning when the focal human arrives after one algorithm firm. -/
theorem sourceDirectRankMeanConditionalHAA_f102
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAA algorithm .f102 =
      sourceConditionalHAA algorithm .f102 := by
  unfold sourceDirectRankMeanConditionalHAA sourceConditionalHAA
  simp_rw [sourceFocalUtility_HAA_f102]
  exact (sourceHumanExpectedAfterOneValue_eq_ranking_sum (algorithm 0)).symm

/-- Direct conditioning when firm `2` arrives before the focal human. -/
theorem sourceDirectRankMeanConditionalHAA_f201
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAA algorithm .f201 =
      sourceConditionalHAA algorithm .f201 := by
  unfold sourceDirectRankMeanConditionalHAA sourceConditionalHAA
  simp_rw [sourceFocalUtility_HAA_f201]
  exact (sourceHumanExpectedAfterOneValue_eq_ranking_sum (algorithm 0)).symm

/-- Direct conditioning when both algorithm firms arrive before the focal human. -/
theorem sourceDirectRankMeanConditionalHAA_f120
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAA algorithm .f120 =
      sourceConditionalHAA algorithm .f120 := by
  unfold sourceDirectRankMeanConditionalHAA sourceConditionalHAA
  simp_rw [sourceFocalUtility_HAA_f120]
  exact
    (sourceHumanExpectedAfterTwoValue_eq_ranking_sum
      (algorithm 0) (algorithm 1)).symm

/-- Direct conditioning for the other order with both algorithm firms first. -/
theorem sourceDirectRankMeanConditionalHAA_f210
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAA algorithm .f210 =
      sourceConditionalHAA algorithm .f210 := by
  unfold sourceDirectRankMeanConditionalHAA sourceConditionalHAA
  simp_rw [sourceFocalUtility_HAA_f210]
  exact
    (sourceHumanExpectedAfterTwoValue_eq_ranking_sum
      (algorithm 0) (algorithm 1)).symm

/-- Every direct HAA conditional expectation is the corresponding collapsed evaluator. -/
theorem sourceDirectRankMeanConditionalHAA_eq_collapsed
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceDirectRankMeanConditionalHAA algorithm order =
      sourceConditionalHAA algorithm order := by
  cases order
  · exact sourceDirectRankMeanConditionalHAA_f012 algorithm
  · exact sourceDirectRankMeanConditionalHAA_f021 algorithm
  · exact sourceDirectRankMeanConditionalHAA_f102 algorithm
  · exact sourceDirectRankMeanConditionalHAA_f120 algorithm
  · exact sourceDirectRankMeanConditionalHAA_f201 algorithm
  · exact sourceDirectRankMeanConditionalHAA_f210 algorithm

/-- The direct HAA finite product expectation is the executable collapsed evaluator. -/
theorem sourceDirectRankMeanExpectedHAA_eq_executable :
    sourceDirectRankMeanExpectedHAA = sourceExecutableExpectedHAA := by
  unfold sourceDirectRankMeanExpectedHAA sourceExecutableExpectedHAA
  simp_rw [sourceDirectRankMeanConditionalHAA_eq_collapsed]

/-- Exact rational evaluation of the direct HAA finite product expectation. -/
theorem sourceDirectRankMeanExpectedHAA_eq :
    sourceDirectRankMeanExpectedHAA = 57174284 / 104729625 := by
  rw [sourceDirectRankMeanExpectedHAA_eq_executable,
    source_executable_expectedHAA_eq]

/-! ## Two-algorithm/one-human direct product bridge -/

/--
Direct AAH expectation conditional on the shared algorithm ranking and the
firm-arrival order.  The focal firm `0` and firm `1` use the shared algorithm
ranking; firm `2` uses the independently sampled human ranking.
-/
def sourceDirectRankMeanConditionalAAH
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  ∑ human : SourceFourRanking,
    sourceHumanMallowsMass human *
      sourceFocalUtility sourceProfileAAH algorithm
        (sourceHumanRankings .r0123 .r0123 human) order

/-- Canonically nested direct finite product expectation for the AAH profile. -/
def sourceDirectRankMeanExpectedAAH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceDirectRankMeanConditionalAAH algorithm order)

/-- The direct AAH expectation uses the same normalized three-coordinate product law. -/
theorem sourceDirectRankMeanAAHMass_sum :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        (∑ order : SourceFirmOrder,
          sourceUniformFirmOrderMass *
            (∑ human : SourceFourRanking, sourceHumanMallowsMass human))) = 1 :=
  sourceDirectRankMeanHAAMass_sum

private theorem sourceFocalUtility_AAH_f012
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) .f012 =
      sourceExpectedOrderStatisticValue (algorithm 0) := by
  simp [sourceFocalUtility, sourceProfileAAH,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_AAH_f021
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) .f021 =
      sourceExpectedOrderStatisticValue (algorithm 0) := by
  simp [sourceFocalUtility, sourceProfileAAH,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_AAH_f102
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) .f102 =
      sourceExpectedOrderStatisticValue (algorithm 1) := by
  simp [sourceFocalUtility, sourceProfileAAH,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first]

private theorem sourceFocalUtility_AAH_f120
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) .f120 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterTwo algorithm (algorithm 0)
          (sourceBestAvailable human {algorithm 0})) := by
  simp [sourceFocalUtility, sourceProfileAAH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty, sourceBestAvailable_pair]

private theorem sourceFocalUtility_AAH_f201
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) .f201 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterOne algorithm
          (sourceBestAvailable human ∅)) := by
  simp [sourceFocalUtility, sourceProfileAAH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton]

private theorem sourceFocalUtility_AAH_f210
    (algorithm human : SourceFourRanking) :
    sourceFocalUtility sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) .f210 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable human ∅)
          (sourceBestAvailableAfterOne algorithm
            (sourceBestAvailable human ∅))) := by
  simp [sourceFocalUtility, sourceProfileAAH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton, sourceBestAvailable_pair]

/-- Direct conditioning when the focal algorithm arrives first. -/
theorem sourceDirectRankMeanConditionalAAH_f012
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAH algorithm .f012 =
      sourceConditionalAAH algorithm .f012 := by
  unfold sourceDirectRankMeanConditionalAAH sourceConditionalAAH
  simp_rw [sourceFocalUtility_AAH_f012]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning for the other order in which the focal algorithm arrives first. -/
theorem sourceDirectRankMeanConditionalAAH_f021
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAH algorithm .f021 =
      sourceConditionalAAH algorithm .f021 := by
  unfold sourceDirectRankMeanConditionalAAH sourceConditionalAAH
  simp_rw [sourceFocalUtility_AAH_f021]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning when the focal algorithm follows the other algorithm firm. -/
theorem sourceDirectRankMeanConditionalAAH_f102
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAH algorithm .f102 =
      sourceConditionalAAH algorithm .f102 := by
  unfold sourceDirectRankMeanConditionalAAH sourceConditionalAAH
  simp_rw [sourceFocalUtility_AAH_f102]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning when a human first choice precedes the focal algorithm. -/
theorem sourceDirectRankMeanConditionalAAH_f201
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAH algorithm .f201 =
      sourceConditionalAAH algorithm .f201 := by
  unfold sourceDirectRankMeanConditionalAAH sourceConditionalAAH
  simp_rw [sourceFocalUtility_AAH_f201]
  simpa using
    (sourceHuman_expectation_of_top
      (fun first =>
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterOne algorithm first)))

/-- Direct conditioning when a human follows the first algorithm firm. -/
theorem sourceDirectRankMeanConditionalAAH_f120
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAH algorithm .f120 =
      sourceConditionalAAH algorithm .f120 := by
  unfold sourceDirectRankMeanConditionalAAH sourceConditionalAAH
  simp_rw [sourceFocalUtility_AAH_f120]
  simpa using
    (sourceHuman_expectation_after_one (algorithm 0)
      (fun next =>
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterTwo algorithm (algorithm 0) next)))

/-- Direct conditioning when the human arrives before both algorithm firms. -/
theorem sourceDirectRankMeanConditionalAAH_f210
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAH algorithm .f210 =
      sourceConditionalAAH algorithm .f210 := by
  unfold sourceDirectRankMeanConditionalAAH sourceConditionalAAH
  simp_rw [sourceFocalUtility_AAH_f210]
  simpa using
    (sourceHuman_expectation_of_top
      (fun first =>
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterTwo algorithm first
            (sourceBestAvailableAfterOne algorithm first))))

/-- Every direct AAH conditional expectation is the corresponding collapsed evaluator. -/
theorem sourceDirectRankMeanConditionalAAH_eq_collapsed
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceDirectRankMeanConditionalAAH algorithm order =
      sourceConditionalAAH algorithm order := by
  cases order
  · exact sourceDirectRankMeanConditionalAAH_f012 algorithm
  · exact sourceDirectRankMeanConditionalAAH_f021 algorithm
  · exact sourceDirectRankMeanConditionalAAH_f102 algorithm
  · exact sourceDirectRankMeanConditionalAAH_f120 algorithm
  · exact sourceDirectRankMeanConditionalAAH_f201 algorithm
  · exact sourceDirectRankMeanConditionalAAH_f210 algorithm

/-- The direct AAH finite product expectation is the executable collapsed evaluator. -/
theorem sourceDirectRankMeanExpectedAAH_eq_executable :
    sourceDirectRankMeanExpectedAAH = sourceExecutableExpectedAAH := by
  unfold sourceDirectRankMeanExpectedAAH sourceExecutableExpectedAAH
  simp_rw [sourceDirectRankMeanConditionalAAH_eq_collapsed]

/-- Exact rational evaluation of the direct AAH finite product expectation. -/
theorem sourceDirectRankMeanExpectedAAH_eq :
    sourceDirectRankMeanExpectedAAH = 117110677 / 209459250 := by
  rw [sourceDirectRankMeanExpectedAAH_eq_executable,
    source_executable_expectedAAH_eq]

/-! ## One-algorithm/two-human direct product bridge -/

/-- Joint mass of the focal and opponent independent human-ranking coordinates. -/
def sourceHumanPairProductMass
    (h0 h2 : SourceFourRanking) : ℚ :=
  sourceHumanMallowsMass h0 * sourceHumanMallowsMass h2

/-- The declared two-human finite product mass is normalized. -/
theorem sourceHumanPairProductMass_sum :
    (∑ h0 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        sourceHumanPairProductMass h0 h2) = 1 := by
  unfold sourceHumanPairProductMass
  calc
    (∑ h0 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        sourceHumanMallowsMass h0 * sourceHumanMallowsMass h2) =
        ∑ h0 : SourceFourRanking,
          sourceHumanMallowsMass h0 *
            (∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2) := by
      apply Finset.sum_congr rfl
      intro h0 _
      rw [Finset.mul_sum]
    _ = ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 * 1 := by
      apply Finset.sum_congr rfl
      intro h0 _
      rw [sourceHumanMallowsMass_sum]
    _ = ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 := by
      simp
    _ = 1 := sourceHumanMallowsMass_sum

/--
Direct HAH expectation conditional on the shared algorithm ranking and the
firm-arrival order.  Firm `0` is the focal human ranking `h0`, firm `1` uses
the shared algorithm ranking, and firm `2` is the independent human ranking
`h2`.  The nesting follows the order in which the existing finite transition
lemmas discharge the conditional expectations.
-/
def sourceDirectRankMeanConditionalHAH
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
    ∑ h0 : SourceFourRanking, sourceHumanMallowsMass h0 *
      sourceFocalUtility sourceProfileHAH algorithm
        (sourceHumanRankings h0 .r0123 h2) order

/-- Direct one-algorithm/two-human finite product expectation. -/
def sourceDirectRankMeanExpectedHAH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceDirectRankMeanConditionalHAH algorithm order)

/-- Canonically `h0,h2`-nested direct HAH expectation conditional on an order. -/
def sourceCanonicalDirectRankMeanConditionalHAH
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  ∑ h0 : SourceFourRanking,
    ∑ h2 : SourceFourRanking,
      sourceHumanPairProductMass h0 h2 *
        sourceFocalUtility sourceProfileHAH algorithm
          (sourceHumanRankings h0 .r0123 h2) order

/-- Canonically nested direct one-algorithm/two-human finite product expectation. -/
def sourceCanonicalDirectRankMeanExpectedHAH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceCanonicalDirectRankMeanConditionalHAH algorithm order)

/-- The four-coordinate product law used by the direct HAH expectation is normalized. -/
theorem sourceDirectRankMeanHAHMass_sum :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        (∑ order : SourceFirmOrder,
          sourceUniformFirmOrderMass *
            (∑ h0 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                sourceHumanPairProductMass h0 h2))) = 1 := by
  rw [sourceHumanPairProductMass_sum]
  simp only [mul_one]
  rw [sourceUniformFirmOrderMass_sum]
  simp only [mul_one]
  exact sourceAlgorithmMallowsMass_sum

/-- Finite Fubini puts the opponent human rank outside the focal human rank. -/
private theorem sourceHumanPairProductMass_reverse_h2_h0
    (f : SourceFourRanking → SourceFourRanking → ℚ) :
    (∑ h0 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        sourceHumanPairProductMass h0 h2 * f h0 h2) =
      ∑ h2 : SourceFourRanking,
        sourceHumanMallowsMass h2 *
          (∑ h0 : SourceFourRanking,
            sourceHumanMallowsMass h0 * f h0 h2) := by
  unfold sourceHumanPairProductMass
  calc
    (∑ h0 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        sourceHumanMallowsMass h0 * sourceHumanMallowsMass h2 * f h0 h2) =
        ∑ h2 : SourceFourRanking,
          ∑ h0 : SourceFourRanking,
            sourceHumanMallowsMass h0 * sourceHumanMallowsMass h2 * f h0 h2 := by
      rw [Finset.sum_comm]
    _ = ∑ h2 : SourceFourRanking,
          ∑ h0 : SourceFourRanking,
            sourceHumanMallowsMass h2 *
              (sourceHumanMallowsMass h0 * f h0 h2) := by
      apply Finset.sum_congr rfl
      intro h2 _
      apply Finset.sum_congr rfl
      intro h0 _
      ring
    _ = ∑ h2 : SourceFourRanking,
          sourceHumanMallowsMass h2 *
            (∑ h0 : SourceFourRanking,
              sourceHumanMallowsMass h0 * f h0 h2) := by
      simp_rw [Finset.mul_sum]

private theorem sourceFocalUtility_HAH_f012
    (algorithm h0 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) .f012 =
      sourceExpectedOrderStatisticValue (sourceBestAvailable h0 ∅) := by
  simp [sourceFocalUtility, sourceProfileHAH, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HAH_f021
    (algorithm h0 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) .f021 =
      sourceExpectedOrderStatisticValue (sourceBestAvailable h0 ∅) := by
  simp [sourceFocalUtility, sourceProfileHAH, sourceHumanRankings,
    sourceFirmOrderAt]

private theorem sourceFocalUtility_HAH_f102
    (algorithm h0 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) .f102 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0 {algorithm 0}) := by
  simp [sourceFocalUtility, sourceProfileHAH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_HAH_f120
    (algorithm h0 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) .f120 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0
          {algorithm 0, sourceBestAvailable h2 {algorithm 0}}) := by
  simp [sourceFocalUtility, sourceProfileHAH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_HAH_f201
    (algorithm h0 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) .f201 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0 {sourceBestAvailable h2 ∅}) := by
  simp [sourceFocalUtility, sourceProfileHAH, sourceHumanRankings,
    sourceFirmOrderAt, Fin.ext_iff]

private theorem sourceFocalUtility_HAH_f210
    (algorithm h0 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) .f210 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailable h0
          {sourceBestAvailable h2 ∅,
            sourceBestAvailableAfterOne algorithm
              (sourceBestAvailable h2 ∅)}) := by
  simp [sourceFocalUtility, sourceProfileHAH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton, Fin.ext_iff]

/-- Direct conditioning when the focal human arrives first. -/
theorem sourceDirectRankMeanConditionalHAH_f012
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAH algorithm .f012 =
      sourceConditionalHAH algorithm .f012 := by
  unfold sourceDirectRankMeanConditionalHAH sourceConditionalHAH
  simp_rw [sourceFocalUtility_HAH_f012]
  rw [← sourceHumanExpectedFirstValue_eq_ranking_sum]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning for the other order in which the focal human arrives first. -/
theorem sourceDirectRankMeanConditionalHAH_f021
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAH algorithm .f021 =
      sourceConditionalHAH algorithm .f021 := by
  unfold sourceDirectRankMeanConditionalHAH sourceConditionalHAH
  simp_rw [sourceFocalUtility_HAH_f021]
  rw [← sourceHumanExpectedFirstValue_eq_ranking_sum]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning when the focal human follows the algorithm firm. -/
theorem sourceDirectRankMeanConditionalHAH_f102
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAH algorithm .f102 =
      sourceConditionalHAH algorithm .f102 := by
  unfold sourceDirectRankMeanConditionalHAH sourceConditionalHAH
  simp_rw [sourceFocalUtility_HAH_f102]
  rw [← sourceHumanExpectedAfterOneValue_eq_ranking_sum]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning when a human follows the first algorithm firm. -/
theorem sourceDirectRankMeanConditionalHAH_f120
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAH algorithm .f120 =
      sourceConditionalHAH algorithm .f120 := by
  unfold sourceDirectRankMeanConditionalHAH sourceConditionalHAH
  simp_rw [sourceFocalUtility_HAH_f120]
  simp_rw [← sourceHumanExpectedAfterTwoValue_eq_ranking_sum]
  simpa using
    (sourceHuman_expectation_after_one (algorithm 0)
      (fun next => sourceHumanExpectedAfterTwoValue (algorithm 0) next))

/-- Direct conditioning when the opponent human arrives before the focal human. -/
theorem sourceDirectRankMeanConditionalHAH_f201
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAH algorithm .f201 =
      sourceConditionalHAH algorithm .f201 := by
  unfold sourceDirectRankMeanConditionalHAH sourceConditionalHAH
  simp_rw [sourceFocalUtility_HAH_f201]
  simp_rw [← sourceHumanExpectedAfterOneValue_eq_ranking_sum]
  simpa using
    (sourceHuman_expectation_of_top sourceHumanExpectedAfterOneValue)

/-- Direct conditioning when the opponent human precedes the algorithm firm. -/
theorem sourceDirectRankMeanConditionalHAH_f210
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalHAH algorithm .f210 =
      sourceConditionalHAH algorithm .f210 := by
  unfold sourceDirectRankMeanConditionalHAH sourceConditionalHAH
  simp_rw [sourceFocalUtility_HAH_f210]
  simp_rw [← sourceHumanExpectedAfterTwoValue_eq_ranking_sum]
  simpa using
    (sourceHuman_expectation_of_top
      (fun first =>
        sourceHumanExpectedAfterTwoValue first
          (sourceBestAvailableAfterOne algorithm first)))

/-- Every direct HAH conditional expectation is the corresponding collapsed evaluator. -/
theorem sourceDirectRankMeanConditionalHAH_eq_collapsed
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceDirectRankMeanConditionalHAH algorithm order =
      sourceConditionalHAH algorithm order := by
  cases order
  · exact sourceDirectRankMeanConditionalHAH_f012 algorithm
  · exact sourceDirectRankMeanConditionalHAH_f021 algorithm
  · exact sourceDirectRankMeanConditionalHAH_f102 algorithm
  · exact sourceDirectRankMeanConditionalHAH_f120 algorithm
  · exact sourceDirectRankMeanConditionalHAH_f201 algorithm
  · exact sourceDirectRankMeanConditionalHAH_f210 algorithm

/-- The canonical `h0,h2` nesting is a finite-Fubini rearrangement of the direct form. -/
theorem sourceCanonicalDirectRankMeanConditionalHAH_eq_direct
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceCanonicalDirectRankMeanConditionalHAH algorithm order =
      sourceDirectRankMeanConditionalHAH algorithm order := by
  unfold sourceCanonicalDirectRankMeanConditionalHAH
    sourceDirectRankMeanConditionalHAH
  exact sourceHumanPairProductMass_reverse_h2_h0
    (fun h0 h2 =>
      sourceFocalUtility sourceProfileHAH algorithm
        (sourceHumanRankings h0 .r0123 h2) order)

/-- The direct HAH finite product expectation is the executable collapsed evaluator. -/
theorem sourceDirectRankMeanExpectedHAH_eq_executable :
    sourceDirectRankMeanExpectedHAH = sourceExecutableExpectedHAH := by
  unfold sourceDirectRankMeanExpectedHAH sourceExecutableExpectedHAH
  simp_rw [sourceDirectRankMeanConditionalHAH_eq_collapsed]

/-- The canonical HAH product law is equal to its sequentially nested direct form. -/
theorem sourceCanonicalDirectRankMeanExpectedHAH_eq_direct :
    sourceCanonicalDirectRankMeanExpectedHAH = sourceDirectRankMeanExpectedHAH := by
  unfold sourceCanonicalDirectRankMeanExpectedHAH sourceDirectRankMeanExpectedHAH
  simp_rw [sourceCanonicalDirectRankMeanConditionalHAH_eq_direct]

/-- The canonical HAH finite product expectation is the executable collapsed evaluator. -/
theorem sourceCanonicalDirectRankMeanExpectedHAH_eq_executable :
    sourceCanonicalDirectRankMeanExpectedHAH = sourceExecutableExpectedHAH := by
  rw [sourceCanonicalDirectRankMeanExpectedHAH_eq_direct,
    sourceDirectRankMeanExpectedHAH_eq_executable]

/-- Exact rational evaluation of the direct HAH finite product expectation. -/
theorem sourceDirectRankMeanExpectedHAH_eq :
    sourceDirectRankMeanExpectedHAH =
      2539918857979 / 4642664276250 := by
  rw [sourceDirectRankMeanExpectedHAH_eq_executable,
    source_executable_expectedHAH_eq]

/-! ## One-algorithm/two-human focal-algorithm product bridge -/

/--
Direct AHH expectation conditional on the shared focal algorithm ranking and
the firm-arrival order.  Firms `1` and `2` independently draw human rankings.
The nesting follows the two human arrivals whenever that makes the transition
law explicit; the canonical product form below proves this is still the same
finite product law.
-/
def sourceDirectRankMeanConditionalAHH
    (algorithm : SourceFourRanking) : SourceFirmOrder → ℚ
  | .f012 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          sourceFocalUtility sourceProfileAHH algorithm
            (sourceHumanRankings .r0123 h1 h2) .f012
  | .f021 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          sourceFocalUtility sourceProfileAHH algorithm
            (sourceHumanRankings .r0123 h1 h2) .f021
  | .f102 =>
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          sourceFocalUtility sourceProfileAHH algorithm
            (sourceHumanRankings .r0123 h1 h2) .f102
  | .f120 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          sourceFocalUtility sourceProfileAHH algorithm
            (sourceHumanRankings .r0123 h1 h2) .f120
  | .f201 =>
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          sourceFocalUtility sourceProfileAHH algorithm
            (sourceHumanRankings .r0123 h1 h2) .f201
  | .f210 =>
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          sourceFocalUtility sourceProfileAHH algorithm
            (sourceHumanRankings .r0123 h1 h2) .f210

/-- Direct focal-algorithm finite product expectation against two human firms. -/
def sourceDirectRankMeanExpectedAHH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceDirectRankMeanConditionalAHH algorithm order)

/--
Canonical `h1,h2`-nested form of the same focal-algorithm expectation.  Its
mass names the two independent human-ranking coordinates explicitly.
-/
def sourceCanonicalDirectRankMeanConditionalAHH
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  ∑ h1 : SourceFourRanking,
    ∑ h2 : SourceFourRanking,
      sourceHumanPairProductMass h1 h2 *
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) order

/-- Canonically nested direct focal-algorithm finite product expectation. -/
def sourceCanonicalDirectRankMeanExpectedAHH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceCanonicalDirectRankMeanConditionalAHH algorithm order)

/-- The four-coordinate AHH product law (algorithm, order, and two humans) is normalized. -/
theorem sourceDirectRankMeanAHHMass_sum :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        (∑ order : SourceFirmOrder,
          sourceUniformFirmOrderMass *
            (∑ h1 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                sourceHumanPairProductMass h1 h2))) = 1 := by
  rw [sourceHumanPairProductMass_sum]
  simp only [mul_one]
  rw [sourceUniformFirmOrderMass_sum]
  simp only [mul_one]
  exact sourceAlgorithmMallowsMass_sum

/-- Finite Fubini in the canonical `h1,h2` nesting. -/
private theorem sourceHumanPairProductMass_forward_h1_h2
    (f : SourceFourRanking → SourceFourRanking → ℚ) :
    (∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        sourceHumanPairProductMass h1 h2 * f h1 h2) =
      ∑ h1 : SourceFourRanking,
        sourceHumanMallowsMass h1 *
          (∑ h2 : SourceFourRanking,
            sourceHumanMallowsMass h2 * f h1 h2) := by
  unfold sourceHumanPairProductMass
  apply Finset.sum_congr rfl
  intro h1 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h2 _
  ring

private theorem sourceFocalUtility_AHH_f012
    (algorithm h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) .f012 =
      sourceExpectedOrderStatisticValue (algorithm 0) := by
  simp [sourceFocalUtility, sourceProfileAHH,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_AHH_f021
    (algorithm h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) .f021 =
      sourceExpectedOrderStatisticValue (algorithm 0) := by
  simp [sourceFocalUtility, sourceProfileAHH,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_AHH_f102
    (algorithm h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) .f102 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterOne algorithm (sourceBestAvailable h1 ∅)) := by
  simp [sourceFocalUtility, sourceProfileAHH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton]

private theorem sourceFocalUtility_AHH_f120
    (algorithm h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) .f120 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h1 ∅)
          (sourceBestAvailable h2 {sourceBestAvailable h1 ∅})) := by
  simp [sourceFocalUtility, sourceProfileAHH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton,
    sourceBestAvailable_pair]

private theorem sourceFocalUtility_AHH_f201
    (algorithm h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) .f201 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterOne algorithm (sourceBestAvailable h2 ∅)) := by
  simp [sourceFocalUtility, sourceProfileAHH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton]

private theorem sourceFocalUtility_AHH_f210
    (algorithm h1 h2 : SourceFourRanking) :
    sourceFocalUtility sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) .f210 =
      sourceExpectedOrderStatisticValue
        (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h2 ∅)
          (sourceBestAvailable h1 {sourceBestAvailable h2 ∅})) := by
  simp [sourceFocalUtility, sourceProfileAHH, sourceHumanRankings,
    sourceFirmOrderAt, sourceBestAvailable_singleton,
    sourceBestAvailable_pair]

/-- Direct conditioning when the focal algorithm arrives first. -/
theorem sourceDirectRankMeanConditionalAHH_f012
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAHH algorithm .f012 =
      sourceConditionalAHH algorithm .f012 := by
  unfold sourceDirectRankMeanConditionalAHH sourceConditionalAHH
  simp_rw [sourceFocalUtility_AHH_f012]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  simp
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning for the other arrival order in which the focal algorithm is first. -/
theorem sourceDirectRankMeanConditionalAHH_f021
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAHH algorithm .f021 =
      sourceConditionalAHH algorithm .f021 := by
  unfold sourceDirectRankMeanConditionalAHH sourceConditionalAHH
  simp_rw [sourceFocalUtility_AHH_f021]
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  simp
  rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
  norm_num

/-- Direct conditioning after human firm `1` makes the first selection. -/
theorem sourceDirectRankMeanConditionalAHH_f102
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAHH algorithm .f102 =
      sourceConditionalAHH algorithm .f102 := by
  unfold sourceDirectRankMeanConditionalAHH sourceConditionalAHH
  simp_rw [sourceFocalUtility_AHH_f102]
  calc
    (∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterOne algorithm (sourceBestAvailable h1 ∅))) =
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          (∑ first : SourceFourCandidate,
            sourceHumanTopCandidateMass first *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterOne algorithm first)) := by
      apply Finset.sum_congr rfl
      intro h2 _
      congr 1
      exact sourceHuman_expectation_of_top
        (fun first =>
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterOne algorithm first))
    _ = ∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceExpectedOrderStatisticValue
              (sourceBestAvailableAfterOne algorithm first) := by
      rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
      norm_num

/-- Direct conditioning after the two human firms arrive in the order `1,2`. -/
theorem sourceDirectRankMeanConditionalAHH_f120
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAHH algorithm .f120 =
      sourceConditionalAHH algorithm .f120 := by
  unfold sourceDirectRankMeanConditionalAHH sourceConditionalAHH
  simp_rw [sourceFocalUtility_AHH_f120]
  calc
    (∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h1 ∅)
            (sourceBestAvailable h2 {sourceBestAvailable h1 ∅}))) =
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          (∑ next : SourceFourCandidate,
            sourceHumanNextCandidateMass (sourceBestAvailable h1 ∅) next *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h1 ∅) next)) := by
      apply Finset.sum_congr rfl
      intro h1 _
      congr 1
      exact sourceHuman_expectation_after_one (sourceBestAvailable h1 ∅)
        (fun next =>
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h1 ∅) next))
    _ = ∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            (∑ next : SourceFourCandidate,
              sourceHumanNextCandidateMass first next *
                sourceExpectedOrderStatisticValue
                  (sourceBestAvailableAfterTwo algorithm first next)) := by
      exact sourceHuman_expectation_of_top
        (fun first =>
          ∑ next : SourceFourCandidate,
            sourceHumanNextCandidateMass first next *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterTwo algorithm first next))

/-- Direct conditioning after human firm `2` makes the first selection. -/
theorem sourceDirectRankMeanConditionalAHH_f201
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAHH algorithm .f201 =
      sourceConditionalAHH algorithm .f201 := by
  unfold sourceDirectRankMeanConditionalAHH sourceConditionalAHH
  simp_rw [sourceFocalUtility_AHH_f201]
  calc
    (∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
      ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterOne algorithm (sourceBestAvailable h2 ∅))) =
        ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
          (∑ first : SourceFourCandidate,
            sourceHumanTopCandidateMass first *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterOne algorithm first)) := by
      apply Finset.sum_congr rfl
      intro h1 _
      congr 1
      exact sourceHuman_expectation_of_top
        (fun first =>
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterOne algorithm first))
    _ = ∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceExpectedOrderStatisticValue
              (sourceBestAvailableAfterOne algorithm first) := by
      rw [← Finset.sum_mul, sourceHumanMallowsMass_sum]
      norm_num

/-- Direct conditioning after the two human firms arrive in the order `2,1`. -/
theorem sourceDirectRankMeanConditionalAHH_f210
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAHH algorithm .f210 =
      sourceConditionalAHH algorithm .f210 := by
  unfold sourceDirectRankMeanConditionalAHH sourceConditionalAHH
  simp_rw [sourceFocalUtility_AHH_f210]
  calc
    (∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
      ∑ h1 : SourceFourRanking, sourceHumanMallowsMass h1 *
        sourceExpectedOrderStatisticValue
          (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h2 ∅)
            (sourceBestAvailable h1 {sourceBestAvailable h2 ∅}))) =
        ∑ h2 : SourceFourRanking, sourceHumanMallowsMass h2 *
          (∑ next : SourceFourCandidate,
            sourceHumanNextCandidateMass (sourceBestAvailable h2 ∅) next *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h2 ∅) next)) := by
      apply Finset.sum_congr rfl
      intro h2 _
      congr 1
      exact sourceHuman_expectation_after_one (sourceBestAvailable h2 ∅)
        (fun next =>
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo algorithm (sourceBestAvailable h2 ∅) next))
    _ = ∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            (∑ next : SourceFourCandidate,
              sourceHumanNextCandidateMass first next *
                sourceExpectedOrderStatisticValue
                  (sourceBestAvailableAfterTwo algorithm first next)) := by
      exact sourceHuman_expectation_of_top
        (fun first =>
          ∑ next : SourceFourCandidate,
            sourceHumanNextCandidateMass first next *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterTwo algorithm first next))

/-- Every direct AHH conditional expectation is the corresponding collapsed evaluator. -/
theorem sourceDirectRankMeanConditionalAHH_eq_collapsed
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceDirectRankMeanConditionalAHH algorithm order =
      sourceConditionalAHH algorithm order := by
  cases order
  · exact sourceDirectRankMeanConditionalAHH_f012 algorithm
  · exact sourceDirectRankMeanConditionalAHH_f021 algorithm
  · exact sourceDirectRankMeanConditionalAHH_f102 algorithm
  · exact sourceDirectRankMeanConditionalAHH_f120 algorithm
  · exact sourceDirectRankMeanConditionalAHH_f201 algorithm
  · exact sourceDirectRankMeanConditionalAHH_f210 algorithm

/-- The canonical AHH law is a finite-Fubini rearrangement of the direct nesting. -/
theorem sourceCanonicalDirectRankMeanConditionalAHH_eq_direct
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceCanonicalDirectRankMeanConditionalAHH algorithm order =
      sourceDirectRankMeanConditionalAHH algorithm order := by
  cases order
  · unfold sourceCanonicalDirectRankMeanConditionalAHH
      sourceDirectRankMeanConditionalAHH
    exact sourceHumanPairProductMass_forward_h1_h2
      (fun h1 h2 =>
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) .f012)
  · unfold sourceCanonicalDirectRankMeanConditionalAHH
      sourceDirectRankMeanConditionalAHH
    exact sourceHumanPairProductMass_forward_h1_h2
      (fun h1 h2 =>
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) .f021)
  · unfold sourceCanonicalDirectRankMeanConditionalAHH
      sourceDirectRankMeanConditionalAHH
    exact sourceHumanPairProductMass_reverse_h2_h0
      (fun h1 h2 =>
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) .f102)
  · unfold sourceCanonicalDirectRankMeanConditionalAHH
      sourceDirectRankMeanConditionalAHH
    exact sourceHumanPairProductMass_forward_h1_h2
      (fun h1 h2 =>
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) .f120)
  · unfold sourceCanonicalDirectRankMeanConditionalAHH
      sourceDirectRankMeanConditionalAHH
    exact sourceHumanPairProductMass_forward_h1_h2
      (fun h1 h2 =>
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) .f201)
  · unfold sourceCanonicalDirectRankMeanConditionalAHH
      sourceDirectRankMeanConditionalAHH
    exact sourceHumanPairProductMass_reverse_h2_h0
      (fun h1 h2 =>
        sourceFocalUtility sourceProfileAHH algorithm
          (sourceHumanRankings .r0123 h1 h2) .f210)

/-- The direct AHH finite product expectation is the executable collapsed evaluator. -/
theorem sourceDirectRankMeanExpectedAHH_eq_executable :
    sourceDirectRankMeanExpectedAHH = sourceExecutableExpectedAHH := by
  unfold sourceDirectRankMeanExpectedAHH sourceExecutableExpectedAHH
  simp_rw [sourceDirectRankMeanConditionalAHH_eq_collapsed]

/-- The canonical AHH product law equals its sequentially nested direct form. -/
theorem sourceCanonicalDirectRankMeanExpectedAHH_eq_direct :
    sourceCanonicalDirectRankMeanExpectedAHH = sourceDirectRankMeanExpectedAHH := by
  unfold sourceCanonicalDirectRankMeanExpectedAHH sourceDirectRankMeanExpectedAHH
  simp_rw [sourceCanonicalDirectRankMeanConditionalAHH_eq_direct]

/-- The canonical AHH product expectation is the executable collapsed evaluator. -/
theorem sourceCanonicalDirectRankMeanExpectedAHH_eq_executable :
    sourceCanonicalDirectRankMeanExpectedAHH = sourceExecutableExpectedAHH := by
  rw [sourceCanonicalDirectRankMeanExpectedAHH_eq_direct,
    sourceDirectRankMeanExpectedAHH_eq_executable]

/-- Exact rational evaluation of the direct focal-algorithm rank-mean expectation. -/
theorem sourceDirectRankMeanExpectedAHH_eq :
    sourceDirectRankMeanExpectedAHH = 42778976113 / 74881681875 := by
  rw [sourceDirectRankMeanExpectedAHH_eq_executable,
    source_executable_expectedAHH_eq]

/-! ## Shared-algorithm direct product bridge -/

/--
The ranking map for an all-algorithm profile.  Every firm reads the one sampled
algorithm ranking; it is deliberately not a product of independently sampled
algorithm rankings.
-/
def sourceSharedAlgorithmRankings (algorithm : SourceFourRanking) :
    SourceThreeFirm → SourceFourRanking := fun _ => algorithm

/--
Joint finite mass for the all-algorithm direct model: one shared algorithm
ranking and one independently sampled uniform firm-arrival order.
-/
def sourceDirectRankMeanAAAJointMass
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  sourceAlgorithmMallowsMass algorithm * sourceUniformFirmOrderMass

/--
Direct all-algorithm rank-mean payoff after the shared ranking and arrival
order have been sampled.  The third argument supplies the same shared ranking
at every firm; `sourceProfileAAA` selects that common ranking at all three
sequential arrivals.
-/
def sourceDirectRankMeanConditionalAAA
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  sourceFocalUtility sourceProfileAAA algorithm
    (sourceSharedAlgorithmRankings algorithm) order

/-- Direct all-algorithm finite expectation under the explicit shared-ranking law. -/
def sourceDirectRankMeanExpectedAAA : ℚ :=
  ∑ algorithm : SourceFourRanking,
    ∑ order : SourceFirmOrder,
      sourceDirectRankMeanAAAJointMass algorithm order *
        sourceDirectRankMeanConditionalAAA algorithm order

/-- The shared-ranking/all-orders direct finite law has total mass one. -/
theorem sourceDirectRankMeanAAAJointMass_sum :
    (∑ algorithm : SourceFourRanking,
      ∑ order : SourceFirmOrder,
        sourceDirectRankMeanAAAJointMass algorithm order) = 1 := by
  unfold sourceDirectRankMeanAAAJointMass
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ order : SourceFirmOrder,
        sourceAlgorithmMallowsMass algorithm * sourceUniformFirmOrderMass) =
        ∑ algorithm : SourceFourRanking,
          sourceAlgorithmMallowsMass algorithm *
            (∑ order : SourceFirmOrder, sourceUniformFirmOrderMass) := by
      apply Finset.sum_congr rfl
      intro algorithm _
      rw [Finset.mul_sum]
    _ = ∑ algorithm : SourceFourRanking, sourceAlgorithmMallowsMass algorithm := by
      rw [sourceUniformFirmOrderMass_sum]
      simp
    _ = 1 := sourceAlgorithmMallowsMass_sum

private theorem sourceFocalUtility_AAA_f012
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAA algorithm .f012 =
      sourceExpectedOrderStatisticValue (algorithm 0) := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_AAA_f021
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAA algorithm .f021 =
      sourceExpectedOrderStatisticValue (algorithm 0) := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA,
    sourceFirmOrderAt, sourceBestAvailable_empty]

private theorem sourceFocalUtility_AAA_f102
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAA algorithm .f102 =
      sourceExpectedOrderStatisticValue (algorithm 1) := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first]

/-- The shared algorithm's third choice is its third-ranked candidate. -/
private theorem sourceAlgorithmBestAvailable_after_two
    (algorithm : SourceFourRanking) :
    sourceBestAvailable algorithm {algorithm 0, algorithm 1} = algorithm 2 := by
  cases algorithm <;> decide

private theorem sourceFocalUtility_AAA_f120
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAA algorithm .f120 =
      sourceExpectedOrderStatisticValue (algorithm 2) := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first, sourceAlgorithmBestAvailable_after_two]

private theorem sourceFocalUtility_AAA_f201
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAA algorithm .f201 =
      sourceExpectedOrderStatisticValue (algorithm 1) := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first]

private theorem sourceFocalUtility_AAA_f210
    (algorithm : SourceFourRanking) :
    sourceDirectRankMeanConditionalAAA algorithm .f210 =
      sourceExpectedOrderStatisticValue (algorithm 2) := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA,
    sourceFirmOrderAt, sourceBestAvailable_empty,
    sourceAlgorithmBestAvailable_after_first, sourceAlgorithmBestAvailable_after_two]

/-- Every direct all-algorithm conditional payoff is its collapsed evaluator. -/
theorem sourceDirectRankMeanConditionalAAA_eq_collapsed
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceDirectRankMeanConditionalAAA algorithm order =
      sourceConditionalAAA algorithm order := by
  cases order
  · exact sourceFocalUtility_AAA_f012 algorithm
  · exact sourceFocalUtility_AAA_f021 algorithm
  · exact sourceFocalUtility_AAA_f102 algorithm
  · exact sourceFocalUtility_AAA_f120 algorithm
  · exact sourceFocalUtility_AAA_f201 algorithm
  · exact sourceFocalUtility_AAA_f210 algorithm

/-- The direct shared-ranking AAA expectation equals the collapsed executable evaluator. -/
theorem sourceDirectRankMeanExpectedAAA_eq_executable :
    sourceDirectRankMeanExpectedAAA = sourceExecutableExpectedAAA := by
  unfold sourceDirectRankMeanExpectedAAA sourceDirectRankMeanAAAJointMass
    sourceExecutableExpectedAAA
  simp_rw [sourceDirectRankMeanConditionalAAA_eq_collapsed]
  apply Finset.sum_congr rfl
  intro algorithm _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order _
  ring

/-- Exact rational evaluation of the direct shared-ranking AAA finite expectation. -/
theorem sourceDirectRankMeanExpectedAAA_eq :
    sourceDirectRankMeanExpectedAAA = 124 / 225 := by
  rw [sourceDirectRankMeanExpectedAAA_eq_executable,
    source_executable_expectedAAA_eq]

end KR21Monoculture
