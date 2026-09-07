import AppliedModelingLib.Applications.RatingSystems.BinaryLargeDeviations
import AppliedModelingLib.Foundations.Probability.FiniteIID
import FalahatgarEtAl2017MaxingRanking.AdaptiveFreshSeqEliminate

/-!
# Canonical finite comparison batches

The paper's primitive pairwise probabilities induce a Bernoulli law for each
fresh Compare batch. This file constructs the corresponding finite iid PMF.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory

/-- The centered preference probabilities in the paper lie in the unit interval. -/
def CenteredComparisonProbabilities {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) : Prop :=
  ∀ challenger incumbent,
    0 ≤ 1 / 2 + preferenceGap challenger incumbent ∧
      1 / 2 + preferenceGap challenger incumbent ≤ 1

/-- The Bernoulli success probability for one ordered comparison. -/
noncomputable def centeredComparisonProbability {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (challenger incumbent : Arm) : ℝ :=
  1 / 2 + preferenceGap challenger incumbent

/--
The canonical finite iid Boolean batch for comparisons of `challenger` against
`incumbent`.
-/
noncomputable def canonicalComparisonBatchLaw {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize : ℕ) : PMF (Fin batchSize → Bool) := by
  let probability := centeredComparisonProbability preferenceGap challenger incumbent
  let marginal := realBernoulliPMF probability
    (hprobability challenger incumbent).1 (hprobability challenger incumbent).2
  letI : IsProbabilityMeasure marginal.toMeasure := inferInstance
  letI : ∀ _ : Fin batchSize, IsProbabilityMeasure marginal.toMeasure := fun _ => inferInstance
  letI : IsProbabilityMeasure (finiteIIDSampleLaw marginal.toMeasure batchSize) := by
    unfold finiteIIDSampleLaw
    infer_instance
  exact (finiteIIDSampleLaw marginal.toMeasure batchSize).toPMF

/-- The PMF batch has exactly the finite iid product measure used to construct it. -/
theorem canonicalComparisonBatchLaw_toMeasure {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize : ℕ) :
    (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent batchSize).toMeasure =
      finiteIIDSampleLaw
        (realBernoulliPMF
          (centeredComparisonProbability preferenceGap challenger incumbent)
          (hprobability challenger incumbent).1
          (hprobability challenger incumbent).2).toMeasure batchSize := by
  classical
  let probability := centeredComparisonProbability preferenceGap challenger incumbent
  let marginal := realBernoulliPMF probability
    (hprobability challenger incumbent).1 (hprobability challenger incumbent).2
  letI : IsProbabilityMeasure marginal.toMeasure := inferInstance
  letI : ∀ _ : Fin batchSize, IsProbabilityMeasure marginal.toMeasure := fun _ => inferInstance
  letI : IsProbabilityMeasure (finiteIIDSampleLaw marginal.toMeasure batchSize) := by
    unfold finiteIIDSampleLaw
    infer_instance
  change (finiteIIDSampleLaw marginal.toMeasure batchSize).toPMF.toMeasure =
    finiteIIDSampleLaw marginal.toMeasure batchSize
  exact Measure.toPMF_toMeasure _

/-- The real-valued score recorded for a batch coordinate. -/
def canonicalComparisonBatchObservation (batchSize sampleIndex : ℕ)
    (outcome : Fin batchSize → Bool) : ℝ :=
  if hindex : sampleIndex < batchSize then
    binaryRatingScore (outcome ⟨sampleIndex, hindex⟩)
  else 0

/-- In-range observations are the corresponding Boolean success scores. -/
theorem canonicalComparisonBatchObservation_eq_score
    {batchSize sampleIndex : ℕ} (hindex : sampleIndex < batchSize)
    (outcome : Fin batchSize → Bool) :
    canonicalComparisonBatchObservation batchSize sampleIndex outcome =
      binaryRatingScore (outcome ⟨sampleIndex, hindex⟩) := by
  simp [canonicalComparisonBatchObservation, hindex]

/-- Every canonical comparison score lies in the source interval `[0,1]`. -/
theorem canonicalComparisonBatchObservation_mem_Icc
    (batchSize sampleIndex : ℕ) (outcome : Fin batchSize → Bool) :
    canonicalComparisonBatchObservation batchSize sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hindex : sampleIndex < batchSize
  · rw [canonicalComparisonBatchObservation_eq_score hindex]
    rcases hvalue : outcome ⟨sampleIndex, hindex⟩ with (_ | _)
    · norm_num [binaryRatingScore, hvalue]
    · norm_num [binaryRatingScore, hvalue]
  · simp [canonicalComparisonBatchObservation, hindex]

/-- Canonical comparison observations are measurable on the finite batch space. -/
theorem measurable_canonicalComparisonBatchObservation
    (batchSize sampleIndex : ℕ) :
    Measurable (canonicalComparisonBatchObservation batchSize sampleIndex) :=
  Measurable.of_discrete

/-- The Bernoulli score has expectation equal to its success probability. -/
theorem integral_realBernoulliPMF_binaryRatingScore
    (probability : ℝ) (hprobabilityZero : 0 ≤ probability)
    (hprobabilityOne : probability ≤ 1) :
    (realBernoulliPMF probability hprobabilityZero hprobabilityOne).toMeasure[
      binaryRatingScore] = probability := by
  rw [PMF.integral_eq_sum]
  simp [binaryRatingScore, realBernoulliPMF_apply_true_toReal]

/-- The in-budget canonical comparison scores form an independent finite family. -/
theorem iIndepFun_canonicalComparisonBatchObservation
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize : ℕ) :
    iIndepFun (fun sampleIndex : Fin batchSize =>
      canonicalComparisonBatchObservation batchSize sampleIndex.val)
      (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent batchSize).toMeasure := by
  rw [canonicalComparisonBatchLaw_toMeasure]
  convert (iIndepFun_finiteIIDSampleCoordinate
      (realBernoulliPMF
        (centeredComparisonProbability preferenceGap challenger incumbent)
        (hprobability challenger incumbent).1
        (hprobability challenger incumbent).2).toMeasure batchSize).comp
      (fun _ => binaryRatingScore) (fun _ => Measurable.of_discrete) using 1
  funext sampleIndex outcome
  simp [Function.comp_apply, canonicalComparisonBatchObservation, sampleIndex.isLt,
    finiteIIDSampleCoordinate]

/-- Each in-budget canonical score has the paper's centered comparison mean. -/
theorem integral_canonicalComparisonBatchObservation
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize : ℕ) (sampleIndex : Fin batchSize) :
    (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent batchSize).toMeasure[
      canonicalComparisonBatchObservation batchSize sampleIndex.val] =
        1 / 2 + preferenceGap challenger incumbent := by
  rw [canonicalComparisonBatchLaw_toMeasure]
  have hcoordinate : canonicalComparisonBatchObservation batchSize sampleIndex.val =
      binaryRatingScore ∘ finiteIIDSampleCoordinate sampleIndex := by
    funext outcome
    simp [Function.comp_apply, canonicalComparisonBatchObservation, sampleIndex.isLt,
      finiteIIDSampleCoordinate]
  rw [hcoordinate]
  calc
    (finiteIIDSampleLaw
        (realBernoulliPMF
          (centeredComparisonProbability preferenceGap challenger incumbent)
          (hprobability challenger incumbent).1
          (hprobability challenger incumbent).2).toMeasure batchSize)[
        binaryRatingScore ∘ finiteIIDSampleCoordinate sampleIndex] =
        (Measure.map (finiteIIDSampleCoordinate sampleIndex)
          (finiteIIDSampleLaw
            (realBernoulliPMF
              (centeredComparisonProbability preferenceGap challenger incumbent)
              (hprobability challenger incumbent).1
              (hprobability challenger incumbent).2).toMeasure batchSize))[
          binaryRatingScore] := by
      symm
      apply integral_map
      · exact (measurable_finiteIIDSampleCoordinate sampleIndex).aemeasurable
      · exact Measurable.of_discrete.aestronglyMeasurable
    _ = (realBernoulliPMF
          (centeredComparisonProbability preferenceGap challenger incumbent)
          (hprobability challenger incumbent).1
          (hprobability challenger incumbent).2).toMeasure[binaryRatingScore] := by
      rw [map_finiteIIDSampleCoordinate]
    _ = centeredComparisonProbability preferenceGap challenger incumbent :=
      by
        simpa [centeredComparisonProbability] using
          (integral_realBernoulliPMF_binaryRatingScore
            (1 / 2 + preferenceGap challenger incumbent)
            (hprobability challenger incumbent).1 (hprobability challenger incumbent).2)
    _ = 1 / 2 + preferenceGap challenger incumbent := rfl

/-- Every in-range natural-number observation has the stated centered mean. -/
theorem integral_canonicalComparisonBatchObservation_of_lt
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize sampleIndex : ℕ)
    (hsampleIndex : sampleIndex < batchSize) :
    (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent batchSize).toMeasure[
      canonicalComparisonBatchObservation batchSize sampleIndex] =
        1 / 2 + preferenceGap challenger incumbent := by
  simpa using integral_canonicalComparisonBatchObservation preferenceGap hprobability
    challenger incumbent batchSize ⟨sampleIndex, hsampleIndex⟩

/-- The pointwise score bound holds almost everywhere under the canonical batch law. -/
theorem ae_canonicalComparisonBatchObservation_mem_Icc
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize sampleIndex : ℕ) :
    ∀ᵐ outcome ∂(canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent
      batchSize).toMeasure,
      canonicalComparisonBatchObservation batchSize sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1 :=
  Filter.Eventually.of_forall
    (canonicalComparisonBatchObservation_mem_Icc batchSize sampleIndex)

/-- Every finite prefix of a canonical batch remains an independent score family. -/
theorem iIndepFun_canonicalComparisonBatchObservation_prefix
    {Arm : Type*} (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (batchSize prefixSize : ℕ) (hprefix : prefixSize ≤ batchSize) :
    iIndepFun (fun sampleIndex : Fin prefixSize =>
      canonicalComparisonBatchObservation batchSize sampleIndex.val)
      (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent batchSize).toMeasure := by
  simpa using (iIndepFun_canonicalComparisonBatchObservation
    preferenceGap hprobability challenger incumbent batchSize).precomp
      (Fin.castLEEmb hprefix).injective

end FalahatgarEtAl2017MaxingRanking
