import FalahatgarEtAl2017MaxingRanking.AdaptiveFreshSeqEliminate
import FalahatgarEtAl2017MaxingRanking.FiniteBatchAdaptiveCompareProbability

/-!
# Fresh Seq-Eliminate with finite comparison batches

Each history-selected Compare call receives only its source-budgeted finite
Bernoulli batch.  The results here compose the finite per-call bound over the
fresh adaptive-query execution.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- Theorem 2 for fresh calls with finite, rather than infinite, iid batches. -/
theorem finiteBatchFreshAdaptiveCompareSeqEliminate_epsilonMaximum_probability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ queryIndex < challengers.length, ∀ incumbent,
      iIndepFun (fun sampleIndex : Fin (fixedSampleBudget 0 epsilon eta) =>
        observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex.val)
        (outcomeLaw queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        Measurable (observation queryIndex (challengers.getD queryIndex initial)
          incumbent sampleIndex))
    (hbounded : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        ∀ᵐ outcome ∂(outcomeLaw queryIndex incumbent).toMeasure,
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex outcome ∈
            Set.Icc (0 : ℝ) 1)
    (hmean : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        (outcomeLaw queryIndex incumbent).toMeasure[
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex] =
            1 / 2 + preferenceGap (challengers.getD queryIndex initial) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    1 - (challengers.length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability initial challengers
        outcomeLaw observation preferenceGap epsilon eta := by
  classical
  unfold freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability
  unfold freshAdaptiveCompareSeqEliminateStateLaw
  apply freshSeqEliminate_epsilonMaximum_probability_of_historywiseCallBounds
    initial challengers outcomeLaw
    (fun queryIndex incumbent challenger outcome =>
      adaptiveCompareStep (observation queryIndex)
        (fixedSampleBudget 0 epsilon eta) epsilon eta outcome incumbent challenger)
    (fun queryIndex incumbent outcome =>
      if _ : queryIndex < challengers.length then
        ¬ AdaptiveCompareStepCallValid (observation queryIndex)
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome incumbent
            (challengers.getD queryIndex initial)
      else False)
    preferenceGap epsilon eta hantisymmetric hsst (le_of_lt hepsilon)
    maximum hmaximum happears
  · intro queryIndex hqueryIndex incumbent outcome hnotBad
    simp only [dif_pos hqueryIndex] at hnotBad
    exact Classical.not_not.mp hnotBad
  · intro queryIndex incumbent
    by_cases hqueryIndex : queryIndex < challengers.length
    · simp only [dif_pos hqueryIndex]
      rw [← pmfProbClassical_eq_pmfProb]
      refine finiteBatchAdaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
        (outcomeLaw queryIndex incumbent) (observation queryIndex) preferenceGap epsilon eta
        incumbent (challengers.getD queryIndex initial) ?_ ?_ ?_ ?_ hantisymmetric hself
        hepsilon heta hetaLeOne
      · exact hindependent queryIndex hqueryIndex incumbent
      · exact hmeasurable queryIndex hqueryIndex incumbent
      · exact hbounded queryIndex hqueryIndex incumbent
      · exact hmean queryIndex hqueryIndex incumbent
    · simp only [dif_neg hqueryIndex, pmfProb_false]
      exact le_of_lt heta

/-- The source-local fresh Seq-Eliminate result with finite comparison batches. -/
theorem finiteBatchFreshAdaptiveCompareSeqEliminate_listEpsilonMaximum_probability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ queryIndex < challengers.length, ∀ incumbent,
      iIndepFun (fun sampleIndex : Fin (fixedSampleBudget 0 epsilon eta) =>
        observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex.val)
        (outcomeLaw queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        Measurable (observation queryIndex (challengers.getD queryIndex initial)
          incumbent sampleIndex))
    (hbounded : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        ∀ᵐ outcome ∂(outcomeLaw queryIndex incumbent).toMeasure,
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex outcome ∈
            Set.Icc (0 : ℝ) 1)
    (hmean : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        (outcomeLaw queryIndex incumbent).toMeasure[
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex] =
            1 / 2 + preferenceGap (challengers.getD queryIndex initial) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : ListAbsoluteMaximum preferenceGap maximum initial challengers) :
    1 - (challengers.length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability initial challengers
        outcomeLaw observation preferenceGap epsilon eta := by
  classical
  unfold freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability
  unfold freshAdaptiveCompareSeqEliminateStateLaw
  apply freshSeqEliminate_listEpsilonMaximum_probability_of_historywiseCallBounds
    initial challengers outcomeLaw
    (fun queryIndex incumbent challenger outcome =>
      adaptiveCompareStep (observation queryIndex)
        (fixedSampleBudget 0 epsilon eta) epsilon eta outcome incumbent challenger)
    (fun queryIndex incumbent outcome =>
      if _ : queryIndex < challengers.length then
        ¬ AdaptiveCompareStepCallValid (observation queryIndex)
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome incumbent
            (challengers.getD queryIndex initial)
      else False)
    preferenceGap epsilon eta hantisymmetric hsst (le_of_lt hepsilon)
    maximum hmaximum
  · intro queryIndex hqueryIndex incumbent outcome hnotBad
    simp only [dif_pos hqueryIndex] at hnotBad
    exact Classical.not_not.mp hnotBad
  · intro queryIndex incumbent
    by_cases hqueryIndex : queryIndex < challengers.length
    · simp only [dif_pos hqueryIndex]
      rw [← pmfProbClassical_eq_pmfProb]
      refine finiteBatchAdaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
        (outcomeLaw queryIndex incumbent) (observation queryIndex) preferenceGap epsilon eta
        incumbent (challengers.getD queryIndex initial) ?_ ?_ ?_ ?_ hantisymmetric hself
        hepsilon heta hetaLeOne
      · exact hindependent queryIndex hqueryIndex incumbent
      · exact hmeasurable queryIndex hqueryIndex incumbent
      · exact hbounded queryIndex hqueryIndex incumbent
      · exact hmean queryIndex hqueryIndex incumbent
    · simp only [dif_neg hqueryIndex, pmfProb_false]
      exact le_of_lt heta

/-- The history-dependent source kernel chooses the Bernoulli law for each actual pair. -/
noncomputable def canonicalFreshAdaptiveCompareOutcomeLaw {Arm : Type*}
    (initial : Arm) (challengers : List Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ) :
    AdaptiveOutcomeKernel Arm (Fin (fixedSampleBudget 0 epsilon eta) → Bool) :=
  fun queryIndex incumbent =>
    canonicalComparisonBatchLaw preferenceGap hprobability
      (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta)

/-- The source records each Boolean batch coordinate as its binary comparison score. -/
noncomputable def canonicalFreshAdaptiveCompareObservation {Arm : Type*}
    (epsilon eta : ℝ) :
    ℕ → Arm → Arm → ℕ → (Fin (fixedSampleBudget 0 epsilon eta) → Bool) → ℝ :=
  fun _ _ _ sampleIndex batch =>
    canonicalComparisonBatchObservation (fixedSampleBudget 0 epsilon eta) sampleIndex batch

/-- Theorem 2 under the paper's actual finite Bernoulli fresh-call model. -/
theorem canonicalFreshAdaptiveCompareSeqEliminate_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm]
    (initial : Arm) (challengers : List Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    1 - (challengers.length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability initial challengers
        (canonicalFreshAdaptiveCompareOutcomeLaw initial challengers preferenceGap hprobability
          epsilon eta)
        (canonicalFreshAdaptiveCompareObservation epsilon eta)
        preferenceGap epsilon eta := by
  apply finiteBatchFreshAdaptiveCompareSeqEliminate_epsilonMaximum_probability
    initial challengers
    (canonicalFreshAdaptiveCompareOutcomeLaw initial challengers preferenceGap hprobability
      epsilon eta)
    (canonicalFreshAdaptiveCompareObservation epsilon eta)
    preferenceGap epsilon eta
  · intro queryIndex hqueryIndex incumbent
    simpa [canonicalFreshAdaptiveCompareOutcomeLaw,
      canonicalFreshAdaptiveCompareObservation] using
      iIndepFun_canonicalComparisonBatchObservation preferenceGap hprobability
        (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta)
  · intro queryIndex hqueryIndex incumbent sampleIndex hsampleIndex
    exact measurable_canonicalComparisonBatchObservation
      (fixedSampleBudget 0 epsilon eta) sampleIndex
  · intro queryIndex hqueryIndex incumbent sampleIndex hsampleIndex
    exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
      (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta) sampleIndex
  · intro queryIndex hqueryIndex incumbent sampleIndex hsampleIndex
    exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
      (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta)
      sampleIndex hsampleIndex
  · exact hantisymmetric
  · exact hself
  · exact hsst
  · exact hepsilon
  · exact heta
  · exact hetaLeOne
  · exact hmaximum
  · exact happears

/-- The source-local Seq-Eliminate theorem under the same concrete finite kernel. -/
theorem canonicalFreshAdaptiveCompareSeqEliminate_listEpsilonMaximum_probability
    {Arm : Type*} [Fintype Arm]
    (initial : Arm) (challengers : List Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : ListAbsoluteMaximum preferenceGap maximum initial challengers) :
    1 - (challengers.length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability initial challengers
        (canonicalFreshAdaptiveCompareOutcomeLaw initial challengers preferenceGap hprobability
          epsilon eta)
        (canonicalFreshAdaptiveCompareObservation epsilon eta)
        preferenceGap epsilon eta := by
  apply finiteBatchFreshAdaptiveCompareSeqEliminate_listEpsilonMaximum_probability
    initial challengers
    (canonicalFreshAdaptiveCompareOutcomeLaw initial challengers preferenceGap hprobability
      epsilon eta)
    (canonicalFreshAdaptiveCompareObservation epsilon eta)
    preferenceGap epsilon eta
  · intro queryIndex hqueryIndex incumbent
    simpa [canonicalFreshAdaptiveCompareOutcomeLaw,
      canonicalFreshAdaptiveCompareObservation] using
      iIndepFun_canonicalComparisonBatchObservation preferenceGap hprobability
        (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta)
  · intro queryIndex hqueryIndex incumbent sampleIndex hsampleIndex
    exact measurable_canonicalComparisonBatchObservation
      (fixedSampleBudget 0 epsilon eta) sampleIndex
  · intro queryIndex hqueryIndex incumbent sampleIndex hsampleIndex
    exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
      (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta) sampleIndex
  · intro queryIndex hqueryIndex incumbent sampleIndex hsampleIndex
    exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
      (challengers.getD queryIndex initial) incumbent (fixedSampleBudget 0 epsilon eta)
      sampleIndex hsampleIndex
  · exact hantisymmetric
  · exact hself
  · exact hsst
  · exact hepsilon
  · exact heta
  · exact hetaLeOne
  · exact hmaximum

end FalahatgarEtAl2017MaxingRanking
