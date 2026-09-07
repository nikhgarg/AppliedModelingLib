import FalahatgarEtAl2017MaxingRanking.CanonicalPruneChernoff

/-!
# Canonical full Prune-round coupling

For an adaptive Prune execution it is convenient to draw a fresh batch for
every arm and then read only the currently active ones.  This module proves
that the source bad-survivor Chernoff tail remains valid under that finite
full-arm coupling; the unqueried coordinates are never consulted.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
The Prune decision obtained by looking up an arm in a batch for all arms.
It agrees with the source decision on every arm that is currently active.
-/
noncomputable def canonicalFullPruneRoundDecision {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (lower upper eta : ℝ)
    (batchTable : ↑(Finset.univ : Finset Arm) →
      Fin (fixedSampleBudget lower upper eta) → Bool) (arm : Arm) : CompareDecision :=
  canonicalPruneRoundDecision Finset.univ lower upper eta batchTable arm

/--
The finite Chernoff bad-survivor tail under a full-arm Bernoulli batch.
Restricting the resulting decision to `active` is a coupling of the source
round: every used arm has its same independent source batch, while the other
coordinates are ignored.
-/
theorem canonicalFullPruneRound_badSurvivorCard_probability_exponential
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper eta threshold t : ℝ)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) (ht : 0 ≤ t) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable | threshold ≤
        (((pruneRound active
          (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-t * threshold +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta)) := by
  classical
  let badActive : Finset Arm := active.filter fun arm => preferenceGap arm anchor ≤ lower
  let embed : badActive → (Finset.univ : Finset Arm) := fun arm =>
    ⟨arm.val, Finset.mem_univ _⟩
  let law := (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
    (fixedSampleBudget lower upper eta)).toMeasure
  letI : IsProbabilityMeasure law := by
    dsimp [law]
    infer_instance
  let survival : badActive →
      (↑(Finset.univ : Finset Arm) → Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ :=
      fun arm batchTable =>
        if canonicalFullPruneRoundDecision lower upper eta batchTable arm.val = .upper
          then 1 else 0
  have hembed : Function.Injective embed := by
    intro first second hequal
    apply Subtype.ext
    exact congrArg (fun arm : (Finset.univ : Finset Arm) => arm.val) hequal
  have hsurvivalFunction : survival = fun arm =>
      canonicalPruneRoundUpperSurvival Finset.univ lower upper eta (embed arm) := by
    funext arm batchTable
    simp [survival, embed, canonicalFullPruneRoundDecision,
      canonicalPruneRoundDecision, canonicalPruneRoundUpperSurvival]
  have hindependent : iIndepFun survival law := by
    rw [hsurvivalFunction]
    simpa [law] using
      (iIndepFun_canonicalPruneRoundUpperSurvival preferenceGap hprobability Finset.univ anchor
        lower upper eta).precomp hembed
  have hmeasurable : ∀ arm, Measurable (survival arm) := by
    rw [hsurvivalFunction]
    intro arm
    exact measurable_canonicalPruneRoundUpperSurvival Finset.univ lower upper eta (embed arm)
  have hmeanBound : ∀ arm, law[survival arm] ≤ eta := by
    rw [hsurvivalFunction]
    intro arm
    apply integral_canonicalPruneRoundUpperSurvival_le preferenceGap hprobability Finset.univ
      anchor lower upper eta (embed arm)
    · exact (Finset.mem_filter.mp arm.property).2
    · exact hseparation
    · exact heta
    · exact hetaLeOne
  have hindicator : ∀ arm batchTable, survival arm batchTable = 0 ∨ survival arm batchTable = 1 := by
    intro arm batchTable
    unfold survival
    split <;> simp
  have hcard : ∀ batchTable,
      (((pruneRound active
        (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
        fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) =
        ∑ arm, survival arm batchTable := by
    intro batchTable
    change
      (((pruneRound active
        (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
        fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) =
        ∑ arm : badActive,
          if canonicalFullPruneRoundDecision lower upper eta batchTable arm.val = .upper
            then 1 else 0
    rw [← Finset.sum_subtype badActive (by simp)
      (fun arm => if canonicalFullPruneRoundDecision lower upper eta batchTable arm = .upper
        then 1 else 0)]
    rw [Finset.sum_boole]
    congr 1
    simp [badActive, pruneRound, Finset.filter_filter, and_comm]
  have htail := independentIndicatorSum_ge_probability_exponential law survival eta threshold t
    hindependent hmeasurable hindicator hmeanBound ht
  change law.real {batchTable | threshold ≤
    (((pruneRound active
      (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
      fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-t * threshold +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta))
  calc
    law.real {batchTable | threshold ≤
        (((pruneRound active
          (canonicalFullPruneRoundDecision lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} =
        law.real {batchTable | threshold ≤ ∑ arm, survival arm batchTable} := by
          congr 1
          ext batchTable
          simp only [Set.mem_setOf_eq]
          rw [hcard batchTable]
    _ ≤ Real.exp (-t * threshold +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta)) := by
      rw [Fintype.card_coe] at htail
      simpa [badActive] using htail

/--
Under the full-arm coupling, an arm whose gap above the anchor meets the
upper Compare threshold is incorrectly removed with probability at most
`eta`.  This is the per-round retention input for the source Prune loop.
-/
theorem canonicalFullPruneRound_upper_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor arm : Arm) (lower upper eta : ℝ)
    (hgap : upper ≤ preferenceGap arm anchor)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        canonicalFullPruneRoundDecision lower upper eta batchTable arm ≠ .upper} ≤ eta := by
  let batchObservation : ℕ → (Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ :=
    fun sampleIndex batch =>
      canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta) sampleIndex batch
  let failureEvent : Set (Fin (fixedSampleBudget lower upper eta) → Bool) := {batch |
    adaptiveCompare batchObservation (fixedSampleBudget lower upper eta)
      lower upper eta batch ≠ .upper}
  let fullLaw := canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
    (fixedSampleBudget lower upper eta)
  let fullArm : (Finset.univ : Finset Arm) := ⟨arm, Finset.mem_univ _⟩
  have hfailureMeasurable : MeasurableSet failureEvent := MeasurableSet.of_discrete
  have hpreimage : {batchTable |
      canonicalFullPruneRoundDecision lower upper eta batchTable arm ≠ .upper} =
      (fun batchTable => batchTable fullArm) ⁻¹' failureEvent := by
    ext batchTable
    simp [canonicalFullPruneRoundDecision, canonicalPruneRoundDecision, failureEvent,
      batchObservation, fullArm]
  have hcoordinate : Measure.map (fun batchTable => batchTable fullArm) fullLaw.toMeasure =
      (canonicalComparisonBatchLaw preferenceGap hprobability arm anchor
        (fixedSampleBudget lower upper eta)).toMeasure := by
    simpa [fullLaw, fullArm] using
      (map_canonicalPruneRoundBatchCoordinate preferenceGap hprobability Finset.univ anchor
        (fixedSampleBudget lower upper eta) fullArm)
  calc
    fullLaw.toMeasure.real {batchTable |
        canonicalFullPruneRoundDecision lower upper eta batchTable arm ≠ .upper} =
        fullLaw.toMeasure.real ((fun batchTable => batchTable fullArm) ⁻¹' failureEvent) := by
          rw [hpreimage]
    _ = (Measure.map (fun batchTable => batchTable fullArm) fullLaw.toMeasure).real
        failureEvent := by
          simp only [measureReal_def]
          rw [Measure.map_apply (measurable_pi_apply fullArm) hfailureMeasurable]
    _ = (canonicalComparisonBatchLaw preferenceGap hprobability arm anchor
        (fixedSampleBudget lower upper eta)).toMeasure.real failureEvent := by
          rw [hcoordinate]
    _ ≤ eta := by
      apply finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget
        (canonicalComparisonBatchLaw preferenceGap hprobability arm anchor
          (fixedSampleBudget lower upper eta)).toMeasure
        batchObservation lower upper (preferenceGap arm anchor) eta
      · simpa [batchObservation] using iIndepFun_canonicalComparisonBatchObservation
          preferenceGap hprobability arm anchor (fixedSampleBudget lower upper eta)
      · intro sampleIndex hsampleIndex
        exact measurable_canonicalComparisonBatchObservation
          (fixedSampleBudget lower upper eta) sampleIndex
      · intro sampleIndex hsampleIndex
        exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
          arm anchor (fixedSampleBudget lower upper eta) sampleIndex
      · intro sampleIndex hsampleIndex
        exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
          arm anchor (fixedSampleBudget lower upper eta) sampleIndex hsampleIndex
      · exact hgap
      · exact hseparation
      · exact heta
      · exact hetaLeOne

end FalahatgarEtAl2017MaxingRanking
