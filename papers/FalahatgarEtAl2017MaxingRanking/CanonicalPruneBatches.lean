import FalahatgarEtAl2017MaxingRanking.CanonicalComparisonBatches
import FalahatgarEtAl2017MaxingRanking.FiniteBatchAdaptiveCompareProbability

/-!
# Canonical Prune-round batches

A Prune round compares every currently active arm with one anchor.  The
product law below assigns each active arm its own finite Bernoulli comparison
batch and makes the across-arm independence used by the size argument explicit.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory

/-- The product of the source Bernoulli batches for every active arm in one Prune round. -/
noncomputable def canonicalPruneRoundBatchLaw {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (batchSize : ℕ) :
    PMF (active → Fin batchSize → Bool) := by
  let marginal : active → Measure (Fin batchSize → Bool) := fun arm =>
    (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor batchSize).toMeasure
  letI : ∀ arm : active, IsProbabilityMeasure (marginal arm) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The PMF form has exactly the heterogeneous finite product measure. -/
theorem canonicalPruneRoundBatchLaw_toMeasure {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (batchSize : ℕ) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor batchSize).toMeasure =
      Measure.pi (fun arm : active =>
        (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor batchSize).toMeasure) := by
  classical
  let marginal : active → Measure (Fin batchSize → Bool) := fun arm =>
    (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor batchSize).toMeasure
  letI : ∀ arm : active, IsProbabilityMeasure (marginal arm) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/-- The full batches of different active arms are independent under the canonical round law. -/
theorem iIndepFun_canonicalPruneRoundBatchCoordinate {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (batchSize : ℕ) :
    iIndepFun (fun arm : active => fun batchTable => batchTable arm)
      (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor batchSize).toMeasure := by
  let marginal : active → Measure (Fin batchSize → Bool) := fun arm =>
    (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor batchSize).toMeasure
  letI : ∀ arm : active, IsProbabilityMeasure (marginal arm) := fun _ => inferInstance
  rw [canonicalPruneRoundBatchLaw_toMeasure]
  simpa only [marginal] using
    (iIndepFun_pi (X := fun _ : active => (id : (Fin batchSize → Bool) → Fin batchSize → Bool))
      (μ := marginal) (fun _ => measurable_id.aemeasurable))

/-- Each active-arm batch coordinate has precisely its arm-specific Bernoulli law. -/
theorem map_canonicalPruneRoundBatchCoordinate {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (batchSize : ℕ) (arm : active) :
    Measure.map (fun batchTable => batchTable arm)
      (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor batchSize).toMeasure =
        (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor batchSize).toMeasure := by
  rw [canonicalPruneRoundBatchLaw_toMeasure]
  let marginal : active → Measure (Fin batchSize → Bool) := fun index =>
    (canonicalComparisonBatchLaw preferenceGap hprobability index.val anchor batchSize).toMeasure
  letI : ∀ index : active, IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun batchTable => batchTable arm) (Measure.pi marginal) = marginal arm
  exact (measurePreserving_eval marginal arm).map_eq

/-- The upper-decision indicator for one active arm under its own round batch. -/
noncomputable def canonicalPruneRoundUpperSurvival {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (lower upper eta : ℝ)
    (arm : active) (batchTable : active → Fin (fixedSampleBudget lower upper eta) → Bool) : ℝ :=
  if adaptiveCompare
      (fun sampleIndex batch =>
        canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta) sampleIndex batch)
      (fixedSampleBudget lower upper eta) lower upper eta (batchTable arm) = .upper
    then 1 else 0

/--
The actual source-style Compare decision for one arm in a canonical Prune
round.  Arms outside `active` are assigned `lower` only to make this a total
function; `pruneRound` never consults those values.
-/
noncomputable def canonicalPruneRoundDecision {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (lower upper eta : ℝ)
    (batchTable : active → Fin (fixedSampleBudget lower upper eta) → Bool) (arm : Arm) :
    CompareDecision :=
  if hmem : arm ∈ active then
    adaptiveCompare
      (fun sampleIndex batch =>
        canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta) sampleIndex batch)
      (fixedSampleBudget lower upper eta) lower upper eta (batchTable ⟨arm, hmem⟩)
  else .lower

/-- On an active arm, the total decision is exactly the comparison on that arm's batch. -/
theorem canonicalPruneRoundDecision_apply_mem {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (lower upper eta : ℝ)
    (batchTable : active → Fin (fixedSampleBudget lower upper eta) → Bool) (arm : active) :
    canonicalPruneRoundDecision active lower upper eta batchTable arm.val =
      adaptiveCompare
        (fun sampleIndex batch =>
          canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta) sampleIndex batch)
        (fixedSampleBudget lower upper eta) lower upper eta (batchTable arm) := by
  simp [canonicalPruneRoundDecision, arm.property]

/-- Upper-decision indicators are measurable on the finite product outcome space. -/
theorem measurable_canonicalPruneRoundUpperSurvival {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (lower upper eta : ℝ) (arm : active) :
    Measurable (canonicalPruneRoundUpperSurvival active lower upper eta arm) :=
  Measurable.of_discrete

/-- Every Prune upper-decision indicator is pointwise in the unit interval. -/
theorem canonicalPruneRoundUpperSurvival_mem_Icc {Arm : Type*} [DecidableEq Arm]
    (active : Finset Arm) (lower upper eta : ℝ)
    (arm : active) (batchTable : active → Fin (fixedSampleBudget lower upper eta) → Bool) :
    canonicalPruneRoundUpperSurvival active lower upper eta arm batchTable ∈ Set.Icc (0 : ℝ) 1 := by
  unfold canonicalPruneRoundUpperSurvival
  split <;> norm_num

/-- The armwise upper-decision indicators inherit product-law independence. -/
theorem iIndepFun_canonicalPruneRoundUpperSurvival {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper eta : ℝ) :
    iIndepFun (fun arm : active =>
      canonicalPruneRoundUpperSurvival active lower upper eta arm)
      (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
        (fixedSampleBudget lower upper eta)).toMeasure := by
  have hbatch := iIndepFun_canonicalPruneRoundBatchCoordinate preferenceGap hprobability
    active anchor (fixedSampleBudget lower upper eta)
  let upperIndicator : active → (Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ :=
    fun _ batch => if adaptiveCompare
      (fun sampleIndex value =>
        canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta) sampleIndex value)
      (fixedSampleBudget lower upper eta) lower upper eta batch = .upper then 1 else 0
  have hmeasurable : ∀ arm, Measurable (upperIndicator arm) := fun _ => Measurable.of_discrete
  simpa [upperIndicator, canonicalPruneRoundUpperSurvival, Function.comp_def] using
    hbatch.comp upperIndicator hmeasurable

/-- A threshold-nonbetter active arm survives its canonical Prune batch with probability at most `eta`. -/
theorem integral_canonicalPruneRoundUpperSurvival_le {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper eta : ℝ) (arm : active)
    (hgap : preferenceGap arm.val anchor ≤ lower)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure[
        canonicalPruneRoundUpperSurvival active lower upper eta arm] ≤ eta := by
  let batchObservation : ℕ → (Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ :=
    fun sampleIndex batch =>
      canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta) sampleIndex batch
  let upperEvent : Set (Fin (fixedSampleBudget lower upper eta) → Bool) := {batch |
    adaptiveCompare batchObservation (fixedSampleBudget lower upper eta) lower upper eta batch = .upper}
  let upperIndicator : (Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ :=
    upperEvent.indicator (fun _ => (1 : ℝ))
  have hsurvival : canonicalPruneRoundUpperSurvival active lower upper eta arm =
      upperIndicator ∘ (fun batchTable => batchTable arm) := by
    funext batchTable
    by_cases hupper : adaptiveCompare batchObservation (fixedSampleBudget lower upper eta)
        lower upper eta (batchTable arm) = .upper <;>
      simp [canonicalPruneRoundUpperSurvival, upperIndicator, upperEvent, batchObservation, hupper]
  have hintegral :
      (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
        (fixedSampleBudget lower upper eta)).toMeasure[
          canonicalPruneRoundUpperSurvival active lower upper eta arm] =
        (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor
          (fixedSampleBudget lower upper eta)).toMeasure[upperIndicator] := by
    rw [hsurvival]
    calc
      (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
          (fixedSampleBudget lower upper eta)).toMeasure[
            upperIndicator ∘ (fun batchTable => batchTable arm)] =
          (Measure.map (fun batchTable => batchTable arm)
            (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
              (fixedSampleBudget lower upper eta)).toMeasure)[upperIndicator] := by
            symm
            apply integral_map
            · exact measurable_pi_apply arm |>.aemeasurable
            · exact Measurable.of_discrete.aestronglyMeasurable
      _ = (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor
          (fixedSampleBudget lower upper eta)).toMeasure[upperIndicator] := by
            rw [map_canonicalPruneRoundBatchCoordinate preferenceGap hprobability active anchor
              (fixedSampleBudget lower upper eta) arm]
  rw [hintegral]
  have hupperMeasurable : MeasurableSet upperEvent := MeasurableSet.of_discrete
  have hindicator : upperIndicator = upperEvent.indicator (fun _ => (1 : ℝ)) := rfl
  rw [hindicator]
  change (∫ batch, upperEvent.indicator (1 :
    (Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ) batch ∂
      (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor
        (fixedSampleBudget lower upper eta)).toMeasure) ≤ eta
  rw [integral_indicator_one hupperMeasurable]
  have hfailure := finiteBatchAdaptiveCompare_lower_failure_probability_of_ceilingBudget
    (canonicalComparisonBatchLaw preferenceGap hprobability arm.val anchor
      (fixedSampleBudget lower upper eta)).toMeasure
    batchObservation lower upper (preferenceGap arm.val anchor) eta
    (by
      simpa [batchObservation] using iIndepFun_canonicalComparisonBatchObservation
        preferenceGap hprobability arm.val anchor (fixedSampleBudget lower upper eta))
    (by
      intro sampleIndex hsampleIndex
      exact measurable_canonicalComparisonBatchObservation
        (fixedSampleBudget lower upper eta) sampleIndex)
    (by
      intro sampleIndex hsampleIndex
      exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
        arm.val anchor (fixedSampleBudget lower upper eta) sampleIndex)
    (by
      intro sampleIndex hsampleIndex
      exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
        arm.val anchor (fixedSampleBudget lower upper eta) sampleIndex hsampleIndex)
    hgap hseparation heta hetaLeOne
  have hevent : upperEvent = {batch |
      adaptiveCompare batchObservation (fixedSampleBudget lower upper eta)
        lower upper eta batch ≠ .lower} := by
    ext batch
    simp only [upperEvent, Set.mem_setOf_eq]
    cases adaptiveCompare batchObservation (fixedSampleBudget lower upper eta)
      lower upper eta batch <;> simp
  rw [hevent]
  exact hfailure

end FalahatgarEtAl2017MaxingRanking
