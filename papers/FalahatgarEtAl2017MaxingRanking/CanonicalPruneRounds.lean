import FalahatgarEtAl2017MaxingRanking.FiniteBatchPruneProbability
import FalahatgarEtAl2017MaxingRanking.CanonicalComparisonBatches

/-!
# Canonical finite Prune-round schedule

Prune's active set is selected by preceding rounds.  This file uses one finite
product coupling for every initially available arm, scheduled round, and
within-call sample.  A realized Prune execution reads only coordinates for
active arms; the unused finite coordinates make the conditional fresh-batch
law available without introducing an infinite comparison stream.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory

universe u

/-- A coordinate is one scheduled sample of one arm's comparison with a fixed anchor. -/
def canonicalPruneRoundsCoordinate {Arm : Type u} [Fintype Arm]
    (roundCount : ℕ) (lower upper delta : ℝ) : Type u :=
  Σ round : Fin roundCount, Arm × Fin (fixedSampleBudget lower upper
    (adaptivePruneRoundDelta delta round.val))

noncomputable instance canonicalPruneRoundsCoordinateFintype {Arm : Type u} [Fintype Arm]
    (roundCount : ℕ) (lower upper delta : ℝ) :
    Fintype (canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta) := by
  unfold canonicalPruneRoundsCoordinate
  infer_instance

/-- The finite product of all Bernoulli labels that a scheduled Prune execution can read. -/
noncomputable def canonicalPruneRoundsLabelLaw {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) :
    PMF (canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta → Bool) := by
  let marginal : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta →
      Measure Bool := fun coordinate =>
    (realBernoulliPMF (centeredComparisonProbability preferenceGap coordinate.2.1 anchor)
      (hprobability coordinate.2.1 anchor).1 (hprobability coordinate.2.1 anchor).2).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The PMF schedule has exactly its displayed heterogeneous product measure. -/
theorem canonicalPruneRoundsLabelLaw_toMeasure {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) :
    (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure =
      Measure.pi (fun coordinate : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta =>
        (realBernoulliPMF (centeredComparisonProbability preferenceGap coordinate.2.1 anchor)
          (hprobability coordinate.2.1 anchor).1
          (hprobability coordinate.2.1 anchor).2).toMeasure) := by
  let marginal : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta →
      Measure Bool := fun coordinate =>
    (realBernoulliPMF (centeredComparisonProbability preferenceGap coordinate.2.1 anchor)
      (hprobability coordinate.2.1 anchor).1 (hprobability coordinate.2.1 anchor).2).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/-- Labels at all scheduled arm/sample coordinates are independent. -/
theorem iIndepFun_canonicalPruneRoundsLabelCoordinate {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) :
    iIndepFun (fun coordinate : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta =>
      fun labelTable => labelTable coordinate)
      (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure := by
  let marginal : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta →
      Measure Bool := fun coordinate =>
    (realBernoulliPMF (centeredComparisonProbability preferenceGap coordinate.2.1 anchor)
      (hprobability coordinate.2.1 anchor).1 (hprobability coordinate.2.1 anchor).2).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  rw [canonicalPruneRoundsLabelLaw_toMeasure]
  simpa only [marginal] using
    (iIndepFun_pi (X := fun _ : canonicalPruneRoundsCoordinate (Arm := Arm)
      roundCount lower upper delta => (id : Bool → Bool))
      (μ := marginal) (fun _ => measurable_id.aemeasurable))

/-- The scheduled-coordinate label has its source Bernoulli marginal. -/
theorem map_canonicalPruneRoundsLabelCoordinate {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ)
    (coordinate : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta) :
    Measure.map (fun labelTable => labelTable coordinate)
      (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure =
        (realBernoulliPMF (centeredComparisonProbability preferenceGap coordinate.2.1 anchor)
          (hprobability coordinate.2.1 anchor).1
          (hprobability coordinate.2.1 anchor).2).toMeasure := by
  rw [canonicalPruneRoundsLabelLaw_toMeasure]
  let marginal : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta →
      Measure Bool := fun index =>
    (realBernoulliPMF (centeredComparisonProbability preferenceGap index.2.1 anchor)
      (hprobability index.2.1 anchor).1 (hprobability index.2.1 anchor).2).toMeasure
  letI : ∀ index, IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun labelTable => labelTable coordinate) (Measure.pi marginal) = marginal coordinate
  exact (measurePreserving_eval marginal coordinate).map_eq

/-- The real-valued observation read by a scheduled Prune comparison. -/
noncomputable def canonicalPruneRoundsObservation {Arm : Type u} [Fintype Arm]
    (roundCount : ℕ) (lower upper delta : ℝ)
    (round : ℕ) (arm : Arm) (sample : ℕ)
    (labelTable : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta → Bool) : ℝ :=
  if hround : round < roundCount then
    if hsample : sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) then
      binaryRatingScore (labelTable ⟨⟨round, hround⟩, (arm, ⟨sample, hsample⟩)⟩)
    else 0
  else 0

/-- At a scheduled in-budget point, the observation is its Boolean score. -/
theorem canonicalPruneRoundsObservation_eq_score {Arm : Type u} [Fintype Arm]
    (roundCount : ℕ) (lower upper delta : ℝ)
    (round : ℕ) (arm : Arm) (sample : ℕ)
    (hround : round < roundCount)
    (hsample : sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))
    (labelTable : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta → Bool) :
    canonicalPruneRoundsObservation roundCount lower upper delta round arm sample labelTable =
      binaryRatingScore (labelTable ⟨⟨round, hround⟩, (arm, ⟨sample, hsample⟩)⟩) := by
  simp [canonicalPruneRoundsObservation, hround, hsample]

/-- Scheduled Prune observations are measurable on the finite label space. -/
theorem measurable_canonicalPruneRoundsObservation {Arm : Type u} [Fintype Arm]
    (roundCount : ℕ) (lower upper delta : ℝ) (round : ℕ) (arm : Arm) (sample : ℕ) :
    Measurable (canonicalPruneRoundsObservation (Arm := Arm)
      roundCount lower upper delta round arm sample) :=
  Measurable.of_discrete

/-- Every scheduled Prune observation lies in the source score interval. -/
theorem canonicalPruneRoundsObservation_mem_Icc {Arm : Type u} [Fintype Arm]
    (roundCount : ℕ) (lower upper delta : ℝ)
    (round : ℕ) (arm : Arm) (sample : ℕ)
    (labelTable : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta → Bool) :
    canonicalPruneRoundsObservation roundCount lower upper delta round arm sample labelTable ∈
      Set.Icc (0 : ℝ) 1 := by
  by_cases hround : round < roundCount
  · by_cases hsample : sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round)
    · rw [canonicalPruneRoundsObservation_eq_score roundCount lower upper delta round arm sample
        hround hsample]
      rcases hvalue : labelTable ⟨⟨round, hround⟩, (arm, ⟨sample, hsample⟩)⟩ with (_ | _)
      · norm_num [binaryRatingScore, hvalue]
      · norm_num [binaryRatingScore, hvalue]
    · simp [canonicalPruneRoundsObservation, hround, hsample]
  · simp [canonicalPruneRoundsObservation, hround]

/-- The in-budget observations for one scheduled arm comparison are independent. -/
theorem iIndepFun_canonicalPruneRoundsObservation {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ)
    (round : ℕ) (hround : round < roundCount) (arm : Arm) :
    iIndepFun (fun sample : Fin (fixedSampleBudget lower upper
      (adaptivePruneRoundDelta delta round)) =>
      canonicalPruneRoundsObservation roundCount lower upper delta round arm sample.val)
      (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure := by
  let coordinate : Fin (fixedSampleBudget lower upper
      (adaptivePruneRoundDelta delta round)) →
      canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta := fun sample =>
    ⟨⟨round, hround⟩, (arm, sample)⟩
  have hcoordinateInjective : Function.Injective coordinate := by
    intro first second hequal
    apply Fin.ext
    exact congrArg (fun index => index.2.2.val) hequal
  have hlabels := (iIndepFun_canonicalPruneRoundsLabelCoordinate preferenceGap hprobability
    roundCount anchor lower upper delta).precomp hcoordinateInjective
  have hscores := hlabels.comp (fun _ => binaryRatingScore) (fun _ => Measurable.of_discrete)
  have hobservations : (fun sample : Fin (fixedSampleBudget lower upper
      (adaptivePruneRoundDelta delta round)) =>
      canonicalPruneRoundsObservation roundCount lower upper delta round arm sample.val) =
      (fun sample labelTable => binaryRatingScore (labelTable (coordinate sample))) := by
    funext sample labelTable
    exact canonicalPruneRoundsObservation_eq_score roundCount lower upper delta round arm sample.val
      hround sample.isLt labelTable
  rw [hobservations]
  exact hscores

/-- A scheduled in-budget observation has its source centered comparison mean. -/
theorem integral_canonicalPruneRoundsObservation {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ)
    (round : ℕ) (hround : round < roundCount) (arm : Arm)
    (sample : Fin (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))) :
    (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure[
      canonicalPruneRoundsObservation roundCount lower upper delta round arm sample.val] =
        1 / 2 + preferenceGap arm anchor := by
  let coordinate : canonicalPruneRoundsCoordinate (Arm := Arm) roundCount lower upper delta :=
    ⟨⟨round, hround⟩, (arm, sample)⟩
  have hscore : canonicalPruneRoundsObservation roundCount lower upper delta round arm sample.val =
      binaryRatingScore ∘ (fun labelTable => labelTable coordinate) := by
    funext labelTable
    simp [coordinate, canonicalPruneRoundsObservation, hround, sample.isLt]
  rw [hscore]
  calc
    (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure[
        binaryRatingScore ∘ (fun labelTable => labelTable coordinate)] =
        (Measure.map (fun labelTable => labelTable coordinate)
          (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure)[
            binaryRatingScore] := by
          symm
          apply integral_map
          · exact (measurable_pi_apply coordinate).aemeasurable
          · exact Measurable.of_discrete.aestronglyMeasurable
    _ = (realBernoulliPMF (centeredComparisonProbability preferenceGap arm anchor)
          (hprobability arm anchor).1 (hprobability arm anchor).2).toMeasure[binaryRatingScore] := by
          rw [map_canonicalPruneRoundsLabelCoordinate preferenceGap hprobability roundCount
            anchor lower upper delta coordinate]
    _ = centeredComparisonProbability preferenceGap arm anchor :=
      integral_realBernoulliPMF_binaryRatingScore
        (centeredComparisonProbability preferenceGap arm anchor)
        (hprobability arm anchor).1 (hprobability arm anchor).2
    _ = 1 / 2 + preferenceGap arm anchor := rfl

/-- The almost-everywhere source score bound for a scheduled observation. -/
theorem ae_canonicalPruneRoundsObservation_mem_Icc {Arm : Type u} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ)
    (round : ℕ) (arm : Arm) (sample : ℕ) :
    ∀ᵐ labelTable ∂(canonicalPruneRoundsLabelLaw preferenceGap hprobability
      roundCount anchor lower upper delta).toMeasure,
      canonicalPruneRoundsObservation roundCount lower upper delta round arm sample labelTable ∈
        Set.Icc (0 : ℝ) 1 :=
  Filter.Eventually.of_forall
    (canonicalPruneRoundsObservation_mem_Icc roundCount lower upper delta round arm sample)

/--
Lemma 13's protected-arm failure bound on the finite coupled Prune schedule.
Although the execution's active set is history-selected, every comparison it
can read has a distinct finite Bernoulli coordinate in the product law above.
-/
theorem canonicalPruneRounds_failure_probability {Arm : Type u} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ)
    (active : Finset Arm) (kept : Arm)
    (hmem : kept ∈ active) (hgap : upper ≤ preferenceGap kept anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure.real
      {labelTable | kept ∉ indexedPruneRounds roundCount
        (adaptivePruneDecision
          (canonicalPruneRoundsObservation (Arm := Arm) roundCount lower upper delta)
          lower upper delta) labelTable active} ≤ delta / 2 := by
  apply finiteBatchAdaptivePrune_failure_probability
    (canonicalPruneRoundsLabelLaw preferenceGap hprobability roundCount anchor lower upper delta).toMeasure
    roundCount (canonicalPruneRoundsObservation (Arm := Arm) roundCount lower upper delta)
    active kept lower upper (preferenceGap kept anchor) delta hmem
  · intro round hround
    exact iIndepFun_canonicalPruneRoundsObservation preferenceGap hprobability roundCount anchor
      lower upper delta round hround kept
  · intro round hround sample hsample
    exact measurable_canonicalPruneRoundsObservation roundCount lower upper delta round kept sample
  · intro round hround sample hsample
    exact ae_canonicalPruneRoundsObservation_mem_Icc preferenceGap hprobability roundCount anchor
      lower upper delta round kept sample
  · intro round hround sample hsample
    simpa using integral_canonicalPruneRoundsObservation preferenceGap hprobability roundCount
      anchor lower upper delta round hround kept ⟨sample, hsample⟩
  · exact hgap
  · exact hseparation
  · exact hdelta
  · exact hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
