import FalahatgarEtAl2017MaxingRanking.BordaProbability
import FalahatgarEtAl2017MaxingRanking.CanonicalComparisonBatches

/-!
# Canonical finite Borda batches

In the Borda procedure, an arm is compared with a uniformly selected opponent
on every trial.  This module turns that two-stage source sampler into a finite
product law over all arm/trial coordinates and proves that the resulting score
has exactly the Borda mean.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The pairwise win probabilities used by the Borda sampler lie in `[0,1]`. -/
def BordaWinProbabilities {Arm : Type*}
    (winProbability : Arm → Arm → ℝ) : Prop :=
  ∀ arm opponent, 0 ≤ winProbability arm opponent ∧
    winProbability arm opponent ≤ 1

/--
One source Borda trial: draw an opponent uniformly and then draw the ordered
comparison outcome against that opponent.
-/
noncomputable def canonicalBordaTrialLaw {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (arm : Arm) : PMF Bool :=
  (uniformPMF Arm).bind fun opponent =>
    realBernoulliPMF (winProbability arm opponent)
      (hprobability arm opponent).1 (hprobability arm opponent).2

/-- A Borda trial's Boolean score has the source Borda expectation. -/
theorem integral_canonicalBordaTrialLaw {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (arm : Arm) :
    (canonicalBordaTrialLaw winProbability hprobability arm).toMeasure[binaryRatingScore] =
      bordaScore winProbability arm := by
  rw [← pmfExp_eq_integral_toMeasure]
  unfold canonicalBordaTrialLaw
  rw [pmfExp_bind]
  simp_rw [pmfExp_eq_integral_toMeasure]
  simp_rw [integral_realBernoulliPMF_binaryRatingScore]
  unfold pmfExp bordaScore
  simp only [uniformPMF_apply_toReal]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

/-- Coordinates in the finite Borda batch: an arm and one of its trials. -/
abbrev canonicalBordaBatchCoordinate (Arm : Type*) (batchSize : ℕ) :=
  Arm × Fin batchSize

/--
The product of the source Borda-trial laws for every arm and trial in a finite
batch.  Different arms may have different Borda marginals, while every trial
of one arm has the same source marginal.
-/
noncomputable def canonicalBordaBatchLaw {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ) :
    PMF (canonicalBordaBatchCoordinate Arm batchSize → Bool) := by
  let marginal : canonicalBordaBatchCoordinate Arm batchSize → Measure Bool := fun coordinate =>
    (canonicalBordaTrialLaw winProbability hprobability coordinate.1).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The PMF batch is exactly the displayed heterogeneous finite product measure. -/
theorem canonicalBordaBatchLaw_toMeasure {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ) :
    (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure =
      Measure.pi (fun coordinate : canonicalBordaBatchCoordinate Arm batchSize =>
        (canonicalBordaTrialLaw winProbability hprobability coordinate.1).toMeasure) := by
  let marginal : canonicalBordaBatchCoordinate Arm batchSize → Measure Bool := fun coordinate =>
    (canonicalBordaTrialLaw winProbability hprobability coordinate.1).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/-- All scheduled Boolean Borda labels are independent under the canonical batch law. -/
theorem iIndepFun_canonicalBordaBatchLabel {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ) :
    iIndepFun (fun coordinate : canonicalBordaBatchCoordinate Arm batchSize =>
      fun labelTable => labelTable coordinate)
      (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure := by
  let marginal : canonicalBordaBatchCoordinate Arm batchSize → Measure Bool := fun coordinate =>
    (canonicalBordaTrialLaw winProbability hprobability coordinate.1).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  rw [canonicalBordaBatchLaw_toMeasure]
  simpa only [marginal] using
    (iIndepFun_pi (X := fun _ : canonicalBordaBatchCoordinate Arm batchSize =>
      (id : Bool → Bool)) (μ := marginal) (fun _ => measurable_id.aemeasurable))

/-- A scheduled Borda label has the trial law for its arm. -/
theorem map_canonicalBordaBatchLabel {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ)
    (coordinate : canonicalBordaBatchCoordinate Arm batchSize) :
    Measure.map (fun labelTable => labelTable coordinate)
      (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure =
        (canonicalBordaTrialLaw winProbability hprobability coordinate.1).toMeasure := by
  rw [canonicalBordaBatchLaw_toMeasure]
  let marginal : canonicalBordaBatchCoordinate Arm batchSize → Measure Bool := fun index =>
    (canonicalBordaTrialLaw winProbability hprobability index.1).toMeasure
  letI : ∀ index, IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun labelTable => labelTable coordinate) (Measure.pi marginal) =
    marginal coordinate
  exact (measurePreserving_eval marginal coordinate).map_eq

/--
The total natural-indexed score observation used by the Borda procedures.
Out-of-budget indices are zero only to keep the observation total; all source
theorems below quantify explicitly over the in-budget prefix.
-/
noncomputable def canonicalBordaBatchObservation {Arm : Type*} (batchSize : ℕ)
    (arm : Arm) (sample : ℕ)
    (labelTable : canonicalBordaBatchCoordinate Arm batchSize → Bool) : ℝ :=
  if hsample : sample < batchSize then
    binaryRatingScore (labelTable (arm, ⟨sample, hsample⟩))
  else 0

/-- At an in-budget sample, the Borda observation is its Boolean score. -/
theorem canonicalBordaBatchObservation_eq_score {Arm : Type*}
    {batchSize sample : ℕ} (arm : Arm) (hsample : sample < batchSize)
    (labelTable : canonicalBordaBatchCoordinate Arm batchSize → Bool) :
    canonicalBordaBatchObservation batchSize arm sample labelTable =
      binaryRatingScore (labelTable (arm, ⟨sample, hsample⟩)) := by
  simp [canonicalBordaBatchObservation, hsample]

/-- Canonical Borda observations are measurable on their finite outcome space. -/
theorem measurable_canonicalBordaBatchObservation {Arm : Type*} [Fintype Arm]
    (batchSize : ℕ) (arm : Arm) (sample : ℕ) :
    Measurable (canonicalBordaBatchObservation (Arm := Arm) batchSize arm sample) :=
  Measurable.of_discrete

/-- Every total Borda observation lies in the binary score interval `[0,1]`. -/
theorem canonicalBordaBatchObservation_mem_Icc {Arm : Type*}
    (batchSize : ℕ) (arm : Arm) (sample : ℕ)
    (labelTable : canonicalBordaBatchCoordinate Arm batchSize → Bool) :
    canonicalBordaBatchObservation batchSize arm sample labelTable ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hsample : sample < batchSize
  · rw [canonicalBordaBatchObservation_eq_score arm hsample]
    rcases hvalue : labelTable (arm, ⟨sample, hsample⟩) with (_ | _)
    · norm_num [binaryRatingScore, hvalue]
    · norm_num [binaryRatingScore, hvalue]
  · simp [canonicalBordaBatchObservation, hsample]

/-- The in-budget observations of every fixed arm are independent. -/
theorem iIndepFun_canonicalBordaBatchObservation {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ) (arm : Arm) :
    iIndepFun (fun sample : Fin batchSize =>
      canonicalBordaBatchObservation batchSize arm sample.val)
      (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure := by
  let coordinate : Fin batchSize → canonicalBordaBatchCoordinate Arm batchSize := fun sample =>
    (arm, sample)
  have hcoordinateInjective : Function.Injective coordinate := by
    intro first second hequal
    exact congrArg Prod.snd hequal
  have hlabels := (iIndepFun_canonicalBordaBatchLabel winProbability hprobability batchSize).precomp
    hcoordinateInjective
  have hscores := hlabels.comp (fun _ => binaryRatingScore) (fun _ => Measurable.of_discrete)
  have hobservations : (fun sample : Fin batchSize =>
      canonicalBordaBatchObservation batchSize arm sample.val) =
      (fun sample labelTable => binaryRatingScore (labelTable (coordinate sample))) := by
    funext sample labelTable
    exact canonicalBordaBatchObservation_eq_score arm sample.isLt labelTable
  rw [hobservations]
  exact hscores

/-- Each in-budget Borda observation has exactly its arm's Borda score as mean. -/
theorem integral_canonicalBordaBatchObservation {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ)
    (arm : Arm) (sample : Fin batchSize) :
    (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure[
      canonicalBordaBatchObservation batchSize arm sample.val] =
        bordaScore winProbability arm := by
  let coordinate : canonicalBordaBatchCoordinate Arm batchSize := (arm, sample)
  have hscore : canonicalBordaBatchObservation batchSize arm sample.val =
      binaryRatingScore ∘ (fun labelTable => labelTable coordinate) := by
    funext labelTable
    simp [coordinate, canonicalBordaBatchObservation, sample.isLt]
  rw [hscore]
  calc
    (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure[
        binaryRatingScore ∘ (fun labelTable => labelTable coordinate)] =
        (Measure.map (fun labelTable => labelTable coordinate)
          (canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure)[
            binaryRatingScore] := by
          symm
          apply integral_map
          · exact (measurable_pi_apply coordinate).aemeasurable
          · exact Measurable.of_discrete.aestronglyMeasurable
    _ = (canonicalBordaTrialLaw winProbability hprobability arm).toMeasure[
          binaryRatingScore] := by
          rw [map_canonicalBordaBatchLabel winProbability hprobability batchSize coordinate]
    _ = bordaScore winProbability arm :=
      integral_canonicalBordaTrialLaw winProbability hprobability arm

/-- The source score bound holds almost everywhere under the canonical Borda law. -/
theorem ae_canonicalBordaBatchObservation_mem_Icc {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (batchSize : ℕ)
    (arm : Arm) (sample : ℕ) :
    ∀ᵐ labelTable ∂(canonicalBordaBatchLaw winProbability hprobability batchSize).toMeasure,
      canonicalBordaBatchObservation batchSize arm sample labelTable ∈ Set.Icc (0 : ℝ) 1 :=
  Filter.Eventually.of_forall
    (canonicalBordaBatchObservation_mem_Icc batchSize arm sample)

/--
The source Borda sampler gives simultaneous `epsilon / 2` score accuracy for
every arm at the stated finite ceiling budget, except with probability at most
`delta`.
-/
theorem canonicalBordaUniformEstimate_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
        {labelTable | ∃ arm, ¬
          |bordaEmpiricalScore
              (canonicalBordaBatchObservation
                (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm)
              (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable -
            bordaScore winProbability arm| < epsilon / 2} ≤ delta := by
  apply bordaUniformEstimate_failure_probability_of_budget
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure
    winProbability
    (fun arm sample => canonicalBordaBatchObservation
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample)
    epsilon delta
  · intro arm
    exact iIndepFun_canonicalBordaBatchObservation winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm
  · intro arm sample hsample
    exact measurable_canonicalBordaBatchObservation
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample
  · intro arm sample hsample
    exact ae_canonicalBordaBatchObservation_mem_Icc winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample
  · intro arm sample hsample
    simpa using integral_canonicalBordaBatchObservation winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm ⟨sample, hsample⟩
  · exact hcard
  · exact hepsilon
  · exact hdelta
  · exact hdeltaLeOne

/--
Selecting any empirical-score maximizer from the concrete Borda batch is an
`epsilon`-Borda maximum except with probability at most `delta`.  This is the
finite all-arms sampling route, distinct from Theorem 8's optimal-bandit
reduction.
-/
theorem canonicalDirectBordaMaxing_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ)
    (selected : (canonicalBordaBatchCoordinate Arm
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) → Bool) → Arm)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hmaximalEstimate : ∀ labelTable competitor,
      bordaEmpiricalScore
        (canonicalBordaBatchObservation
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) competitor)
        (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable ≤
      bordaEmpiricalScore
        (canonicalBordaBatchObservation
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) (selected labelTable))
        (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable) :
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
      {labelTable | ¬ EpsilonBordaMaximum winProbability epsilon (selected labelTable)} ≤ delta := by
  apply directBordaMaxing_failure_probability_of_budget
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure
    winProbability
    (fun arm sample => canonicalBordaBatchObservation
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample)
    epsilon delta selected
  · intro arm
    exact iIndepFun_canonicalBordaBatchObservation winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm
  · intro arm sample hsample
    exact measurable_canonicalBordaBatchObservation
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample
  · intro arm sample hsample
    exact ae_canonicalBordaBatchObservation_mem_Icc winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample
  · intro arm sample hsample
    simpa using integral_canonicalBordaBatchObservation winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm ⟨sample, hsample⟩
  · exact hcard
  · exact hepsilon
  · exact hdelta
  · exact hdeltaLeOne
  · exact hmaximalEstimate

/--
Theorem 9's Borda concentration statement under its concrete uniform-opponent
sampler: every bijective order sorted by the sampled Borda scores is an
`epsilon`-Borda ranking except with probability at most `delta`.
-/
theorem canonicalBordaRanking_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ)
    (ranking : (canonicalBordaBatchCoordinate Arm
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) → Bool) →
        Fin (Fintype.card Arm) → Arm)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbijective : ∀ labelTable, Function.Bijective (ranking labelTable))
    (hsorted : ∀ labelTable, EstimatedScoresSorted
      (fun arm => bordaEmpiricalScore
        (canonicalBordaBatchObservation
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm)
        (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable)
      (ranking labelTable)) :
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
      {labelTable | ¬ EpsilonBordaRanking winProbability epsilon (ranking labelTable)} ≤ delta := by
  apply bordaRanking_failure_probability_of_budget
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure
    winProbability
    (fun arm sample => canonicalBordaBatchObservation
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample)
    epsilon delta ranking
  · intro arm
    exact iIndepFun_canonicalBordaBatchObservation winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm
  · intro arm sample hsample
    exact measurable_canonicalBordaBatchObservation
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample
  · intro arm sample hsample
    exact ae_canonicalBordaBatchObservation_mem_Icc winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm sample
  · intro arm sample hsample
    simpa using integral_canonicalBordaBatchObservation winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm ⟨sample, hsample⟩
  · exact hcard
  · exact hepsilon
  · exact hdelta
  · exact hdeltaLeOne
  · exact hbijective
  · exact hsorted

/--
Algorithm 9's deterministic empirical-score sort, run on the concrete
uniform-opponent Borda batches, returns an `epsilon`-Borda ranking except with
probability at most `delta`.
-/
theorem canonicalEmpiricalBordaRanking_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
      {labelTable | ¬ EpsilonBordaRanking winProbability epsilon
        (empiricalBordaRanking (fun arm => bordaEmpiricalScore
          (canonicalBordaBatchObservation
            (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm)
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable))} ≤ delta := by
  apply canonicalBordaRanking_failure_probability winProbability hprobability epsilon delta
  · exact hcard
  · exact hepsilon
  · exact hdelta
  · exact hdeltaLeOne
  · intro labelTable
    exact empiricalBordaRanking_bijective _
  · intro labelTable
    exact empiricalBordaRanking_sorted _

end FalahatgarEtAl2017MaxingRanking
