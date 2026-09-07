import ZhouChenLi2014OptimalPACMultipleArm.BestArmDeterministic
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Applications.RatingSystems.BinaryLargeDeviations
import AppliedModelingLib.Foundations.Probability.FiniteIID

/-!
# Finite uniform Bernoulli batches

Section 6 of Zhou--Chen--Li's supplement replaces the final Accept--Reject
stage by uniform sampling of each remaining arm.  This file gives the exact
finite product experiment for that stage.  The concentration and integer
resource proof are developed on this concrete sampler rather than assumed as
a best-arm certificate.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The arm/sample coordinates of one uniform Bernoulli batch. -/
abbrev UniformBatchCoordinate (Arm : Type*) (sampleCount : ℕ) := Arm × Fin sampleCount

/--
Independent Bernoulli labels for every arm and every sample of a uniform
batch.  Coordinates of different arms may have different Bernoulli means.
-/
noncomputable def uniformBernoulliBatchLaw {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) :
    PMF (UniformBatchCoordinate Arm sampleCount → Bool) := by
  let marginal : UniformBatchCoordinate Arm sampleCount → Measure Bool := fun coordinate =>
    (bernoulliRewardLaw mean hmean coordinate.1).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The batch PMF is the heterogeneous product of the Bernoulli coordinate laws. -/
theorem uniformBernoulliBatchLaw_toMeasure {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) :
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure =
      Measure.pi (fun coordinate : UniformBatchCoordinate Arm sampleCount =>
        (bernoulliRewardLaw mean hmean coordinate.1).toMeasure) := by
  let marginal : UniformBatchCoordinate Arm sampleCount → Measure Bool := fun coordinate =>
    (bernoulliRewardLaw mean hmean coordinate.1).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/--
The measure-defined uniform batch PMF is exactly the finite dependent product
of its coordinate Bernoulli PMFs.  This pointwise form is used when replaying
the batch through a sequential fixed pull schedule.
-/
theorem uniformBernoulliBatchLaw_eq_pmfPi {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) :
    uniformBernoulliBatchLaw mean hmean sampleCount =
      pmfPi (fun coordinate : UniformBatchCoordinate Arm sampleCount =>
        bernoulliRewardLaw mean hmean coordinate.1) := by
  classical
  apply PMF.ext
  intro labelTable
  rw [← (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure_apply_singleton labelTable
    MeasurableSet.of_discrete]
  rw [uniformBernoulliBatchLaw_toMeasure, Measure.pi_singleton]
  rw [pmfPi_apply]
  apply Finset.prod_congr rfl
  intro coordinate _
  exact (bernoulliRewardLaw mean hmean coordinate.1).toMeasure_apply_singleton
    (labelTable coordinate) MeasurableSet.of_discrete

/-- All labels in the finite uniform batch are mutually independent. -/
theorem iIndepFun_uniformBernoulliBatchLabel {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) :
    iIndepFun (fun coordinate : UniformBatchCoordinate Arm sampleCount =>
      fun labelTable => labelTable coordinate)
      (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure := by
  let marginal : UniformBatchCoordinate Arm sampleCount → Measure Bool := fun coordinate =>
    (bernoulliRewardLaw mean hmean coordinate.1).toMeasure
  letI : ∀ coordinate, IsProbabilityMeasure (marginal coordinate) := fun _ => inferInstance
  rw [uniformBernoulliBatchLaw_toMeasure]
  simpa only [marginal] using
    (iIndepFun_pi (X := fun _ : UniformBatchCoordinate Arm sampleCount =>
      (id : Bool → Bool)) (μ := marginal) (fun _ => measurable_id.aemeasurable))

/-- The marginal law of one scheduled label is its arm's Bernoulli law. -/
theorem map_uniformBernoulliBatchLabel {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ)
    (coordinate : UniformBatchCoordinate Arm sampleCount) :
    Measure.map (fun labelTable => labelTable coordinate)
      (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure =
        (bernoulliRewardLaw mean hmean coordinate.1).toMeasure := by
  rw [uniformBernoulliBatchLaw_toMeasure]
  let marginal : UniformBatchCoordinate Arm sampleCount → Measure Bool := fun index =>
    (bernoulliRewardLaw mean hmean index.1).toMeasure
  letI : ∀ index, IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun labelTable => labelTable coordinate) (Measure.pi marginal) =
    marginal coordinate
  exact (measurePreserving_eval marginal coordinate).map_eq

/--
The total score observation for a uniform batch.  Out-of-budget indices are
zero solely to make the function total; all sampling theorems use its finite
in-budget prefix.
-/
noncomputable def uniformBernoulliBatchObservation {Arm : Type*} (sampleCount : ℕ)
    (arm : Arm) (sample : ℕ)
    (labelTable : UniformBatchCoordinate Arm sampleCount → Bool) : ℝ :=
  if hsample : sample < sampleCount then
    binaryRatingScore (labelTable (arm, ⟨sample, hsample⟩))
  else 0

theorem uniformBernoulliBatchObservation_eq_score {Arm : Type*}
    {sampleCount sample : ℕ} (arm : Arm) (hsample : sample < sampleCount)
    (labelTable : UniformBatchCoordinate Arm sampleCount → Bool) :
    uniformBernoulliBatchObservation sampleCount arm sample labelTable =
      binaryRatingScore (labelTable (arm, ⟨sample, hsample⟩)) := by
  simp [uniformBernoulliBatchObservation, hsample]

theorem measurable_uniformBernoulliBatchObservation {Arm : Type*} [Fintype Arm]
    (sampleCount : ℕ) (arm : Arm) (sample : ℕ) :
    Measurable (uniformBernoulliBatchObservation (Arm := Arm) sampleCount arm sample) :=
  Measurable.of_discrete

theorem uniformBernoulliBatchObservation_mem_Icc {Arm : Type*}
    (sampleCount : ℕ) (arm : Arm) (sample : ℕ)
    (labelTable : UniformBatchCoordinate Arm sampleCount → Bool) :
    uniformBernoulliBatchObservation sampleCount arm sample labelTable ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hsample : sample < sampleCount
  · rw [uniformBernoulliBatchObservation_eq_score arm hsample]
    rcases hvalue : labelTable (arm, ⟨sample, hsample⟩) with (_ | _)
    · norm_num [binaryRatingScore, hvalue]
    · norm_num [binaryRatingScore, hvalue]
  · simp [uniformBernoulliBatchObservation, hsample]

/-- The in-budget samples of one arm are independent under the uniform batch law. -/
theorem iIndepFun_uniformBernoulliBatchObservation {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) (arm : Arm) :
    iIndepFun (fun sample : Fin sampleCount =>
      uniformBernoulliBatchObservation sampleCount arm sample.val)
      (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure := by
  let coordinate : Fin sampleCount → UniformBatchCoordinate Arm sampleCount := fun sample =>
    (arm, sample)
  have hcoordinateInjective : Function.Injective coordinate := by
    intro first second hequal
    exact congrArg Prod.snd hequal
  have hlabels := (iIndepFun_uniformBernoulliBatchLabel mean hmean sampleCount).precomp
    hcoordinateInjective
  have hscores := hlabels.comp (fun _ => binaryRatingScore) (fun _ => Measurable.of_discrete)
  have hobservations : (fun sample : Fin sampleCount =>
      uniformBernoulliBatchObservation sampleCount arm sample.val) =
      (fun sample labelTable => binaryRatingScore (labelTable (coordinate sample))) := by
    funext sample labelTable
    exact uniformBernoulliBatchObservation_eq_score arm sample.isLt labelTable
  rw [hobservations]
  exact hscores

/-- Every in-budget observation has its arm's prescribed Bernoulli mean. -/
theorem integral_uniformBernoulliBatchObservation {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ)
    (arm : Arm) (sample : Fin sampleCount) :
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure[
      uniformBernoulliBatchObservation sampleCount arm sample.val] = mean arm := by
  let coordinate : UniformBatchCoordinate Arm sampleCount := (arm, sample)
  have hscore : uniformBernoulliBatchObservation sampleCount arm sample.val =
      binaryRatingScore ∘ (fun labelTable => labelTable coordinate) := by
    funext labelTable
    simp [coordinate, uniformBernoulliBatchObservation, sample.isLt]
  rw [hscore]
  calc
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure[
        binaryRatingScore ∘ (fun labelTable => labelTable coordinate)] =
        (Measure.map (fun labelTable => labelTable coordinate)
          (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure)[binaryRatingScore] := by
      symm
      apply integral_map
      · exact (measurable_pi_apply coordinate).aemeasurable
      · exact Measurable.of_discrete.aestronglyMeasurable
    _ = (bernoulliRewardLaw mean hmean arm).toMeasure[binaryRatingScore] := by
      rw [map_uniformBernoulliBatchLabel mean hmean sampleCount coordinate]
    _ = mean arm := by
      rw [← pmfExp_eq_integral_toMeasure]
      unfold pmfExp bernoulliRewardLaw
      simp [PMF.bernoulli_apply, binaryRatingScore]
      rfl

/-- The score is pointwise bounded in the Bernoulli interval. -/
theorem ae_uniformBernoulliBatchObservation_mem_Icc {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ)
    (arm : Arm) (sample : ℕ) :
    ∀ᵐ labelTable ∂(uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure,
      uniformBernoulliBatchObservation sampleCount arm sample labelTable ∈ Set.Icc (0 : ℝ) 1 :=
  Filter.Eventually.of_forall
    (uniformBernoulliBatchObservation_mem_Icc sampleCount arm sample)

end ZhouChenLi2014OptimalPACMultipleArm
