import ZhouChenLi2014OptimalPACMultipleArm.QuartileBatch
import ZhouChenLi2014OptimalPACMultipleArm.FixedBernoulliPolicy

/-!
# Sequential replay of one fixed QE batch

For a fixed active set, a QE round is an independent Bernoulli product over
its arm/sample coordinates.  This file realizes that product as a finite
sequential policy and proves the exact PMF identity.  The multi-round replay
uses this conditional one-block bridge after reconstructing its current
active set from earlier blocks.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open MeasureTheory ProbabilityTheory

/-- The flattened QE-batch carrier has one coordinate for every active arm
and every one of its per-arm samples. -/
theorem quartileBatchCoordinate_card {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ) :
    Fintype.card (QuartileBatchCoordinate active sampleCount) = active.card * sampleCount := by
  rw [Fintype.card_sigma]
  simp

/-- A deterministic enumeration of the arm/sample coordinates of one fixed
QE batch. -/
noncomputable def quartileBatchCoordinateEquiv {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ) :
    QuartileBatchCoordinate active sampleCount ≃
      Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) :=
  Fintype.equivFin _

/-- Reindex a sequential QE-batch trace as its arm/sample label table. -/
noncomputable def quartileBatchTraceLabels {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ)
    (rewards : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) → Bool) :
    QuartileBatchCoordinate active sampleCount → Bool := fun coordinate =>
  rewards (quartileBatchCoordinateEquiv active sampleCount coordinate)

/-- Reindex a flattened QE-batch table into sequential trace order. -/
noncomputable def quartileBatchLabelsTrace {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ)
    (labels : QuartileBatchCoordinate active sampleCount → Bool) :
    Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) → Bool := fun round =>
  labels ((quartileBatchCoordinateEquiv active sampleCount).symm round)

@[simp]
theorem quartileBatchTraceLabels_labelsTrace {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ)
    (labels : QuartileBatchCoordinate active sampleCount → Bool) :
    quartileBatchTraceLabels active sampleCount
      (quartileBatchLabelsTrace active sampleCount labels) = labels := by
  funext coordinate
  simp [quartileBatchTraceLabels, quartileBatchLabelsTrace]

@[simp]
theorem quartileBatchLabelsTrace_traceLabels {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ)
    (rewards : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) → Bool) :
    quartileBatchLabelsTrace active sampleCount
      (quartileBatchTraceLabels active sampleCount rewards) = rewards := by
  funext round
  simp [quartileBatchTraceLabels, quartileBatchLabelsTrace]

/-- A one-round sequential QE policy that queries every active arm/sample
coordinate once. Its output is irrelevant to the QE state update, so it is a
fixed active arm chosen only to inhabit the best-arm-procedure interface. -/
noncomputable def quartileBernoulliBatchProcedure
    {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (hactive : active.Nonempty) (sampleCount : ℕ) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (QuartileBatchCoordinate active sampleCount)) :=
  fixedBernoulliProcedure
    (fun round => ((quartileBatchCoordinateEquiv active sampleCount).symm round).1.val)
    (fun _ => Classical.choose hactive)

/-- A fixed QE-round schedule with `paddingCount` inert trailing pulls.  The
first coordinate block is exactly the arm/sample enumeration; padding uses a
fixed active arm and is discarded before the batch update. -/
noncomputable def quartilePaddedBatchSchedule
    {Arm : Type*} (active : Finset Arm) (hactive : active.Nonempty)
    (sampleCount paddingCount : ℕ) :
    Fin (Fintype.card (QuartileBatchCoordinate active sampleCount) + paddingCount) → Arm :=
  fun position =>
    if hcoordinate : position.val < Fintype.card (QuartileBatchCoordinate active sampleCount) then
      ((quartileBatchCoordinateEquiv active sampleCount).symm
        ⟨position.val, hcoordinate⟩).1.val
    else Classical.choose hactive

/-- On its allocated prefix, the padded schedule agrees with the unpadded
QE coordinate enumeration. -/
theorem quartilePaddedBatchSchedule_prefix
    {Arm : Type*} (active : Finset Arm) (hactive : active.Nonempty)
    (sampleCount paddingCount : ℕ)
    (coordinate : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount))) :
    fixedSchedulePrefix (quartilePaddedBatchSchedule active hactive sampleCount paddingCount)
      (Nat.le_add_right _ _) coordinate =
      ((quartileBatchCoordinateEquiv active sampleCount).symm coordinate).1.val := by
  unfold fixedSchedulePrefix quartilePaddedBatchSchedule
  dsimp
  rw [if_pos coordinate.isLt]

/-- A sequential QE-batch procedure retaining a fixed number of inert pulls
after the allocated arm/sample coordinates. -/
noncomputable def quartilePaddedBernoulliBatchProcedure
    {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (hactive : active.Nonempty)
    (sampleCount paddingCount : ℕ) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (QuartileBatchCoordinate active sampleCount) + paddingCount) :=
  fixedBernoulliProcedure
    (quartilePaddedBatchSchedule active hactive sampleCount paddingCount)
    (fun _ => Classical.choose hactive)

/-- Replaying a fixed QE batch and reindexing the resulting trace gives its
heterogeneous Bernoulli coordinate product. -/
theorem quartileBatchTraceProductLaw_map_eq_pmfPi
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (active : Finset Arm) (sampleCount : ℕ) :
    (pmfPi (fun round : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) =>
      bernoulliRewardLaw mean hmean
        ((quartileBatchCoordinateEquiv active sampleCount).symm round).1.val)).map
      (quartileBatchTraceLabels active sampleCount) =
      pmfPi (fun coordinate : QuartileBatchCoordinate active sampleCount =>
        bernoulliRewardLaw mean hmean coordinate.1.val) := by
  classical
  let coordinateEquiv := quartileBatchCoordinateEquiv active sampleCount
  let traceLaw : PMF (Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) → Bool) :=
    pmfPi (fun round : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) =>
      bernoulliRewardLaw mean hmean ((coordinateEquiv.symm round).1).val)
  apply PMF.ext
  intro labels
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single
    (quartileBatchLabelsTrace active sampleCount labels)]
  · rw [if_pos (quartileBatchTraceLabels_labelsTrace active sampleCount labels).symm]
    change traceLaw (quartileBatchLabelsTrace active sampleCount labels) =
      pmfPi (fun coordinate : QuartileBatchCoordinate active sampleCount =>
        bernoulliRewardLaw mean hmean coordinate.1.val) labels
    rw [pmfPi_apply, pmfPi_apply]
    change (∏ round : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)),
        bernoulliRewardLaw mean hmean (coordinateEquiv.symm round).1.val
          (quartileBatchLabelsTrace active sampleCount labels round)) =
      ∏ coordinate : QuartileBatchCoordinate active sampleCount,
        bernoulliRewardLaw mean hmean coordinate.1.val (labels coordinate)
    simpa [quartileBatchLabelsTrace, coordinateEquiv] using
      (Equiv.prod_comp coordinateEquiv.symm
        (fun coordinate : QuartileBatchCoordinate active sampleCount =>
          bernoulliRewardLaw mean hmean coordinate.1.val (labels coordinate)))
  · intro other _ hother
    have hnotMapped : quartileBatchTraceLabels active sampleCount other ≠ labels := by
      intro hequal
      have hinverse : other = quartileBatchLabelsTrace active sampleCount labels := by
        funext round
        have hpoint := congrFun hequal
          ((quartileBatchCoordinateEquiv active sampleCount).symm round)
        simpa [quartileBatchTraceLabels, quartileBatchLabelsTrace] using hpoint
      exact hother hinverse
    simp only [if_neg (Ne.symm hnotMapped)]
  · simp

/-- The finite sequential QE-batch policy has exactly the flattened fresh
batch PMF after reindexing its reward trace. -/
theorem adaptiveQuartileBernoulliBatchProcedureRewardLaw_map_eq_flatBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (active : Finset Arm) (hactive : active.Nonempty) (sampleCount : ℕ) :
    (adaptiveBernoulliRewardLaw mean hmean
      (quartileBernoulliBatchProcedure active hactive sampleCount)).map
        (quartileBatchTraceLabels active sampleCount) =
      (quartileBernoulliBatchLaw mean hmean active sampleCount).map quartileBatchUncurry := by
  rw [quartileBernoulliBatchProcedure, adaptiveFixedBernoulliRewardLaw_eq_pmfPi]
  rw [quartileBatchTraceProductLaw_map_eq_pmfPi]
  exact (quartileBernoulliBatchLaw_map_uncurry_eq_pmfPi mean hmean active sampleCount).symm

/-- After discarding inert trailing pulls, a padded sequential QE round has
exactly the same flattened fresh-batch law as its unpadded product model. -/
theorem adaptiveQuartilePaddedBernoulliBatchProcedureRewardLaw_map_eq_flatBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (active : Finset Arm) (hactive : active.Nonempty)
    (sampleCount paddingCount : ℕ) :
    ((adaptiveBernoulliRewardLaw mean hmean
      (quartilePaddedBernoulliBatchProcedure active hactive sampleCount paddingCount)).map
        (rewardTracePrefix (Fintype.card (QuartileBatchCoordinate active sampleCount)) paddingCount)).map
      (quartileBatchTraceLabels active sampleCount) =
      (quartileBernoulliBatchLaw mean hmean active sampleCount).map quartileBatchUncurry := by
  rw [adaptiveBernoulliRewardLaw]
  rw [adaptiveBernoulliRewardPrefixLaw_map_rewardTracePrefix mean hmean
    (quartilePaddedBernoulliBatchProcedure active hactive sampleCount paddingCount)
    (Fintype.card (QuartileBatchCoordinate active sampleCount)) paddingCount (le_refl _)]
  rw [quartilePaddedBernoulliBatchProcedure,
    adaptiveFixedBernoulliRewardPrefixLaw_eq_pmfPi]
  have hschedule :
      (fun coordinate : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) =>
        bernoulliRewardLaw mean hmean
          (fixedSchedulePrefix
            (quartilePaddedBatchSchedule active hactive sampleCount paddingCount)
            (Nat.le_add_right _ _) coordinate)) =
      (fun coordinate : Fin (Fintype.card (QuartileBatchCoordinate active sampleCount)) =>
        bernoulliRewardLaw mean hmean
          ((quartileBatchCoordinateEquiv active sampleCount).symm coordinate).1.val) := by
    funext coordinate
    rw [quartilePaddedBatchSchedule_prefix]
  rw [hschedule]
  rw [quartileBatchTraceProductLaw_map_eq_pmfPi]
  exact (quartileBernoulliBatchLaw_map_uncurry_eq_pmfPi mean hmean active sampleCount).symm

end ZhouChenLi2014OptimalPACMultipleArm
