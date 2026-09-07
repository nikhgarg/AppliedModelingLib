import ZhouChenLi2014OptimalPACMultipleArm.FixedBernoulliPolicy
import ZhouChenLi2014OptimalPACMultipleArm.UniformBudget
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC

/-!
# Sequential replay of the uniform final batch

The supplement's uniform final stage is not left as a static sampler: it is
replayed by a fixed finite Bernoulli procedure and shown to have exactly the
same output distribution.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open AppliedModelingLib.PreferenceRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A deterministic enumeration of the arm/sample coordinates in a final batch. -/
noncomputable def uniformBatchCoordinateEquiv (Arm : Type*) [Fintype Arm]
    (sampleCount : ℕ) :
    UniformBatchCoordinate Arm sampleCount ≃
      Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) :=
  Fintype.equivFin _

/-- Reindex a sequential trace as the corresponding arm/sample label table. -/
noncomputable def uniformBatchTraceLabels {Arm : Type*} [Fintype Arm]
    (sampleCount : ℕ)
    (rewards : Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) → Bool) :
    UniformBatchCoordinate Arm sampleCount → Bool := fun coordinate =>
  rewards (uniformBatchCoordinateEquiv Arm sampleCount coordinate)

/-- Reindex a label table into the trace order of the fixed procedure. -/
noncomputable def uniformBatchLabelsTrace {Arm : Type*} [Fintype Arm]
    (sampleCount : ℕ) (labels : UniformBatchCoordinate Arm sampleCount → Bool) :
    Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) → Bool := fun round =>
  labels ((uniformBatchCoordinateEquiv Arm sampleCount).symm round)

@[simp]
theorem uniformBatchTraceLabels_labelsTrace {Arm : Type*} [Fintype Arm]
    (sampleCount : ℕ) (labels : UniformBatchCoordinate Arm sampleCount → Bool) :
    uniformBatchTraceLabels sampleCount (uniformBatchLabelsTrace sampleCount labels) = labels := by
  funext coordinate
  simp [uniformBatchTraceLabels, uniformBatchLabelsTrace]

@[simp]
theorem uniformBatchLabelsTrace_traceLabels {Arm : Type*} [Fintype Arm]
    (sampleCount : ℕ)
    (rewards : Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) → Bool) :
    uniformBatchLabelsTrace sampleCount (uniformBatchTraceLabels sampleCount rewards) = rewards := by
  funext round
  simp [uniformBatchTraceLabels, uniformBatchLabelsTrace]

/--
The nonadaptive procedure that queries every arm/sample coordinate once and
returns the static batch empirical maximizer.
-/
noncomputable def uniformBernoulliBatchProcedure {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (sampleCount : ℕ) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (UniformBatchCoordinate Arm sampleCount)) :=
  fixedBernoulliProcedure
    (fun round => ((uniformBatchCoordinateEquiv Arm sampleCount).symm round).1)
    (fun rewards => uniformBernoulliBatchBestArm sampleCount
      (uniformBatchTraceLabels sampleCount rewards))

/-- The replay policy makes exactly one pull for every arm/sample coordinate. -/
theorem uniformBernoulliBatchProcedure_pullBudget {Arm : Type*} [Fintype Arm]
    (sampleCount : ℕ) :
    Fintype.card (UniformBatchCoordinate Arm sampleCount) = Fintype.card Arm * sampleCount := by
  simp [UniformBatchCoordinate]

/-- Replaying the fixed trace product and then reindexing produces the batch product PMF. -/
theorem uniformBatchTraceProductLaw_map_eq_uniformBernoulliBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) :
    (AppliedModelingLib.pmfPi (fun round : Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) =>
      bernoulliRewardLaw mean hmean
        ((uniformBatchCoordinateEquiv Arm sampleCount).symm round).1)).map
      (uniformBatchTraceLabels sampleCount) =
      uniformBernoulliBatchLaw mean hmean sampleCount := by
  classical
  let coordinateEquiv := uniformBatchCoordinateEquiv Arm sampleCount
  let traceLaw : PMF (Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) → Bool) :=
    AppliedModelingLib.pmfPi (fun round : Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)) =>
      bernoulliRewardLaw mean hmean (coordinateEquiv.symm round).1)
  apply PMF.ext
  intro labels
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single
    (uniformBatchLabelsTrace sampleCount labels)]
  · rw [if_pos (uniformBatchTraceLabels_labelsTrace sampleCount labels).symm]
    change traceLaw (uniformBatchLabelsTrace sampleCount labels) =
      uniformBernoulliBatchLaw mean hmean sampleCount labels
    rw [uniformBernoulliBatchLaw_eq_pmfPi, pmfPi_apply, pmfPi_apply]
    change (∏ round : Fin (Fintype.card (UniformBatchCoordinate Arm sampleCount)),
        bernoulliRewardLaw mean hmean (coordinateEquiv.symm round).1
          (uniformBatchLabelsTrace sampleCount labels round)) =
      ∏ coordinate : UniformBatchCoordinate Arm sampleCount,
        bernoulliRewardLaw mean hmean coordinate.1 (labels coordinate)
    simpa [uniformBatchLabelsTrace, coordinateEquiv] using
      (Equiv.prod_comp coordinateEquiv.symm
        (fun coordinate : UniformBatchCoordinate Arm sampleCount =>
          bernoulliRewardLaw mean hmean coordinate.1 (labels coordinate)))
  · intro other _ hother
    have hnotMapped : uniformBatchTraceLabels sampleCount other ≠ labels := by
      intro hequal
      have hinverse : other = uniformBatchLabelsTrace sampleCount labels := by
        funext round
        have hpoint := congrFun hequal
          ((uniformBatchCoordinateEquiv Arm sampleCount).symm round)
        simpa [uniformBatchTraceLabels, uniformBatchLabelsTrace] using hpoint
      exact hother hinverse
    simp only [if_neg (Ne.symm hnotMapped)]
  · simp

/-- The actual reward trace of the replay policy pushes forward to the uniform batch law. -/
theorem adaptiveUniformBernoulliBatchProcedureRewardLaw_map_eq_uniformBernoulliBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) :
    (adaptiveBernoulliRewardLaw mean hmean (uniformBernoulliBatchProcedure sampleCount)).map
      (uniformBatchTraceLabels sampleCount) =
      uniformBernoulliBatchLaw mean hmean sampleCount := by
  rw [uniformBernoulliBatchProcedure, adaptiveFixedBernoulliRewardLaw_eq_pmfPi]
  exact uniformBatchTraceProductLaw_map_eq_uniformBernoulliBatchLaw mean hmean sampleCount

/-- The replay procedure's PAC success probability is the static batch success probability. -/
theorem finiteBestArmSuccessProbability_uniformBernoulliBatchProcedure
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (epsilon : ℝ) (sampleCount : ℕ) :
    finiteBestArmSuccessProbability mean hmean epsilon
      (uniformBernoulliBatchProcedure (Arm := Arm) sampleCount) =
      pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) (fun labels =>
        EpsilonPACBestArm mean epsilon
          (uniformBernoulliBatchBestArm sampleCount labels)) := by
  classical
  unfold finiteBestArmSuccessProbability finiteBestArmSuccess
  unfold pmfProbClassical
  rw [← adaptiveUniformBernoulliBatchProcedureRewardLaw_map_eq_uniformBernoulliBatchLaw
    mean hmean sampleCount, pmfProb_map]
  rfl

/--
The supplement's ceiling-specified uniform final batch is an actual finite
Bernoulli best-arm procedure with its proved `epsilon`-PAC guarantee.
-/
theorem finitePACBestArmGuarantee_uniformBernoulliBatchProcedure
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    FinitePACBestArmGuarantee mean hmean epsilon delta
      (uniformBernoulliBatchProcedure (Arm := Arm)
        (uniformBernoulliBatchSampleBudget (Fintype.card Arm) epsilon delta)) := by
  classical
  let sampleCount := uniformBernoulliBatchSampleBudget (Fintype.card Arm) epsilon delta
  let success : (UniformBatchCoordinate Arm sampleCount → Bool) → Prop := fun labels =>
    EpsilonPACBestArm mean epsilon (uniformBernoulliBatchBestArm sampleCount labels)
  let failure : (UniformBatchCoordinate Arm sampleCount → Bool) → Prop := fun labels =>
    ¬ success labels
  have hfailure : pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) failure ≤
      delta := by
    rw [pmfProbClassical_eq_pmfProb, AppliedModelingLib.pmfProb_eq_toMeasure_real]
    exact uniformBernoulliBatchBestArm_failure_probability_of_budget mean hmean epsilon delta
      hepsilon hdelta hdeltaLeOne
  have hcomplement : pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) failure =
      1 - pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) success := by
    calc
      pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) failure =
          pmfProb (uniformBernoulliBatchLaw mean hmean sampleCount) failure :=
        pmfProbClassical_eq_pmfProb _ _
      _ = pmfProb (uniformBernoulliBatchLaw mean hmean sampleCount) (fun labels =>
          ¬ success labels) := by
            apply pmfProb_congr
            intro labels
            rfl
      _ = 1 - pmfProb (uniformBernoulliBatchLaw mean hmean sampleCount) success :=
        pmfProb_compl _ _
      _ = 1 - pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) success := by
        rw [pmfProbClassical_eq_pmfProb]
  unfold FinitePACBestArmGuarantee
  rw [finiteBestArmSuccessProbability_uniformBernoulliBatchProcedure]
  change 1 - delta ≤ pmfProbClassical (uniformBernoulliBatchLaw mean hmean sampleCount) success
  linarith

end ZhouChenLi2014OptimalPACMultipleArm
