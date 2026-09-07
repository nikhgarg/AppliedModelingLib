import ZhouChenLi2014OptimalPACMultipleArm.UniformBatch
import AppliedModelingLib.Foundations.Probability.UniformHoeffding

/-!
# Uniform-batch best-arm concentration

The supplement's alternative final stage samples every surviving arm equally
often and returns an empirical maximizer.  These lemmas prove its finite
concentration and deterministic PAC implication on the explicit product law.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The empirical Bernoulli mean of one arm in a finite uniform batch. -/
noncomputable def uniformBernoulliBatchEmpiricalMean {Arm : Type*} (sampleCount : ℕ)
    (arm : Arm) (labelTable : UniformBatchCoordinate Arm sampleCount → Bool) : ℝ :=
  (∑ sample : Fin sampleCount,
    uniformBernoulliBatchObservation sampleCount arm sample.val labelTable) /
      (sampleCount : ℝ)

/-- The uniform-batch empirical-maximization output. -/
noncomputable def uniformBernoulliBatchBestArm {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (sampleCount : ℕ) (labelTable : UniformBatchCoordinate Arm sampleCount → Bool) : Arm :=
  finiteScoreMaximizer (fun arm =>
    uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable)

/-- A finite-index two-sided Hoeffding bound specialized to one batch arm. -/
theorem uniformBernoulliBatch_centeredSum_abs_upperTail {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ) (arm : Arm)
    (error : ℝ) (herror : 0 ≤ error) :
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure.real
      {labelTable | (sampleCount : ℝ) * error ≤
        |∑ sample : Fin sampleCount,
          (uniformBernoulliBatchObservation sampleCount arm sample.val labelTable -
            (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure[
              uniformBernoulliBatchObservation sampleCount arm sample.val])|} ≤
        2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure
  let observation : Fin sampleCount →
      (UniformBatchCoordinate Arm sampleCount → Bool) → ℝ := fun sample =>
    uniformBernoulliBatchObservation sampleCount arm sample.val
  let upperEvent : Set (UniformBatchCoordinate Arm sampleCount → Bool) := {labelTable |
    (sampleCount : ℝ) * error ≤
      ∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])}
  let lowerEvent : Set (UniformBatchCoordinate Arm sampleCount → Bool) := {labelTable |
    (∑ sample : Fin sampleCount,
      (observation sample labelTable - law[observation sample])) ≤
        -(sampleCount : ℝ) * error}
  let absoluteEvent : Set (UniformBatchCoordinate Arm sampleCount → Bool) := {labelTable |
    (sampleCount : ℝ) * error ≤
      |∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])|}
  have hupper : law.real upperEvent ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    simpa [law, observation, upperEvent] using
      (boundedIIndep_centeredSum_upperTail_finset law observation
        (iIndepFun_uniformBernoulliBatchObservation mean hmean sampleCount arm)
        (fun sample => measurable_uniformBernoulliBatchObservation sampleCount arm sample.val)
        (fun sample => ae_uniformBernoulliBatchObservation_mem_Icc
          mean hmean sampleCount arm sample.val)
        ((sampleCount : ℝ) * error)
        (mul_nonneg (Nat.cast_nonneg sampleCount) herror))
  have hlower : law.real lowerEvent ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    simpa [law, observation, lowerEvent] using
      (boundedIIndep_centeredSum_lowerTail_finset law observation
        (iIndepFun_uniformBernoulliBatchObservation mean hmean sampleCount arm)
        (fun sample => measurable_uniformBernoulliBatchObservation sampleCount arm sample.val)
        (fun sample => ae_uniformBernoulliBatchObservation_mem_Icc
          mean hmean sampleCount arm sample.val)
        ((sampleCount : ℝ) * error)
        (mul_nonneg (Nat.cast_nonneg sampleCount) herror))
  have hsubset : absoluteEvent ⊆ upperEvent ∪ lowerEvent := by
    intro labelTable habsolute
    change (sampleCount : ℝ) * error ≤
      |∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])| at habsolute
    change ((sampleCount : ℝ) * error ≤
      ∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) ∨
      ((∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) ≤
          -(sampleCount : ℝ) * error)
    rcases le_abs.mp habsolute with hupper | hnegated
    · exact Or.inl hupper
    · exact Or.inr (by linarith)
  change law.real absoluteEvent ≤ _
  calc
    law.real absoluteEvent ≤ law.real (upperEvent ∪ lowerEvent) :=
      measureReal_mono hsubset
    _ ≤ law.real upperEvent + law.real lowerEvent := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
      nlinarith [hupper, hlower]

/-- The exact one-arm empirical-mean failure event is controlled by Hoeffding. -/
theorem uniformBernoulliBatch_empiricalMean_failure_probability {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ)
    (hcount : 0 < sampleCount) (arm : Arm) (error : ℝ) (herror : 0 ≤ error) :
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure.real
      {labelTable | error <
        |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm|} ≤
        2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure
  let observation : Fin sampleCount →
      (UniformBatchCoordinate Arm sampleCount → Bool) → ℝ := fun sample =>
    uniformBernoulliBatchObservation sampleCount arm sample.val
  have hsum : ∀ labelTable,
      (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) =
      (sampleCount : ℝ) *
          (uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm) := by
    intro labelTable
    dsimp [observation]
    calc
      (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) =
          ∑ sample : Fin sampleCount, (observation sample labelTable - mean arm) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [show law[observation sample] = mean arm by
              exact integral_uniformBernoulliBatchObservation mean hmean sampleCount arm sample]
      _ = (sampleCount : ℝ) *
          (uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm) := by
            unfold uniformBernoulliBatchEmpiricalMean
            have hraw :
                (∑ sample : Fin sampleCount,
                  (uniformBernoulliBatchObservation sampleCount arm sample.val labelTable - mean arm)) =
                  (sampleCount : ℝ) *
                    ((∑ sample : Fin sampleCount,
                      uniformBernoulliBatchObservation sampleCount arm sample.val labelTable) /
                      (sampleCount : ℝ) - mean arm) := by
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              have hcountReal : (sampleCount : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt hcount
              field_simp [hcountReal]
            rw [Finset.sum_sub_distrib] at hraw
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul] at hraw
            simpa [observation] using hraw
  have hsubset : {labelTable | error <
      |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm|} ⊆
      {labelTable | (sampleCount : ℝ) * error ≤
        |∑ sample : Fin sampleCount,
          (observation sample labelTable - law[observation sample])|} := by
    intro labelTable hfailure
    change (sampleCount : ℝ) * error ≤
      |∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])|
    rw [hsum labelTable, abs_mul]
    have hcountReal : 0 < (sampleCount : ℝ) := by exact_mod_cast hcount
    rw [abs_of_pos hcountReal]
    exact le_of_lt (mul_lt_mul_of_pos_left hfailure hcountReal)
  exact (measureReal_mono hsubset).trans
    (uniformBernoulliBatch_centeredSum_abs_upperTail mean hmean sampleCount arm error herror)

/-- Uniform concentration across every arm of the finite batch. -/
theorem uniformBernoulliBatch_uniformEmpiricalMean_failure_probability {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ)
    (hcount : 0 < sampleCount) (error : ℝ) (herror : 0 ≤ error) :
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure.real
      {labelTable | ∃ arm, error <
        |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm|} ≤
        (Fintype.card Arm : ℝ) * 2 *
          Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
            (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  classical
  let law := (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure
  let bad : Arm → Set (UniformBatchCoordinate Arm sampleCount → Bool) := fun arm =>
    {labelTable | error <
      |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm|}
  have hbad : ∀ arm, law.real (bad arm) ≤
      2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    intro arm
    exact uniformBernoulliBatch_empiricalMean_failure_probability
      mean hmean sampleCount hcount arm error herror
  have hbadUnion : {labelTable | ∃ arm, error <
      |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm|} =
        ⋃ arm ∈ (Finset.univ : Finset Arm), bad arm := by
    ext labelTable
    simp [bad]
  rw [hbadUnion]
  calc
    law.real (⋃ arm ∈ (Finset.univ : Finset Arm), bad arm) ≤
        ∑ arm ∈ (Finset.univ : Finset Arm), law.real (bad arm) := by
          simpa using (measureReal_biUnion_finset_le (μ := law)
            (Finset.univ : Finset Arm) bad)
    _ ≤ ∑ _arm ∈ (Finset.univ : Finset Arm),
        2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
          apply Finset.sum_le_sum
          intro arm _
          exact hbad arm
    _ = (Fintype.card Arm : ℝ) * 2 *
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
          simp [mul_assoc, mul_comm]

/-- Uniform empirical accuracy certifies the batch's selected arm as epsilon-PAC. -/
theorem epsilonPACBestArm_uniformBernoulliBatchBestArm_of_uniformEstimate {Arm : Type*}
    [Fintype Arm] [Nonempty Arm] (mean : Arm → ℝ) (sampleCount : ℕ)
    (epsilon : ℝ) (labelTable : UniformBatchCoordinate Arm sampleCount → Bool)
    (huniform : ∀ arm,
      |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm| < epsilon / 2) :
    EpsilonPACBestArm mean epsilon
      (uniformBernoulliBatchBestArm sampleCount labelTable) := by
  exact epsilonPACBestArm_of_uniformEstimate mean
    (fun arm => uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable) epsilon huniform

/-- The uniform batch fails to return an epsilon-PAC arm only on a uniform estimation failure. -/
theorem uniformBernoulliBatchBestArm_failure_probability {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (sampleCount : ℕ)
    (hcount : 0 < sampleCount) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure.real
      {labelTable | ¬ EpsilonPACBestArm mean epsilon
        (uniformBernoulliBatchBestArm sampleCount labelTable)} ≤
        (Fintype.card Arm : ℝ) * 2 *
          Real.exp (-((sampleCount : ℝ) * (epsilon / 2)) ^ 2 /
            (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (uniformBernoulliBatchLaw mean hmean sampleCount).toMeasure
  have hsubset : {labelTable | ¬ EpsilonPACBestArm mean epsilon
      (uniformBernoulliBatchBestArm sampleCount labelTable)} ⊆
      {labelTable | ∃ arm, epsilon / 2 <
        |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm|} := by
    intro labelTable hfailure
    by_contra hnotbad
    simp only [Set.mem_setOf_eq, not_exists] at hnotbad
    have huniform : ∀ arm,
        |uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable - mean arm| ≤
          epsilon / 2 := by
      intro arm
      exact le_of_not_gt (hnotbad arm)
    exact hfailure
      (epsilonPACBestArm_of_uniformEstimate_le mean
        (fun arm => uniformBernoulliBatchEmpiricalMean sampleCount arm labelTable)
        epsilon huniform)
  exact (measureReal_mono hsubset).trans
    (uniformBernoulliBatch_uniformEmpiricalMean_failure_probability
      mean hmean sampleCount hcount (epsilon / 2) (by linarith))

end ZhouChenLi2014OptimalPACMultipleArm
