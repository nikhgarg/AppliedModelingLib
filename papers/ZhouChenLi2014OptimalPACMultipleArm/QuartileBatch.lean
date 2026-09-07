import ZhouChenLi2014OptimalPACMultipleArm.QuartileElimination
import AppliedModelingLib.Foundations.Probability.IndependentIndicators
import AppliedModelingLib.Foundations.Probability.UniformHoeffding

/-!
# Fresh product batches for Quartile-Elimination

Each QE round assigns an independent finite Bernoulli batch to every arm that
is active at the start of that round.  The outer product is indexed by the
active subtype, so armwise score events are independent even when the active
set was selected by preceding rounds.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The independent finite batch drawn from one particular Bernoulli arm. -/
noncomputable def bernoulliArmBatchLaw {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ) :
    PMF (Fin sampleCount → Bool) := by
  let marginal : Fin sampleCount → Measure Bool := fun _ =>
    (bernoulliRewardLaw mean hmean arm).toMeasure
  letI : ∀ sample, IsProbabilityMeasure (marginal sample) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The one-arm batch PMF is its product of Bernoulli coordinate laws. -/
theorem bernoulliArmBatchLaw_toMeasure {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ) :
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure =
      Measure.pi (fun _ : Fin sampleCount => (bernoulliRewardLaw mean hmean arm).toMeasure) := by
  let marginal : Fin sampleCount → Measure Bool := fun _ =>
    (bernoulliRewardLaw mean hmean arm).toMeasure
  letI : ∀ sample, IsProbabilityMeasure (marginal sample) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/-- The labels inside a one-arm batch are mutually independent. -/
theorem iIndepFun_bernoulliArmBatchLabel {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ) :
    iIndepFun (fun sample : Fin sampleCount => fun labelTable => labelTable sample)
      (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure := by
  let marginal : Fin sampleCount → Measure Bool := fun _ =>
    (bernoulliRewardLaw mean hmean arm).toMeasure
  letI : ∀ sample, IsProbabilityMeasure (marginal sample) := fun _ => inferInstance
  rw [bernoulliArmBatchLaw_toMeasure]
  simpa only [marginal] using
    (iIndepFun_pi (X := fun _ : Fin sampleCount => (id : Bool → Bool))
      (μ := marginal) (fun _ => measurable_id.aemeasurable))

/-- A coordinate of a one-arm batch has the arm's Bernoulli reward law. -/
theorem map_bernoulliArmBatchLabel {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (sample : Fin sampleCount) :
    Measure.map (fun labelTable => labelTable sample)
      (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure =
        (bernoulliRewardLaw mean hmean arm).toMeasure := by
  rw [bernoulliArmBatchLaw_toMeasure]
  let marginal : Fin sampleCount → Measure Bool := fun _ =>
    (bernoulliRewardLaw mean hmean arm).toMeasure
  letI : ∀ index, IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun labelTable => labelTable sample) (Measure.pi marginal) = marginal sample
  exact (measurePreserving_eval marginal sample).map_eq

/-- The real-valued reward observed at a one-arm batch coordinate. -/
def bernoulliArmBatchObservation {sampleCount : ℕ}
    (labelTable : Fin sampleCount → Bool) (sample : Fin sampleCount) : ℝ :=
  binaryRatingScore (labelTable sample)

theorem measurable_bernoulliArmBatchObservation (sampleCount : ℕ)
    (sample : Fin sampleCount) :
    Measurable (fun labelTable : Fin sampleCount → Bool =>
      bernoulliArmBatchObservation labelTable sample) :=
  Measurable.of_discrete

theorem bernoulliArmBatchObservation_mem_Icc {sampleCount : ℕ}
    (labelTable : Fin sampleCount → Bool) (sample : Fin sampleCount) :
    bernoulliArmBatchObservation labelTable sample ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hlabel : labelTable sample with (_ | _)
  · norm_num [bernoulliArmBatchObservation, binaryRatingScore, hlabel]
  · norm_num [bernoulliArmBatchObservation, binaryRatingScore, hlabel]

theorem integral_bernoulliArmBatchObservation {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (sample : Fin sampleCount) :
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure[
      fun labelTable => bernoulliArmBatchObservation labelTable sample] = mean arm := by
  let coordinate : (Fin sampleCount → Bool) → Bool := fun labelTable => labelTable sample
  have hscore : (fun labelTable => bernoulliArmBatchObservation labelTable sample) =
      binaryRatingScore ∘ coordinate := by
    funext labelTable
    rfl
  rw [hscore]
  calc
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure[
        binaryRatingScore ∘ coordinate] =
        (Measure.map coordinate
          (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure)[binaryRatingScore] := by
      symm
      apply integral_map
      · exact (measurable_pi_apply sample).aemeasurable
      · exact Measurable.of_discrete.aestronglyMeasurable
    _ = (bernoulliRewardLaw mean hmean arm).toMeasure[binaryRatingScore] := by
      rw [map_bernoulliArmBatchLabel mean hmean arm sampleCount sample]
    _ = mean arm := by
      rw [← pmfExp_eq_integral_toMeasure]
      unfold pmfExp bernoulliRewardLaw
      simp [PMF.bernoulli_apply, binaryRatingScore]
      rfl

theorem ae_bernoulliArmBatchObservation_mem_Icc {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (sample : Fin sampleCount) :
    ∀ᵐ labelTable ∂(bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure,
      bernoulliArmBatchObservation labelTable sample ∈ Set.Icc (0 : ℝ) 1 :=
  Filter.Eventually.of_forall fun labelTable =>
    bernoulliArmBatchObservation_mem_Icc labelTable sample

/-- The observations within one arm's fresh batch are independent. -/
theorem iIndepFun_bernoulliArmBatchObservation {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ) :
    iIndepFun (fun sample : Fin sampleCount =>
      fun labelTable => bernoulliArmBatchObservation labelTable sample)
      (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure := by
  have hlabels := iIndepFun_bernoulliArmBatchLabel mean hmean arm sampleCount
  have hscores := hlabels.comp (fun _ => binaryRatingScore) (fun _ => Measurable.of_discrete)
  simpa [bernoulliArmBatchObservation, Function.comp_def] using hscores

/-- The empirical mean of one active arm in a QE round. -/
noncomputable def bernoulliArmBatchEmpiricalMean (sampleCount : ℕ)
    (labelTable : Fin sampleCount → Bool) : ℝ :=
  (∑ sample : Fin sampleCount, bernoulliArmBatchObservation labelTable sample) /
    (sampleCount : ℝ)

/-- A one-sided Hoeffding upper tail for one arm's fresh empirical batch. -/
theorem bernoulliArmBatch_centeredSum_upperTail {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (error : ℝ) (herror : 0 ≤ error) :
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure.real
      {labelTable | (sampleCount : ℝ) * error ≤
        ∑ sample : Fin sampleCount,
          (bernoulliArmBatchObservation labelTable sample -
            (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure[
              fun table => bernoulliArmBatchObservation table sample])} ≤
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure
  let observation : Fin sampleCount → (Fin sampleCount → Bool) → ℝ := fun sample =>
    fun labelTable => bernoulliArmBatchObservation labelTable sample
  simpa [law, observation] using
    (boundedIIndep_centeredSum_upperTail_finset law observation
      (iIndepFun_bernoulliArmBatchObservation mean hmean arm sampleCount)
      (fun sample => measurable_bernoulliArmBatchObservation sampleCount sample)
      (fun sample => ae_bernoulliArmBatchObservation_mem_Icc
        mean hmean arm sampleCount sample)
      ((sampleCount : ℝ) * error)
      (mul_nonneg (Nat.cast_nonneg sampleCount) herror))

/-- A one-sided Hoeffding lower tail for one arm's fresh empirical batch. -/
theorem bernoulliArmBatch_centeredSum_lowerTail {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (error : ℝ) (herror : 0 ≤ error) :
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure.real
      {labelTable | (∑ sample : Fin sampleCount,
          (bernoulliArmBatchObservation labelTable sample -
            (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure[
              fun table => bernoulliArmBatchObservation table sample])) ≤
          -(sampleCount : ℝ) * error} ≤
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure
  let observation : Fin sampleCount → (Fin sampleCount → Bool) → ℝ := fun sample =>
    fun labelTable => bernoulliArmBatchObservation labelTable sample
  simpa [law, observation] using
    (boundedIIndep_centeredSum_lowerTail_finset law observation
      (iIndepFun_bernoulliArmBatchObservation mean hmean arm sampleCount)
      (fun sample => measurable_bernoulliArmBatchObservation sampleCount sample)
      (fun sample => ae_bernoulliArmBatchObservation_mem_Icc
        mean hmean arm sampleCount sample)
      ((sampleCount : ℝ) * error)
      (mul_nonneg (Nat.cast_nonneg sampleCount) herror))

/-- The upper empirical-mean deviation of one arm obeys Hoeffding's bound. -/
theorem bernoulliArmBatch_empiricalMean_upperTail {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (hcount : 0 < sampleCount) (error : ℝ) (herror : 0 ≤ error) :
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure.real
      {labelTable | error <
        bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm} ≤
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure
  let observation : Fin sampleCount → (Fin sampleCount → Bool) → ℝ := fun sample =>
    fun labelTable => bernoulliArmBatchObservation labelTable sample
  have hsum : ∀ labelTable,
      (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) =
      (sampleCount : ℝ) *
        (bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm) := by
    intro labelTable
    dsimp [observation]
    calc
      (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) =
          ∑ sample : Fin sampleCount, (observation sample labelTable - mean arm) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [show law[observation sample] = mean arm by
              exact integral_bernoulliArmBatchObservation mean hmean arm sampleCount sample]
      _ = (sampleCount : ℝ) *
          (bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm) := by
            have hraw :
                (∑ sample : Fin sampleCount,
                  (bernoulliArmBatchObservation labelTable sample - mean arm)) =
                (sampleCount : ℝ) *
                  (bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm) := by
              unfold bernoulliArmBatchEmpiricalMean
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              have hcountReal : (sampleCount : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt hcount
              field_simp [hcountReal]
            simpa [observation] using hraw
  have hsubset : {labelTable | error <
      bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm} ⊆
      {labelTable | (sampleCount : ℝ) * error ≤
        ∑ sample : Fin sampleCount,
          (observation sample labelTable - law[observation sample])} := by
    intro labelTable hfailure
    change (sampleCount : ℝ) * error ≤
      ∑ sample : Fin sampleCount, (observation sample labelTable - law[observation sample])
    rw [hsum labelTable]
    have hcountReal : 0 < (sampleCount : ℝ) := by exact_mod_cast hcount
    exact le_of_lt (mul_lt_mul_of_pos_left hfailure hcountReal)
  exact (measureReal_mono hsubset).trans
    (bernoulliArmBatch_centeredSum_upperTail mean hmean arm sampleCount error herror)

/-- The lower empirical-mean deviation of one arm obeys Hoeffding's bound. -/
theorem bernoulliArmBatch_empiricalMean_lowerTail {Arm : Type*}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (arm : Arm) (sampleCount : ℕ)
    (hcount : 0 < sampleCount) (error : ℝ) (herror : 0 ≤ error) :
    (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure.real
      {labelTable | error <
        mean arm - bernoulliArmBatchEmpiricalMean sampleCount labelTable} ≤
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (bernoulliArmBatchLaw mean hmean arm sampleCount).toMeasure
  let observation : Fin sampleCount → (Fin sampleCount → Bool) → ℝ := fun sample =>
    fun labelTable => bernoulliArmBatchObservation labelTable sample
  have hsum : ∀ labelTable,
      (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) =
      (sampleCount : ℝ) *
        (bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm) := by
    intro labelTable
    dsimp [observation]
    calc
      (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) =
          ∑ sample : Fin sampleCount, (observation sample labelTable - mean arm) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [show law[observation sample] = mean arm by
              exact integral_bernoulliArmBatchObservation mean hmean arm sampleCount sample]
      _ = (sampleCount : ℝ) *
          (bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm) := by
            have hraw :
                (∑ sample : Fin sampleCount,
                  (bernoulliArmBatchObservation labelTable sample - mean arm)) =
                (sampleCount : ℝ) *
                  (bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm) := by
              unfold bernoulliArmBatchEmpiricalMean
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              have hcountReal : (sampleCount : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt hcount
              field_simp [hcountReal]
            simpa [observation] using hraw
  have hsubset : {labelTable | error <
      mean arm - bernoulliArmBatchEmpiricalMean sampleCount labelTable} ⊆
      {labelTable | (∑ sample : Fin sampleCount,
        (observation sample labelTable - law[observation sample])) ≤
          -(sampleCount : ℝ) * error} := by
    intro labelTable hfailure
    change (∑ sample : Fin sampleCount,
      (observation sample labelTable - law[observation sample])) ≤
        -(sampleCount : ℝ) * error
    rw [hsum labelTable]
    have hcountReal : 0 < (sampleCount : ℝ) := by exact_mod_cast hcount
    nlinarith [mul_lt_mul_of_pos_left hfailure hcountReal]
  exact (measureReal_mono hsubset).trans
    (bernoulliArmBatch_centeredSum_lowerTail mean hmean arm sampleCount error herror)

/-- The independent product of one fresh Bernoulli batch for each active arm. -/
noncomputable def quartileBernoulliBatchLaw {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) : PMF (active → Fin sampleCount → Bool) := by
  let marginal : active → Measure (Fin sampleCount → Bool) := fun arm =>
    (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure
  letI : ∀ arm, IsProbabilityMeasure (marginal arm) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The arm/sample coordinates of a QE round, in the product order used by
the sequential replay. -/
abbrev QuartileBatchCoordinate {Arm : Type*} (active : Finset Arm) (sampleCount : ℕ) :=
  Σ _ : active, Fin sampleCount

/-- Flatten a curried QE batch table into its arm/sample coordinate labels. -/
def quartileBatchUncurry {Arm : Type*} {active : Finset Arm} {sampleCount : ℕ}
    (batchTable : active → Fin sampleCount → Bool) :
    QuartileBatchCoordinate active sampleCount → Bool := fun coordinate =>
  batchTable coordinate.1 coordinate.2

/-- Rebuild a curried QE batch table from its flattened arm/sample labels. -/
def quartileBatchCurry {Arm : Type*} {active : Finset Arm} {sampleCount : ℕ}
    (labels : QuartileBatchCoordinate active sampleCount → Bool) :
    active → Fin sampleCount → Bool := fun arm sample =>
  labels ⟨arm, sample⟩

@[simp]
theorem quartileBatchUncurry_curry {Arm : Type*} {active : Finset Arm} {sampleCount : ℕ}
    (labels : QuartileBatchCoordinate active sampleCount → Bool) :
    quartileBatchUncurry (quartileBatchCurry labels) = labels := by
  funext coordinate
  rcases coordinate with ⟨arm, sample⟩
  rfl

@[simp]
theorem quartileBatchCurry_uncurry {Arm : Type*} {active : Finset Arm} {sampleCount : ℕ}
    (batchTable : active → Fin sampleCount → Bool) :
    quartileBatchCurry (quartileBatchUncurry batchTable) = batchTable := by
  funext arm sample
  rfl

theorem quartileBernoulliBatchLaw_toMeasure {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure =
      Measure.pi (fun arm : active =>
        (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure) := by
  let marginal : active → Measure (Fin sampleCount → Bool) := fun arm =>
    (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure
  letI : ∀ arm, IsProbabilityMeasure (marginal arm) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/-- The mass of a QE batch table is the independent product over all of its
arm/sample labels. -/
theorem quartileBernoulliBatchLaw_apply_curry {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) (labels : QuartileBatchCoordinate active sampleCount → Bool) :
    quartileBernoulliBatchLaw mean hmean active sampleCount (quartileBatchCurry labels) =
      ∏ coordinate : QuartileBatchCoordinate active sampleCount,
        bernoulliRewardLaw mean hmean coordinate.1.val (labels coordinate) := by
  calc
    quartileBernoulliBatchLaw mean hmean active sampleCount (quartileBatchCurry labels) =
        ∏ arm : active,
          (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure
            {labels' | labels' = fun sample => labels ⟨arm, sample⟩} := by
          rw [← (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure_apply_singleton
            (quartileBatchCurry labels) MeasurableSet.of_discrete]
          rw [quartileBernoulliBatchLaw_toMeasure, Measure.pi_singleton]
          apply Finset.prod_congr rfl
          intro arm _
          congr 1
    _ = ∏ arm : active, ∏ sample : Fin sampleCount,
          bernoulliRewardLaw mean hmean arm.val (labels ⟨arm, sample⟩) := by
          apply Finset.prod_congr rfl
          intro arm _
          rw [bernoulliArmBatchLaw_toMeasure]
          have hsingleton :
              {labels' | labels' = fun sample => labels ⟨arm, sample⟩} =
                {fun sample => labels ⟨arm, sample⟩} := by
            ext labels'
            simp
          rw [hsingleton, Measure.pi_singleton]
          apply Finset.prod_congr rfl
          intro sample _
          exact (bernoulliRewardLaw mean hmean arm.val).toMeasure_apply_singleton
            (labels ⟨arm, sample⟩) MeasurableSet.of_discrete
    _ = ∏ coordinate : QuartileBatchCoordinate active sampleCount,
          bernoulliRewardLaw mean hmean coordinate.1.val (labels coordinate) := by
          exact (Fintype.prod_sigma
            (fun coordinate : QuartileBatchCoordinate active sampleCount =>
              bernoulliRewardLaw mean hmean coordinate.1.val (labels coordinate))).symm

/-- Flattening a fresh QE batch produces exactly the heterogeneous product of
its Bernoulli arm/sample coordinate laws. -/
theorem quartileBernoulliBatchLaw_map_uncurry_eq_pmfPi
    {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).map quartileBatchUncurry =
      pmfPi (fun coordinate : QuartileBatchCoordinate active sampleCount =>
        bernoulliRewardLaw mean hmean coordinate.1.val) := by
  classical
  apply PMF.ext
  intro labels
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (quartileBatchCurry labels)]
  · rw [if_pos (quartileBatchUncurry_curry labels).symm]
    rw [quartileBernoulliBatchLaw_apply_curry, pmfPi_apply]
  · intro other _ hother
    have hnotMapped : quartileBatchUncurry other ≠ labels := by
      intro hequal
      have hinverse : other = quartileBatchCurry labels := by
        calc
          other = quartileBatchCurry (quartileBatchUncurry other) :=
            (quartileBatchCurry_uncurry other).symm
          _ = quartileBatchCurry labels := congrArg quartileBatchCurry hequal
      exact hother hinverse
    simp only [if_neg (Ne.symm hnotMapped)]
  · simp

/-- The armwise fresh batches in a QE round are mutually independent. -/
theorem iIndepFun_quartileBernoulliBatch {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) :
    iIndepFun (fun arm : active => fun batchTable => batchTable arm)
      (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure := by
  let marginal : active → Measure (Fin sampleCount → Bool) := fun arm =>
    (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure
  letI : ∀ arm, IsProbabilityMeasure (marginal arm) := fun _ => inferInstance
  rw [quartileBernoulliBatchLaw_toMeasure]
  simpa only [marginal] using
    (iIndepFun_pi (X := fun _ : active =>
      (id : (Fin sampleCount → Bool) → Fin sampleCount → Bool))
      (μ := marginal) (fun _ => measurable_id.aemeasurable))

/-- The marginal QE batch of one active arm is its independent one-arm batch. -/
theorem map_quartileBernoulliBatch {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) (arm : active) :
    Measure.map (fun batchTable => batchTable arm)
      (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure =
        (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure := by
  rw [quartileBernoulliBatchLaw_toMeasure]
  let marginal : active → Measure (Fin sampleCount → Bool) := fun index =>
    (bernoulliArmBatchLaw mean hmean index.val sampleCount).toMeasure
  letI : ∀ index, IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun batchTable => batchTable arm) (Measure.pi marginal) = marginal arm
  exact (measurePreserving_eval marginal arm).map_eq

/-- The total empirical score function supplied to the tie-broken QE rule. -/
noncomputable def quartileBernoulliBatchScore {Arm : Type*} (active : Finset Arm)
    (sampleCount : ℕ) (batchTable : active → Fin sampleCount → Bool) (arm : Arm) : ℝ := by
  classical
  exact if hmem : arm ∈ active then
    bernoulliArmBatchEmpiricalMean sampleCount (batchTable ⟨arm, hmem⟩)
  else 0

theorem quartileBernoulliBatchScore_eq_empiricalMean {Arm : Type*}
    (active : Finset Arm) (sampleCount : ℕ)
    (batchTable : active → Fin sampleCount → Bool) (arm : active) :
    quartileBernoulliBatchScore active sampleCount batchTable arm.val =
      bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) := by
  classical
  simp [quartileBernoulliBatchScore, arm.property]

/-- The tie-broken QE active set produced by a fresh round batch. -/
noncomputable def quartileEliminationFromBatch {Arm : Type*} [Fintype Arm]
    (active : Finset Arm) (sampleCount : ℕ)
    (batchTable : active → Fin sampleCount → Bool) : Finset Arm :=
  quartileEliminationSurvivors active
    (quartileBernoulliBatchScore active sampleCount batchTable)

/-- A deterministic true-mean maximizer within a nonempty active set. -/
noncomputable def finiteActiveMeanMaximizer {Arm : Type*} (mean : Arm → ℝ)
    (active : Finset Arm) [Nonempty active] : active :=
  finiteScoreMaximizer (fun arm : active => mean arm.val)

theorem mean_le_finiteActiveMeanMaximizer {Arm : Type*} (mean : Arm → ℝ)
    (active : Finset Arm) [Nonempty active] (arm : active) :
    mean arm.val ≤ mean (finiteActiveMeanMaximizer mean active).val :=
  score_le_finiteScoreMaximizer (fun arm : active => mean arm.val) arm

/-- The one-arm QE score upper tail, transported through the outer batch product. -/
theorem quartileBernoulliBatch_empiricalMean_upperTail {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) (arm : active) (hcount : 0 < sampleCount)
    (error : ℝ) (herror : 0 ≤ error) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | error <
        bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val} ≤
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  let armLaw := (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure
  let bad : Set (Fin sampleCount → Bool) := {labelTable | error <
    bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm.val}
  have hmap : Measure.map (fun batchTable => batchTable arm) law = armLaw :=
    map_quartileBernoulliBatch mean hmean active sampleCount arm
  have htransport : law.real ((fun batchTable => batchTable arm) ⁻¹' bad) = armLaw.real bad := by
    unfold Measure.real
    rw [← hmap, Measure.map_apply (measurable_pi_apply arm) MeasurableSet.of_discrete]
  change law.real ((fun batchTable => batchTable arm) ⁻¹' bad) ≤ _
  rw [htransport]
  exact bernoulliArmBatch_empiricalMean_upperTail mean hmean arm.val sampleCount
    hcount error herror

/-- The one-arm QE score lower tail, transported through the outer batch product. -/
theorem quartileBernoulliBatch_empiricalMean_lowerTail {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) (arm : active) (hcount : 0 < sampleCount)
    (error : ℝ) (herror : 0 ≤ error) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | error < mean arm.val -
        bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm)} ≤
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  let armLaw := (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure
  let bad : Set (Fin sampleCount → Bool) := {labelTable | error < mean arm.val -
    bernoulliArmBatchEmpiricalMean sampleCount labelTable}
  have hmap : Measure.map (fun batchTable => batchTable arm) law = armLaw :=
    map_quartileBernoulliBatch mean hmean active sampleCount arm
  have htransport : law.real ((fun batchTable => batchTable arm) ⁻¹' bad) = armLaw.real bad := by
    unfold Measure.real
    rw [← hmap, Measure.map_apply (measurable_pi_apply arm) MeasurableSet.of_discrete]
  change law.real ((fun batchTable => batchTable arm) ⁻¹' bad) ≤ _
  rw [htransport]
  exact bernoulliArmBatch_empiricalMean_lowerTail mean hmean arm.val sampleCount
    hcount error herror

/-- Hoeffding's two-sided tail for one arm inside a fresh QE batch. -/
theorem quartileBernoulliBatch_empiricalMean_failure_probability
    {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) (arm : active) (hcount : 0 < sampleCount)
    (error : ℝ) (herror : 0 ≤ error) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | error <
        |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val|} ≤
        2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  let upperEvent : Set (active → Fin sampleCount → Bool) := {batchTable | error <
    bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val}
  let lowerEvent : Set (active → Fin sampleCount → Bool) := {batchTable | error <
    mean arm.val - bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm)}
  let absoluteEvent : Set (active → Fin sampleCount → Bool) := {batchTable | error <
    |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val|}
  have hsubset : absoluteEvent ⊆ upperEvent ∪ lowerEvent := by
    intro batchTable hfailure
    dsimp only [absoluteEvent] at hfailure
    by_cases hnonneg : 0 ≤
        bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val
    · left
      dsimp only [upperEvent]
      simpa [abs_of_nonneg hnonneg] using hfailure
    · right
      have hnegative :
          bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val < 0 :=
        lt_of_not_ge hnonneg
      change error <
        |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val| at hfailure
      change error < mean arm.val -
        bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm)
      rw [abs_of_neg hnegative] at hfailure
      linarith
  have hupper : law.real upperEvent ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    dsimp only [law, upperEvent]
    exact quartileBernoulliBatch_empiricalMean_upperTail mean hmean active sampleCount arm
      hcount error herror
  have hlower : law.real lowerEvent ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    dsimp only [law, lowerEvent]
    exact quartileBernoulliBatch_empiricalMean_lowerTail mean hmean active sampleCount arm
      hcount error herror
  change law.real absoluteEvent ≤ _
  calc
    law.real absoluteEvent ≤ law.real (upperEvent ∪ lowerEvent) := measureReal_mono hsubset
    _ ≤ law.real upperEvent + law.real lowerEvent := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- Union-bound concentration across all arms in a fresh QE batch. -/
theorem quartileBernoulliBatch_uniformEmpiricalMean_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (sampleCount : ℕ) (hcount : 0 < sampleCount)
    (error : ℝ) (herror : 0 ≤ error) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | ∃ arm : active, error <
        |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val|} ≤
        (active.card : ℝ) * 2 *
          Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
            (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  classical
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  let bad : active → Set (active → Fin sampleCount → Bool) := fun arm =>
    {batchTable | error <
      |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val|}
  have hbad : ∀ arm, law.real (bad arm) ≤
      2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    intro arm
    exact quartileBernoulliBatch_empiricalMean_failure_probability mean hmean active sampleCount
      arm hcount error herror
  have hbadUnion : {batchTable | ∃ arm : active, error <
      |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val|} =
        ⋃ arm ∈ (Finset.univ : Finset active), bad arm := by
    ext batchTable
    simp [bad]
  rw [hbadUnion]
  calc
    law.real (⋃ arm ∈ (Finset.univ : Finset active), bad arm) ≤
        ∑ arm ∈ (Finset.univ : Finset active), law.real (bad arm) := by
          simpa using (measureReal_biUnion_finset_le (μ := law)
            (Finset.univ : Finset active) bad)
    _ ≤ ∑ _arm ∈ (Finset.univ : Finset active),
        2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
          apply Finset.sum_le_sum
          intro arm _
          exact hbad arm
    _ = (active.card : ℝ) * 2 *
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
          simp [mul_assoc, mul_comm]

/--
If every empirical mean in a QE batch is accurate, the tie-broken survivor
set retains an arm within twice the accuracy of any specified active arm.
-/
theorem quartileEliminationFromBatch_no_near_reference_probability_of_uniformEstimate
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (reference : active) (sampleCount : ℕ) (hcount : 0 < sampleCount)
    (error : ℝ) (herror : 0 ≤ error) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | ¬ ∃ survivor, survivor ∈
          quartileEliminationFromBatch active sampleCount batchTable ∧
        mean reference.val - 2 * error ≤ mean survivor} ≤
      (active.card : ℝ) * 2 *
        Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
          (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  have hsubset : {batchTable | ¬ ∃ survivor, survivor ∈
      quartileEliminationFromBatch active sampleCount batchTable ∧
      mean reference.val - 2 * error ≤ mean survivor} ⊆
      {batchTable | ∃ arm : active, error <
        |bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) - mean arm.val|} := by
    intro batchTable hfailure
    by_contra hnotbad
    simp only [Set.mem_setOf_eq, not_exists] at hnotbad
    have hactive : active.Nonempty := ⟨reference.val, reference.property⟩
    have haccurate : ∀ arm ∈ active,
        |quartileBernoulliBatchScore active sampleCount batchTable arm - mean arm| ≤ error := by
      intro arm harm
      have hnotbadArm := hnotbad ⟨arm, harm⟩
      rw [quartileBernoulliBatchScore_eq_empiricalMean active sampleCount batchTable
        ⟨arm, harm⟩]
      exact le_of_not_gt hnotbadArm
    obtain ⟨survivor, hsurvivor, hnear⟩ :=
      exists_quartileEliminationSurvivor_mean_near_best_of_uniformEstimate active mean
        (quartileBernoulliBatchScore active sampleCount batchTable) error hactive haccurate
    apply hfailure
    refine ⟨survivor, ?_, hnear reference.val reference.property⟩
    exact hsurvivor
  exact (measureReal_mono hsubset).trans
    (quartileBernoulliBatch_uniformEmpiricalMean_failure_probability mean hmean active
      sampleCount hcount error herror)

/--
An active arm is counted when it is more than `2 * error` below a reference
mean but its fresh empirical score reaches the reference's `error`-lower
threshold.
-/
noncomputable def quartileBadOvershootIndicator {Arm : Type*}
    (mean : Arm → ℝ) (reference : Arm) (error : ℝ) (sampleCount : ℕ)
    (arm : Arm) (labelTable : Fin sampleCount → Bool) : ℝ :=
  if mean arm < mean reference - 2 * error ∧
      mean reference - error ≤ bernoulliArmBatchEmpiricalMean sampleCount labelTable
  then 1 else 0

theorem measurable_quartileBadOvershootIndicator {Arm : Type*}
    (mean : Arm → ℝ) (reference : Arm) (error : ℝ) (sampleCount : ℕ) (arm : Arm) :
    Measurable (quartileBadOvershootIndicator mean reference error sampleCount arm) :=
  Measurable.of_discrete

theorem quartileBadOvershootIndicator_zero_or_one {Arm : Type*}
    (mean : Arm → ℝ) (reference : Arm) (error : ℝ) (sampleCount : ℕ) (arm : Arm)
    (labelTable : Fin sampleCount → Bool) :
    quartileBadOvershootIndicator mean reference error sampleCount arm labelTable = 0 ∨
      quartileBadOvershootIndicator mean reference error sampleCount arm labelTable = 1 := by
  unfold quartileBadOvershootIndicator
  split <;> simp

theorem quartileBadOvershootIndicator_eq_one {Arm : Type*}
    (mean : Arm → ℝ) (reference : Arm) (error : ℝ) (sampleCount : ℕ) (arm : Arm)
    (labelTable : Fin sampleCount → Bool)
    (hbad : mean arm < mean reference - 2 * error)
    (hover : mean reference - error ≤
      bernoulliArmBatchEmpiricalMean sampleCount labelTable) :
    quartileBadOvershootIndicator mean reference error sampleCount arm labelTable = 1 := by
  unfold quartileBadOvershootIndicator
  simp [hbad, hover]

theorem quartileBadOvershootIndicator_nonneg {Arm : Type*}
    (mean : Arm → ℝ) (reference : Arm) (error : ℝ) (sampleCount : ℕ) (arm : Arm)
    (labelTable : Fin sampleCount → Bool) :
    0 ≤ quartileBadOvershootIndicator mean reference error sampleCount arm labelTable := by
  rcases quartileBadOvershootIndicator_zero_or_one mean reference error sampleCount arm labelTable
    with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- The bad-overshoot indicators inherit independence from the armwise QE batches. -/
theorem iIndepFun_quartileBadOvershootIndicator {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (reference : Arm) (error : ℝ) (sampleCount : ℕ) :
    iIndepFun (fun arm : active =>
      fun batchTable => quartileBadOvershootIndicator mean reference error sampleCount arm.val
        (batchTable arm))
      (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure := by
  have hbatch := iIndepFun_quartileBernoulliBatch mean hmean active sampleCount
  let transform : active → (Fin sampleCount → Bool) → ℝ := fun arm =>
    quartileBadOvershootIndicator mean reference error sampleCount arm.val
  have hmeasurable : ∀ arm, Measurable (transform arm) := fun arm =>
    measurable_quartileBadOvershootIndicator mean reference error sampleCount arm.val
  simpa [transform, Function.comp_def] using hbatch.comp transform hmeasurable

/-- A bad-overshoot indicator has the one-arm Hoeffding mean bound. -/
theorem integral_quartileBadOvershootIndicator_le {Arm : Type*} [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (reference : Arm) (error : ℝ) (sampleCount : ℕ) (hcount : 0 < sampleCount)
    (herror : 0 ≤ error) (arm : active) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure[
      fun batchTable => quartileBadOvershootIndicator mean reference error sampleCount arm.val
        (batchTable arm)] ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  change (∫ batchTable,
    quartileBadOvershootIndicator mean reference error sampleCount arm.val
      (batchTable arm) ∂law) ≤ _
  by_cases hbad : mean arm.val < mean reference - 2 * error
  · let overshoot : Set (Fin sampleCount → Bool) := {labelTable |
      mean reference - error ≤ bernoulliArmBatchEmpiricalMean sampleCount labelTable}
    have hindicator :
        (fun batchTable : active → Fin sampleCount → Bool =>
          quartileBadOvershootIndicator mean reference error sampleCount arm.val
          (batchTable arm)) =
        overshoot.indicator (fun _ => (1 : ℝ)) ∘
          (fun batchTable : active → Fin sampleCount → Bool => batchTable arm) := by
      funext batchTable
      by_cases hscore : mean reference - error ≤
          bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm)
      · have hscore' : mean reference ≤
            bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) + error := by
          linarith
        simp [quartileBadOvershootIndicator, overshoot, hbad, hscore, hscore']
      · have hnotScore' : ¬ mean reference ≤
            bernoulliArmBatchEmpiricalMean sampleCount (batchTable arm) + error := by
          intro hscore'
          apply hscore
          linarith
        simp [quartileBadOvershootIndicator, overshoot, hbad, hscore, hnotScore']
    rw [hindicator]
    have hpush :
        (∫ batchTable,
          overshoot.indicator (fun _ => (1 : ℝ)) (batchTable arm) ∂law) =
        ∫ labelTable,
          overshoot.indicator (fun _ => (1 : ℝ)) labelTable ∂
            Measure.map (fun batchTable : active → Fin sampleCount → Bool => batchTable arm) law := by
      symm
      apply integral_map
      · exact (measurable_pi_apply arm).aemeasurable
      · exact Measurable.of_discrete.aestronglyMeasurable
    change (∫ batchTable,
      overshoot.indicator (fun _ => (1 : ℝ)) (batchTable arm) ∂law) ≤ _
    rw [hpush, map_quartileBernoulliBatch mean hmean active sampleCount arm]
    have hintegral :
        (∫ labelTable, overshoot.indicator (fun _ => (1 : ℝ)) labelTable ∂
          (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure) =
        (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure.real overshoot := by
      simpa using MeasureTheory.integral_indicator_one (μ :=
        (bernoulliArmBatchLaw mean hmean arm.val sampleCount).toMeasure)
        MeasurableSet.of_discrete
    rw [hintegral]
    apply (measureReal_mono ?_).trans
      (bernoulliArmBatch_empiricalMean_upperTail mean hmean arm.val sampleCount
        hcount error herror)
    intro labelTable hover
    change error < bernoulliArmBatchEmpiricalMean sampleCount labelTable - mean arm.val
    simp only [overshoot, Set.mem_setOf_eq] at hover
    linarith
  · have hzero : (fun batchTable : active → Fin sampleCount → Bool =>
        quartileBadOvershootIndicator mean reference error sampleCount
        arm.val (batchTable arm)) = fun _ => 0 := by
      funext batchTable
      simp [quartileBadOvershootIndicator, hbad]
    rw [hzero]
    rw [integral_zero]
    exact (Real.exp_pos _).le

/--
One fresh tie-broken QE round loses every arm within `2 * error` of a current
mean maximizer only through either that maximizer's lower deviation or a
simultaneous overshoot by every retained arm.  The second event has the finite
independent-indicator Chernoff bound displayed on the right.
-/
theorem quartileEliminationFromBatch_no_near_maximum_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (reference : active) (hmaximum : ∀ competitor : active, mean competitor.val ≤ mean reference.val)
    (sampleCount : ℕ) (hcount : 0 < sampleCount) (error t : ℝ)
    (herror : 0 ≤ error) (ht : 0 ≤ t) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | ¬ ∃ survivor, survivor ∈
          quartileEliminationFromBatch active sampleCount batchTable ∧
        mean reference.val - 2 * error ≤ mean survivor} ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) +
      Real.exp (-t * (quartileSurvivorCount active.card : ℝ) +
        (active.card : ℝ) * ((Real.exp t - 1) *
          Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
            (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))))) := by
  let law := (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure
  let score : (active → Fin sampleCount → Bool) → Arm → ℝ := fun batchTable =>
    quartileBernoulliBatchScore active sampleCount batchTable
  let survivors : (active → Fin sampleCount → Bool) → Finset Arm := fun batchTable =>
    quartileEliminationFromBatch active sampleCount batchTable
  let overshoot : active → (active → Fin sampleCount → Bool) → ℝ := fun arm batchTable =>
    quartileBadOvershootIndicator mean reference.val error sampleCount arm.val (batchTable arm)
  let lowerEvent : Set (active → Fin sampleCount → Bool) := {batchTable | error <
    mean reference.val - bernoulliArmBatchEmpiricalMean sampleCount (batchTable reference)}
  let overshootEvent : Set (active → Fin sampleCount → Bool) := {batchTable |
    (quartileSurvivorCount active.card : ℝ) ≤ ∑ arm, overshoot arm batchTable}
  let failureEvent : Set (active → Fin sampleCount → Bool) := {batchTable | ¬ ∃ survivor,
    survivor ∈ survivors batchTable ∧ mean reference.val - 2 * error ≤ mean survivor}
  have houtputSubset : ∀ batchTable, survivors batchTable ⊆ active := by
    intro batchTable
    simpa [survivors, quartileEliminationFromBatch] using
      (quartileEliminationSurvivors_subset active (score batchTable))
  have hfailureSubset : failureEvent ⊆ lowerEvent ∪ overshootEvent := by
    intro batchTable hfailure
    by_cases hlower : batchTable ∈ lowerEvent
    · exact Or.inl hlower
    · right
      have hnoGood : ∀ survivor, survivor ∈ survivors batchTable →
          ¬ mean reference.val - 2 * error ≤ mean survivor := by
        intro survivor hsurvivor hnear
        exact hfailure ⟨survivor, hsurvivor, hnear⟩
      have hreferenceEliminated : reference.val ∉ survivors batchTable := by
        intro hreferenceSurvives
        have hcontradiction := hnoGood reference.val hreferenceSurvives
        apply hcontradiction
        linarith
      have hreferenceScore : mean reference.val - error ≤
          bernoulliArmBatchEmpiricalMean sampleCount (batchTable reference) := by
        dsimp [lowerEvent] at hlower
        have hlowerLe : mean reference.val -
            bernoulliArmBatchEmpiricalMean sampleCount (batchTable reference) ≤ error :=
          le_of_not_gt hlower
        linarith
      let fullOvershoot : Arm → ℝ := fun arm =>
        if hmem : arm ∈ active then overshoot ⟨arm, hmem⟩ batchTable else 0
      have hsurvivorOvershoots : ∀ survivor, survivor ∈ survivors batchTable →
          fullOvershoot survivor = 1 := by
        intro survivor hsurvivor
        let survivorActive : active := ⟨survivor, houtputSubset batchTable hsurvivor⟩
        have hbad : mean survivor < mean reference.val - 2 * error :=
          lt_of_not_ge (hnoGood survivor hsurvivor)
        have horder : score batchTable reference.val ≤ score batchTable survivor := by
          exact score_le_quartileEliminationSurvivor_of_reference_eliminated active
            (score batchTable) reference.property (by simpa [survivors] using hreferenceEliminated)
            (by simpa [survivors] using hsurvivor)
        have horderEmpirical :
            bernoulliArmBatchEmpiricalMean sampleCount (batchTable reference) ≤
              bernoulliArmBatchEmpiricalMean sampleCount (batchTable survivorActive) := by
          have hreferenceEq : score batchTable reference.val =
              bernoulliArmBatchEmpiricalMean sampleCount (batchTable reference) := by
            exact quartileBernoulliBatchScore_eq_empiricalMean active sampleCount batchTable reference
          have hsurvivorEq : score batchTable survivor =
              bernoulliArmBatchEmpiricalMean sampleCount (batchTable survivorActive) := by
            exact quartileBernoulliBatchScore_eq_empiricalMean active sampleCount batchTable survivorActive
          rw [hreferenceEq, hsurvivorEq] at horder
          exact horder
        have hover : mean reference.val - error ≤
            bernoulliArmBatchEmpiricalMean sampleCount (batchTable survivorActive) :=
          hreferenceScore.trans horderEmpirical
        have hone := quartileBadOvershootIndicator_eq_one mean reference.val error sampleCount
          survivor (batchTable survivorActive) hbad hover
        have hsurvivorActive : survivor ∈ active := houtputSubset batchTable hsurvivor
        simpa [fullOvershoot, overshoot, hsurvivorActive] using hone
      have hfullNonneg : ∀ arm ∈ active, arm ∉ survivors batchTable → 0 ≤ fullOvershoot arm := by
        intro arm harm _
        simp only [fullOvershoot, dif_pos harm]
        exact quartileBadOvershootIndicator_nonneg mean reference.val error sampleCount arm
          (batchTable ⟨arm, harm⟩)
      have hsumLower : (survivors batchTable).card ≤
          ∑ arm ∈ active, fullOvershoot arm := by
        calc
          (survivors batchTable).card = ∑ _arm ∈ survivors batchTable, (1 : ℝ) := by simp
          _ = ∑ arm ∈ survivors batchTable, fullOvershoot arm := by
            apply Finset.sum_congr rfl
            intro arm harm
            rw [hsurvivorOvershoots arm harm]
          _ ≤ ∑ arm ∈ active, fullOvershoot arm :=
            Finset.sum_le_sum_of_subset_of_nonneg (houtputSubset batchTable) hfullNonneg
      have hfullSum : (∑ arm ∈ active, fullOvershoot arm) =
          ∑ arm : active, overshoot arm batchTable := by
        have hsubtype : ∀ arm : Arm, arm ∈ active ↔ arm ∈ active := fun _ => Iff.rfl
        rw [Finset.sum_subtype active hsubtype]
        apply Finset.sum_congr rfl
        intro arm _
        simp [fullOvershoot]
      change (quartileSurvivorCount active.card : ℝ) ≤ ∑ arm, overshoot arm batchTable
      rw [← hfullSum]
      rw [show (quartileSurvivorCount active.card : ℝ) =
          (survivors batchTable).card by
            rw [show survivors batchTable = quartileEliminationSurvivors active
              (score batchTable) by rfl, quartileEliminationSurvivors_card]]
      exact_mod_cast hsumLower
  have hlower : law.real lowerEvent ≤
      Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
    dsimp [law, lowerEvent]
    exact quartileBernoulliBatch_empiricalMean_lowerTail mean hmean active sampleCount
      reference hcount error herror
  have hovershoot : law.real overshootEvent ≤
      Real.exp (-t * (quartileSurvivorCount active.card : ℝ) +
        (active.card : ℝ) * ((Real.exp t - 1) *
          Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
            (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))))) := by
    have hchernoff := independentIndicatorSum_ge_probability_exponential law overshoot
      (Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))))
      (quartileSurvivorCount active.card : ℝ) t
      (iIndepFun_quartileBadOvershootIndicator mean hmean active reference.val error sampleCount)
      (fun _ => Measurable.of_discrete)
      (fun arm batchTable =>
        quartileBadOvershootIndicator_zero_or_one mean reference.val error sampleCount arm.val
          (batchTable arm))
      (fun arm => integral_quartileBadOvershootIndicator_le mean hmean active reference.val
        error sampleCount hcount herror arm)
      ht
    dsimp [overshootEvent]
    rw [Fintype.card_coe] at hchernoff
    exact hchernoff
  change law.real failureEvent ≤ _
  calc
    law.real failureEvent ≤ law.real (lowerEvent ∪ overshootEvent) :=
      measureReal_mono hfailureSubset
    _ ≤ law.real lowerEvent + law.real overshootEvent := measureReal_union_le _ _
    _ ≤ _ := add_le_add hlower hovershoot

end ZhouChenLi2014OptimalPACMultipleArm
