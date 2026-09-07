import ZhouChenLi2014OptimalPACMultipleArm.QuartileSequentialPolicy
import ZhouChenLi2014OptimalPACMultipleArm.QuartileSourceUniformFinal

/-!
# Literal sequential QE followed by the source uniform final stage

The QE prefix is now an actual finite history-dependent Bernoulli policy.  This
file attaches its decoded terminal state to the source's tagged uniform-final
kernel and proves that the resulting joint PMF is exactly the previously
verified fresh-QE-plus-final experiment.  It also defines the corresponding
single finite QE-plus-final procedure, proves its QE-prefix and conditional
final replay laws, and identifies its returned-arm PMF with the returned arm
read from that source joint experiment.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The final-horizon portion of a trace split after a QE prefix. -/
def quartileSourceSequentialUniformFinalSuffix
    (qeBudget finalBudget : ℕ)
    (rewards : Fin (qeBudget + finalBudget) → Bool) : Fin finalBudget → Bool :=
  fun position => rewards (Fin.natAdd qeBudget position)

@[simp]
theorem quartileSourceSequentialUniformFinalSuffix_append
    (qeBudget finalBudget : ℕ)
    (history : Fin qeBudget → Bool) (suffix : Fin finalBudget → Bool) :
    quartileSourceSequentialUniformFinalSuffix qeBudget finalBudget
      (Fin.append history suffix) = suffix := by
  funext position
  simp [quartileSourceSequentialUniformFinalSuffix, Fin.append]

@[simp]
theorem rewardTracePrefix_append
    (qeBudget finalBudget : ℕ)
    (history : Fin qeBudget → Bool) (suffix : Fin finalBudget → Bool) :
    rewardTracePrefix qeBudget finalBudget (Fin.append history suffix) = history := by
  funext position
  simp [rewardTracePrefix, Fin.append]

/-- The literal finite policy that runs the chronological source QE prefix and
then replays the history-selected uniform final batch.  The final horizon is
the finite maximum over all survivor sets; unused suffix pulls are inert and
are marginalized by the proved conditional final-replay theorem. -/
noncomputable def quartileSourceSequentialUniformFinalProcedure
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) +
        quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal) where
  pull := fun round history =>
    if hqe : round.val < Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) then
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial).pull
        ⟨round.val, hqe⟩
        (fun previous => history ⟨previous.val, by simpa using previous.isLt⟩)
    else
      let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
      let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
      let qeRewards : Fin qeBudget → Bool := fun position =>
        history (Fin.castLE (Nat.le_of_not_gt hqe) position)
      let active := quartileSourceSequentialState roundCount totalBudget initial qeRewards
        roundCount
      letI : Nonempty active :=
        (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
          qeRewards roundCount).to_subtype
      let finalRound : Fin finalBudget := ⟨round.val - qeBudget, by omega⟩
      let sampleCount := quartileUniformFinalSampleCount epsilon deltaFinal active
      let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
      if hfinal : finalRound.val < localBudget then
        ((uniformBatchCoordinateEquiv active sampleCount).symm
          ⟨finalRound.val, hfinal⟩).1.val
      else Classical.choice (inferInstance : Nonempty Arm)
  output := fun rewards =>
    let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
    let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
    let qeRewards := rewardTracePrefix qeBudget finalBudget rewards
    let active := quartileSourceSequentialState roundCount totalBudget initial qeRewards
      roundCount
    let finalRewards := quartileSourceSequentialUniformFinalSuffix qeBudget finalBudget rewards
    quartileUniformFinalPaddedTraceOutput epsilon deltaFinal active finalRewards

/-- The literal combined policy uses no more than the source QE total budget
plus its fixed padded final-stage cap. -/
theorem quartileSourceSequentialUniformFinalProcedure_pullBudget_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) +
        quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal ≤
      totalBudget + quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal := by
  exact Nat.add_le_add_right
    (quartileSourceSequentialSlot_card_le_totalBudget roundCount totalBudget) _

/-- The source algorithmic pull count after a specified QE history: all
scheduled QE slots, followed by exactly the uniform samples for its terminal
survivor set.  Unlike the fixed-horizon replay procedure, this count excludes
inert coordinates introduced solely to obtain one common Lean trace carrier. -/
noncomputable def quartileSourceSequentialUniformFinalPullCount
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (epsilon deltaFinal : ℝ) : ℕ :=
  let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount
  Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) +
    Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon deltaFinal active))

/-- Once QE has reached its source terminal condition, the unpadded source
execution uses at most its declared QE total plus the final-batch cap over
three-arm survivor sets. -/
theorem quartileSourceSequentialUniformFinalPullCount_le_terminalMax
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (epsilon deltaFinal : ℝ) (hroundCount : initial.card ≤ roundCount) :
    quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        epsilon deltaFinal ≤
      totalBudget + quartileUniformFinalTerminalMaxPullBudget Arm epsilon deltaFinal := by
  let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount
  have hqe : Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) ≤ totalBudget :=
    quartileSourceSequentialSlot_card_le_totalBudget roundCount totalBudget
  have hterminal : active.card ≤ 3 := by
    dsimp [active]
    exact quartileSourceSequentialState_card_le_three roundCount totalBudget initial qeHistory
      hroundCount
  have hfinal : Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon deltaFinal active)) ≤
      quartileUniformFinalTerminalMaxPullBudget Arm epsilon deltaFinal :=
    quartileUniformFinalPullBudget_le_terminalMax epsilon deltaFinal active hterminal
  simpa [quartileSourceSequentialUniformFinalPullCount, active] using
    Nat.add_le_add hqe hfinal

/-- Cardinality-only version of the terminal source resource bound.  Its
final term is the maximum of the four possible uniform-batch costs for zero,
one, two, or three surviving arms, so it carries no dependence on the original
arm count. -/
theorem quartileSourceSequentialUniformFinalPullCount_le_threeArmBudget
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (epsilon deltaFinal : ℝ) (hroundCount : initial.card ≤ roundCount) :
    quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        epsilon deltaFinal ≤
      totalBudget + quartileUniformFinalThreeArmPullBudget epsilon deltaFinal := by
  let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount
  have hqe : Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) ≤ totalBudget :=
    quartileSourceSequentialSlot_card_le_totalBudget roundCount totalBudget
  have hterminal : active.card ≤ 3 := by
    dsimp [active]
    exact quartileSourceSequentialState_card_le_three roundCount totalBudget initial qeHistory
      hroundCount
  have hfinal : Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon deltaFinal active)) ≤
      quartileUniformFinalThreeArmPullBudget epsilon deltaFinal :=
    quartileUniformFinalPullBudget_le_threeArmBudget epsilon deltaFinal active hterminal
  simpa [quartileSourceSequentialUniformFinalPullCount, active] using
    Nat.add_le_add hqe hfinal

/-- Splitting a complete trace at the QE boundary exposes the literal final
selection from the survivor set reconstructed from its QE prefix. -/
theorem quartileSourceSequentialUniformFinalProcedure_output_append
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (suffix : Fin (quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal) → Bool) :
    (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
      epsilon deltaFinal).output (Fin.append qeHistory suffix) =
      quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
        (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)
        suffix := by
  rw [quartileSourceSequentialUniformFinalProcedure]
  simp only [rewardTracePrefix_append,
    quartileSourceSequentialUniformFinalSuffix_append]

/-- The QE portion of the combined policy has exactly the reward law of the
standalone literal QE policy.  This is a prefix statement: final-stage pulls
cannot change the law of the already revealed QE history. -/
theorem adaptiveQuartileSourceSequentialUniformFinalProcedureQEPrefixLaw_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    adaptiveBernoulliRewardPrefixLaw mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget))
      (Nat.le_add_right _ _) =
      adaptiveBernoulliRewardLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial) := by
  simpa [adaptiveBernoulliRewardLaw] using
    (adaptiveBernoulliRewardPrefixLaw_congr_pulls_prefix mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget))
      (Nat.le_add_right _ _) (Nat.le_refl _) (by
        intro round history
        simp only [quartileSourceSequentialUniformFinalProcedure]
        rw [dif_pos round.isLt]))

/-- After any fixed QE reward history, the remaining portion of the combined
policy is the padded sequential replay of that history's survivor-specific
uniform final kernel. -/
theorem adaptiveQuartileSourceSequentialUniformFinalProcedureFinalSuffixLaw_eq_paddedTraceLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory
      roundCount
    let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
    adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) qeHistory
      finalBudget (by omega) =
      quartileUniformFinalPaddedTraceLaw mean hmean epsilon deltaFinal active := by
  dsimp
  let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
  let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory
    roundCount
  have hactive : active.Nonempty :=
    quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
      qeHistory roundCount
  letI : Nonempty active := hactive.to_subtype
  let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
  let sampleCount := quartileUniformFinalSampleCount epsilon deltaFinal active
  let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
  have hlocalBudget : localBudget ≤ finalBudget := by
    simpa [localBudget] using
      (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon deltaFinal active)
  let combined := quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial
    hinitial epsilon deltaFinal
  let padded := canonicalQuartileUniformFinalPaddedArmProcedure epsilon deltaFinal active
    finalBudget hlocalBudget
  let continuation := adaptiveBernoulliContinuationProcedure combined qeBudget
    (Nat.le_add_right _ _) qeHistory
  have hcontinuationBudget : finalBudget ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) +
        quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal - qeBudget := by
    dsimp [qeBudget, finalBudget]
    omega
  have hpulls : ∀ (round : Fin finalBudget) (history : Fin round.val → Bool),
      continuation.pull ⟨round.val, round.isLt.trans_le hcontinuationBudget⟩ history =
        padded.pull round history := by
    intro round history
    have hnotQE : ¬ qeBudget + round.val < qeBudget := by omega
    have hprefix : ∀ position : Fin qeBudget,
        Fin.append qeHistory history
          (Fin.castLE (Nat.le_add_right qeBudget round.val) position) = qeHistory position := by
      intro position
      have hcast : Fin.castLE (Nat.le_add_right qeBudget round.val) position =
          Fin.castAdd round.val position := by
        apply Fin.ext
        rfl
      rw [hcast]
      simp [Fin.append]
    have hstate :
        quartileSourceSequentialState roundCount totalBudget initial
          (fun position => Fin.append qeHistory history
            (Fin.castLE (Nat.le_add_right qeBudget round.val) position)) roundCount =
          active := by
      simp only [hprefix]
      rfl
    simp only [continuation, adaptiveBernoulliContinuationProcedure]
    simp only [combined, quartileSourceSequentialUniformFinalProcedure]
    rw [dif_neg hnotQE]
    simp only [qeBudget, finalBudget] at hprefix ⊢
    simp only [Nat.add_sub_cancel_left]
    rw [hstate]
    simp [padded, canonicalQuartileUniformFinalPaddedArmProcedure, sampleCount,
      localBudget]
  have hcontinuationLaw :
      adaptiveBernoulliRewardPrefixLaw mean hmean continuation finalBudget hcontinuationBudget =
        adaptiveBernoulliRewardLaw mean hmean padded := by
    simpa [adaptiveBernoulliRewardLaw] using
      (adaptiveBernoulliRewardPrefixLaw_congr_pulls_prefix mean hmean continuation padded
        finalBudget hcontinuationBudget (Nat.le_refl _) hpulls)
  calc
    adaptiveBernoulliRewardSuffixLaw mean hmean combined qeBudget qeHistory finalBudget
        (by omega) =
        adaptiveBernoulliRewardPrefixLaw mean hmean continuation finalBudget
          hcontinuationBudget := by
      rw [adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix]
    _ = adaptiveBernoulliRewardLaw mean hmean padded := hcontinuationLaw
    _ = quartileUniformFinalPaddedTraceLaw mean hmean epsilon deltaFinal active := by
      rw [quartileUniformFinalPaddedTraceLaw, dif_pos hactive]

/-- The complete source-shaped experiment on a fixed carrier: a literal QE
reward history together with the padded raw final trace conditioned on the
survivor set that history determines. -/
noncomputable def quartileSourceSequentialUniformFinalHistoryTraceJointLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    PMF ((Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) ×
      (Fin (quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal) → Bool)) :=
  (adaptiveBernoulliRewardLaw mean hmean
    (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)).bind
    (fun qeHistory =>
      (quartileUniformFinalPaddedTraceLaw mean hmean epsilon deltaFinal
        (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)).map
        (fun finalTrace => (qeHistory, finalTrace)))

/-- The actual combined policy has exactly the output law of the literal QE
trace followed by its history-selected padded final trace. -/
theorem adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_historyTraceJoint
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    (adaptiveBernoulliRewardLaw mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)).map
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal).output =
      (quartileSourceSequentialUniformFinalHistoryTraceJointLaw mean hmean
        roundCount totalBudget initial hinitial epsilon deltaFinal).map
        (fun historyTrace => quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
          (quartileSourceSequentialState roundCount totalBudget initial historyTrace.1 roundCount)
          historyTrace.2) := by
  classical
  let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
  let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
  let combined := quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial
    hinitial epsilon deltaFinal
  calc
    (adaptiveBernoulliRewardLaw mean hmean combined).map combined.output =
        (adaptiveBernoulliRewardPrefixLaw mean hmean combined qeBudget
          (Nat.le_add_right _ _)).bind
          (fun qeHistory =>
            (adaptiveBernoulliRewardSuffixLaw mean hmean combined qeBudget qeHistory
              finalBudget (by omega)).map
              (fun finalTrace => quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
                (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)
                finalTrace)) := by
      rw [adaptiveBernoulliRewardLaw,
        adaptiveBernoulliRewardPrefixLaw_eq_bind_suffix mean hmean combined qeBudget
          finalBudget (by omega)]
      rw [PMF.map_bind]
      apply congrArg (fun continuation =>
        (adaptiveBernoulliRewardPrefixLaw mean hmean combined qeBudget
          (Nat.le_add_right _ _)).bind continuation)
      funext qeHistory
      rw [PMF.map_comp]
      apply congrArg (fun output =>
        PMF.map output
          (adaptiveBernoulliRewardSuffixLaw mean hmean combined qeBudget qeHistory
            finalBudget (by omega)))
      funext finalTrace
      exact quartileSourceSequentialUniformFinalProcedure_output_append
        roundCount totalBudget initial hinitial epsilon deltaFinal qeHistory finalTrace
    _ = (adaptiveBernoulliRewardLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)).bind
        (fun qeHistory =>
          (quartileUniformFinalPaddedTraceLaw mean hmean epsilon deltaFinal
            (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)).map
            (fun finalTrace => quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
              (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)
              finalTrace)) := by
      rw [adaptiveQuartileSourceSequentialUniformFinalProcedureQEPrefixLaw_eq]
      apply congrArg (fun continuation =>
        (adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)).bind
          continuation)
      funext qeHistory
      rw [adaptiveQuartileSourceSequentialUniformFinalProcedureFinalSuffixLaw_eq_paddedTraceLaw]
    _ = (quartileSourceSequentialUniformFinalHistoryTraceJointLaw mean hmean
        roundCount totalBudget initial hinitial epsilon deltaFinal).map
        (fun historyTrace => quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
          (quartileSourceSequentialState roundCount totalBudget initial historyTrace.1 roundCount)
          historyTrace.2) := by
      rw [quartileSourceSequentialUniformFinalHistoryTraceJointLaw, PMF.map_bind]
      apply congrArg (fun continuation =>
        (adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)).bind
          continuation)
      funext qeHistory
      rw [PMF.map_comp]
      rfl

/-- After any fixed QE reward history, mapping the remaining padded trace to
the active uniform-batch coordinates gives the source's tagged final kernel. -/
theorem adaptiveQuartileSourceSequentialUniformFinalProcedureFinalSuffixLaw_map_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory
      roundCount
    letI : Nonempty active :=
      (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
        qeHistory roundCount).to_subtype
    let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
    let sampleCount := quartileUniformFinalSampleCount epsilon deltaFinal active
    let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
    let hlocalBudget : localBudget ≤ finalBudget := by
      simpa [localBudget] using
        (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon deltaFinal active)
    (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) qeHistory
      finalBudget (by omega)).map
      (fun suffix => ⟨active,
        uniformBatchTraceLabels sampleCount
          (rewardTracePrefixLE localBudget finalBudget hlocalBudget suffix)⟩) =
      canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal active := by
  dsimp
  let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
  let active := quartileSourceSequentialState roundCount totalBudget initial qeHistory
    roundCount
  letI : Nonempty active :=
    (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
      qeHistory roundCount).to_subtype
  let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
  let sampleCount := quartileUniformFinalSampleCount epsilon deltaFinal active
  let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
  have hlocalBudget : localBudget ≤ finalBudget := by
    simpa [localBudget] using
      (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon deltaFinal active)
  let combined := quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial
    hinitial epsilon deltaFinal
  let padded := canonicalQuartileUniformFinalPaddedArmProcedure epsilon deltaFinal active
    finalBudget hlocalBudget
  let continuation := adaptiveBernoulliContinuationProcedure combined qeBudget
    (Nat.le_add_right _ _) qeHistory
  have hcontinuationBudget : finalBudget ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) +
        quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal - qeBudget := by
    dsimp [qeBudget, finalBudget]
    omega
  have hpulls : ∀ (round : Fin finalBudget) (history : Fin round.val → Bool),
      continuation.pull ⟨round.val, round.isLt.trans_le hcontinuationBudget⟩ history =
        padded.pull round history := by
    intro round history
    have hnotQE : ¬ qeBudget + round.val < qeBudget := by omega
    have hprefix : ∀ position : Fin qeBudget,
        Fin.append qeHistory history
          (Fin.castLE (Nat.le_add_right qeBudget round.val) position) = qeHistory position := by
      intro position
      have hcast : Fin.castLE (Nat.le_add_right qeBudget round.val) position =
          Fin.castAdd round.val position := by
        apply Fin.ext
        rfl
      rw [hcast]
      simp [Fin.append]
    have hstate :
        quartileSourceSequentialState roundCount totalBudget initial
          (fun position => Fin.append qeHistory history
            (Fin.castLE (Nat.le_add_right qeBudget round.val) position)) roundCount =
          active := by
      simp only [hprefix]
      rfl
    simp only [continuation, adaptiveBernoulliContinuationProcedure]
    simp only [combined, quartileSourceSequentialUniformFinalProcedure]
    rw [dif_neg hnotQE]
    simp only [qeBudget, finalBudget] at hprefix ⊢
    simp only [Nat.add_sub_cancel_left]
    rw [hstate]
    simp [padded, canonicalQuartileUniformFinalPaddedArmProcedure, sampleCount,
      localBudget]
  have hcontinuationLaw :
      adaptiveBernoulliRewardPrefixLaw mean hmean continuation finalBudget hcontinuationBudget =
        adaptiveBernoulliRewardLaw mean hmean padded := by
    simpa [adaptiveBernoulliRewardLaw] using
      (adaptiveBernoulliRewardPrefixLaw_congr_pulls_prefix mean hmean continuation padded
        finalBudget hcontinuationBudget (Nat.le_refl _) hpulls)
  calc
    (adaptiveBernoulliRewardSuffixLaw mean hmean combined qeBudget qeHistory finalBudget
        (by omega)).map
        (fun suffix => ⟨active,
          uniformBatchTraceLabels sampleCount
            (rewardTracePrefixLE localBudget finalBudget hlocalBudget suffix)⟩) =
        (adaptiveBernoulliRewardPrefixLaw mean hmean continuation finalBudget
          hcontinuationBudget).map
          (fun suffix => ⟨active,
            uniformBatchTraceLabels sampleCount
              (rewardTracePrefixLE localBudget finalBudget hlocalBudget suffix)⟩) := by
      rw [adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix]
    _ = (adaptiveBernoulliRewardLaw mean hmean padded).map
          (fun suffix => ⟨active,
            uniformBatchTraceLabels sampleCount
              (rewardTracePrefixLE localBudget finalBudget hlocalBudget suffix)⟩) := by
      rw [hcontinuationLaw]
    _ = canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal active := by
      symm
      exact canonicalQuartileUniformFinalOutcomeLaw_eq_paddedArmSequentialReplay
        mean hmean epsilon deltaFinal active finalBudget hlocalBudget

/-- At the full QE boundary, the chronological boundary decoder has the same
survivor component as the direct sequential-state replay on the QE trace. -/
theorem quartileSourceSequentialBoundaryStateFailure_full_fst_eq_state
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount =
        Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
      simpa [quartileSourceSequentialRoundPrefixLength] using
        (quartileSourceSequentialSlot_card roundCount totalBudget).symm
    (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
      roundCount (fun position => rewards (Fin.cast hboundary position))).1 =
      quartileSourceSequentialState roundCount totalBudget initial rewards roundCount := by
  dsimp
  let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount =
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    simpa [quartileSourceSequentialRoundPrefixLength] using
      (quartileSourceSequentialSlot_card roundCount totalBudget).symm
  rw [quartileSourceSequentialBoundaryStateFailure_fst_eq_completePrefixState
    mean error roundCount totalBudget initial roundCount
    (fun position => rewards (Fin.cast hboundary position)) (Nat.le_refl _)]
  congr 1
  funext position
  have hposition : position.val < quartileSourceSequentialRoundPrefixLength totalBudget roundCount := by
    simpa [hboundary] using position.isLt
  rw [show quartileSourceSequentialCompletePrefixExtension
      (fun earlier => rewards (Fin.cast hboundary earlier)) position =
      rewards (Fin.cast hboundary ⟨position.val, hposition⟩) by
        simp [quartileSourceSequentialCompletePrefixExtension, hposition]]
  apply congrArg rewards
  apply Fin.ext
  rfl

/-- Decode the complete reward trace of the combined finite policy into the
QE state/flag and tagged final-batch outcome used by the source-facing joint
experiment. -/
noncomputable def quartileSourceSequentialUniformFinalJointOutput
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) +
      quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal) → Bool) :
    (Finset Arm × Bool) × canonicalQuartileUniformFinalOutcome Arm epsilon deltaFinal := by
  let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
  let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
  let qeRewards : Fin qeBudget → Bool := fun position =>
    rewards (Fin.castAdd finalBudget position)
  let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount = qeBudget := by
    simpa [qeBudget, quartileSourceSequentialRoundPrefixLength] using
      (quartileSourceSequentialSlot_card roundCount totalBudget).symm
  let stateFailure := quartileSourceSequentialBoundaryStateFailure mean error
    roundCount totalBudget initial roundCount
    (fun position => qeRewards (Fin.cast hboundary position))
  let active := quartileSourceSequentialState roundCount totalBudget initial qeRewards roundCount
  let hstate : stateFailure.1 = active := by
    simpa [stateFailure] using
      (quartileSourceSequentialBoundaryStateFailure_full_fst_eq_state
        mean error roundCount totalBudget initial qeRewards)
  letI : Nonempty active :=
    (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
      qeRewards roundCount).to_subtype
  let sampleCount := quartileUniformFinalSampleCount epsilon deltaFinal active
  let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
  let hlocalBudget : localBudget ≤ finalBudget := by
    simpa [localBudget] using
      (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon deltaFinal active)
  let finalRewards : Fin localBudget → Bool := fun position =>
    rewards (Fin.natAdd qeBudget
      ⟨position.val, position.isLt.trans_le hlocalBudget⟩)
  let finalLabels : UniformBatchCoordinate stateFailure.1
      (quartileUniformFinalSampleCount epsilon deltaFinal stateFailure.1) → Bool := by
    rw [hstate]
    exact uniformBatchTraceLabels sampleCount finalRewards
  exact (stateFailure,
    ⟨stateFailure.1, finalLabels⟩)

/-- The joint law obtained by running the literal sequential QE prefix and
then drawing the source's tagged uniform final batch conditional on its
decoded active state. -/
noncomputable def quartileSourceSequentialUniformFinalJointLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    PMF ((Finset Arm × Bool) × canonicalQuartileUniformFinalOutcome Arm epsilon deltaFinal) := by
  let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount =
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    simpa [quartileSourceSequentialRoundPrefixLength] using
      (quartileSourceSequentialSlot_card roundCount totalBudget).symm
  exact
    ((adaptiveBernoulliRewardPrefixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) (Nat.le_refl _)).map
      (fun trace =>
        quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
          roundCount (fun position => trace (Fin.cast hboundary position)))).bind
      (fun stateFailure =>
        (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal stateFailure.1).map
          (fun outcome => (stateFailure, outcome)))

/-- Marginalizing a history-selected padded final trace yields exactly the
selected-arm law of the source's tagged sequential QE-plus-final joint PMF. -/
theorem quartileSourceSequentialUniformFinalHistoryTraceJointLaw_map_output_eq_jointLaw_map_output
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    (quartileSourceSequentialUniformFinalHistoryTraceJointLaw mean hmean
      roundCount totalBudget initial hinitial epsilon deltaFinal).map
      (fun historyTrace => quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
        (quartileSourceSequentialState roundCount totalBudget initial historyTrace.1 roundCount)
        historyTrace.2) =
      (quartileSourceSequentialUniformFinalJointLaw mean hmean error roundCount totalBudget initial
        hinitial epsilon deltaFinal).map
        (fun stateOutcome => canonicalQuartileUniformFinalOutput epsilon deltaFinal
          stateOutcome.1.1 stateOutcome.2) := by
  classical
  let qeBudget := Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)
  let finalBudget := quartileUniformFinalMaxPullBudget Arm epsilon deltaFinal
  let qeLaw := adaptiveBernoulliRewardLaw mean hmean
    (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
  let stateFailure : (Fin qeBudget → Bool) → Finset Arm × Bool := fun qeHistory =>
    let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount = qeBudget := by
      simpa [qeBudget, quartileSourceSequentialRoundPrefixLength] using
        (quartileSourceSequentialSlot_card roundCount totalBudget).symm
    quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
      roundCount (fun position => qeHistory (Fin.cast hboundary position))
  have hstate : ∀ qeHistory : Fin qeBudget → Bool,
      (stateFailure qeHistory).1 =
        quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount := by
    intro qeHistory
    simpa [stateFailure] using
      (quartileSourceSequentialBoundaryStateFailure_full_fst_eq_state
        mean error roundCount totalBudget initial qeHistory)
  calc
    (quartileSourceSequentialUniformFinalHistoryTraceJointLaw mean hmean
        roundCount totalBudget initial hinitial epsilon deltaFinal).map
        (fun historyTrace => quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
          (quartileSourceSequentialState roundCount totalBudget initial historyTrace.1 roundCount)
          historyTrace.2) =
        qeLaw.bind (fun qeHistory =>
          (quartileUniformFinalPaddedTraceLaw mean hmean epsilon deltaFinal
            (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)).map
            (quartileUniformFinalPaddedTraceOutput epsilon deltaFinal
              (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount))) := by
      rw [quartileSourceSequentialUniformFinalHistoryTraceJointLaw, PMF.map_bind]
      apply congrArg (fun continuation => qeLaw.bind continuation)
      funext qeHistory
      rw [PMF.map_comp]
      rfl
    _ = qeLaw.bind (fun qeHistory =>
          (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal
            (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)).map
            (canonicalQuartileUniformFinalOutput epsilon deltaFinal
              (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount))) := by
      apply congrArg (fun continuation => qeLaw.bind continuation)
      funext qeHistory
      exact quartileUniformFinalPaddedTraceLaw_map_output_eq_outcomeLaw_map_output
        mean hmean epsilon deltaFinal
        (quartileSourceSequentialState roundCount totalBudget initial qeHistory roundCount)
        (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
          qeHistory roundCount)
    _ = qeLaw.bind (fun qeHistory =>
          (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal
            (stateFailure qeHistory).1).map
            (canonicalQuartileUniformFinalOutput epsilon deltaFinal
              (stateFailure qeHistory).1)) := by
      apply congrArg (fun continuation => qeLaw.bind continuation)
      funext qeHistory
      rw [hstate qeHistory]
    _ = (quartileSourceSequentialUniformFinalJointLaw mean hmean error roundCount totalBudget
        initial hinitial epsilon deltaFinal).map
        (fun stateOutcome => canonicalQuartileUniformFinalOutput epsilon deltaFinal
          stateOutcome.1.1 stateOutcome.2) := by
      rw [quartileSourceSequentialUniformFinalJointLaw, PMF.map_bind, PMF.bind_map]
      apply congrArg (fun continuation => qeLaw.bind continuation)
      funext qeHistory
      simp only [Function.comp_apply]
      rw [PMF.map_comp]
      rfl

/-- The returned arm of the single literal QE-plus-final policy has exactly
the same finite PMF as the returned arm read from the source's tagged joint
experiment. -/
theorem adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_jointLaw_output
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    (adaptiveBernoulliRewardLaw mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)).map
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal).output =
      (quartileSourceSequentialUniformFinalJointLaw mean hmean error roundCount totalBudget initial
        hinitial epsilon deltaFinal).map
        (fun stateOutcome => canonicalQuartileUniformFinalOutput epsilon deltaFinal
          stateOutcome.1.1 stateOutcome.2) := by
  rw [adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_historyTraceJoint]
  exact quartileSourceSequentialUniformFinalHistoryTraceJointLaw_map_output_eq_jointLaw_map_output
    mean hmean error roundCount totalBudget initial hinitial epsilon deltaFinal

/-- The literal sequential QE-plus-final construction has exactly the joint
law formed from the fresh adaptive QE state law and the source final kernel. -/
theorem quartileSourceSequentialUniformFinalJointLaw_eq_fresh
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (epsilon deltaFinal : ℝ) :
    quartileSourceSequentialUniformFinalJointLaw mean hmean error roundCount totalBudget initial
      hinitial epsilon deltaFinal =
      (freshQuartileRoundsStateLaw mean error initial
        (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun round _ active => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget round active
            (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount).bind
        (fun stateFailure =>
          (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal stateFailure.1).map
            (fun outcome => (stateFailure, outcome))) := by
  let finalKernel : (Finset Arm × Bool) →
      PMF ((Finset Arm × Bool) × canonicalQuartileUniformFinalOutcome Arm epsilon deltaFinal) :=
    fun stateFailure =>
      (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal stateFailure.1).map
        (fun outcome => (stateFailure, outcome))
  simpa [quartileSourceSequentialUniformFinalJointLaw, finalKernel] using
    congrArg (fun stateLaw => stateLaw.bind finalKernel)
      (adaptiveQuartileSourceSequentialQERewardLaw_map_boundaryStateFailure_eq_freshQuartileRoundsStateLaw
        mean hmean error roundCount totalBudget initial hinitial)

/-- At the source QE error schedule, the literal sequential QE-plus-final
joint law is the already-verified `quartileSourceUniformFinalJointLaw`. -/
theorem quartileSourceSequentialUniformFinalJointLaw_eq_source
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (deltaQE epsilon deltaFinal : ℝ) :
    quartileSourceSequentialUniformFinalJointLaw mean hmean
      (quartileSourceError totalBudget initial.card deltaQE)
      roundCount totalBudget initial hinitial epsilon deltaFinal =
      quartileSourceUniformFinalJointLaw mean hmean roundCount totalBudget initial
        deltaQE epsilon deltaFinal := by
  rw [quartileSourceSequentialUniformFinalJointLaw_eq_fresh]
  rfl

/-- With the terminal-aware source radius, the literal sequential experiment
has exactly the terminal-aware QE-plus-final joint PMF. -/
theorem quartileSourceSequentialUniformFinalJointLaw_eq_terminal
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (deltaQE epsilon deltaFinal : ℝ) :
    quartileSourceSequentialUniformFinalJointLaw mean hmean
      (quartileSourceTerminalError totalBudget initial.card deltaQE)
      roundCount totalBudget initial hinitial epsilon deltaFinal =
      quartileSourceTerminalUniformFinalJointLaw mean hmean roundCount totalBudget initial
        deltaQE epsilon deltaFinal := by
  rw [quartileSourceSequentialUniformFinalJointLaw_eq_fresh]
  rfl

/-- The literal policy's output PMF can therefore be read from the
terminal-aware source joint law as well. -/
theorem adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_terminalJoint_output
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (deltaQE epsilon deltaFinal : ℝ) :
    (adaptiveBernoulliRewardLaw mean hmean
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal)).map
      (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget initial hinitial
        epsilon deltaFinal).output =
      (quartileSourceTerminalUniformFinalJointLaw mean hmean roundCount totalBudget initial
        deltaQE epsilon deltaFinal).map
        (fun stateOutcome => canonicalQuartileUniformFinalOutput epsilon deltaFinal
          stateOutcome.1.1 stateOutcome.2) := by
  rw [adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_jointLaw_output
    mean hmean (quartileSourceTerminalError totalBudget initial.card deltaQE)
    roundCount totalBudget initial hinitial epsilon deltaFinal]
  rw [quartileSourceSequentialUniformFinalJointLaw_eq_terminal]

end ZhouChenLi2014OptimalPACMultipleArm
