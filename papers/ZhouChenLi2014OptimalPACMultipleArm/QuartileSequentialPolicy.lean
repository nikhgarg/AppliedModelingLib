import ZhouChenLi2014OptimalPACMultipleArm.QuartileSequentialSlots
import ZhouChenLi2014OptimalPACMultipleArm.QuartileBatchPolicy

/-!
# Sequential replay of source Quartile-Elimination

This file gives a literal finite adaptive pull policy for the QE prefix of
Zhou--Chen--Li's `K = 1` construction.  Each source round has its fixed
budget block.  After the active set is reconstructed from earlier blocks, the
first `|S_r| * floor (Q_r / |S_r|)` coordinates query its active arms in a
fixed order; the remainder of the block is inert padding.  Thus the policy
horizon is the sum of the source round budgets, rather than a rectangular
round-by-arm carrier.

The subsequent law-identification theorem is intentionally separate: this
file fixes the concrete history-dependent procedure and its exact source
budget before showing that its mapped reward law is the fresh-QE PMF.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL

noncomputable section

/-- Extend a revealed reward prefix to the fixed QE horizon by assigning
`false` to unrevealed coordinates.  The replay state used at a current source
round depends only on earlier round blocks, so this total extension is a
convenient way to express a policy using the finite-prefix interface. -/
noncomputable def quartileSourceSequentialPrefixExtension
    {pullBudget : ℕ} (round : Fin pullBudget) (history : Fin round.val → Bool) :
    Fin pullBudget → Bool := fun position =>
  if hposition : position.val < round.val then
    history ⟨position.val, hposition⟩
  else false

/-- The extension agrees with every previously revealed reward. -/
theorem quartileSourceSequentialPrefixExtension_apply_castLT
    {pullBudget : ℕ} (round : Fin pullBudget) (history : Fin round.val → Bool)
    (earlier : Fin round.val) :
    quartileSourceSequentialPrefixExtension round history
      (Fin.castLT earlier (Nat.lt_trans earlier.isLt round.isLt)) = history earlier := by
  simp [quartileSourceSequentialPrefixExtension]

/-- Complete an arbitrary numerical prefix with `false`.  Unlike the
position-indexed policy helper above, this version is available at a block
boundary even when that boundary is the full finite horizon. -/
noncomputable def quartileSourceSequentialCompletePrefixExtension
    {prefixCount totalCount : ℕ} (history : Fin prefixCount → Bool) :
    Fin totalCount → Bool := fun position =>
  if hposition : position.val < prefixCount then
    history ⟨position.val, hposition⟩
  else false

/-- The completed numerical prefix agrees with every original coordinate that
is within its declared length. -/
theorem quartileSourceSequentialCompletePrefixExtension_apply_castLE
    {prefixCount totalCount : ℕ} (history : Fin prefixCount → Bool)
    (hprefix : prefixCount ≤ totalCount) (earlier : Fin prefixCount) :
    quartileSourceSequentialCompletePrefixExtension history
      (Fin.castLE hprefix earlier) = history earlier := by
  simp [quartileSourceSequentialCompletePrefixExtension]

/-- Read the batch coordinate assigned to one active arm and one of its
per-arm QE samples from a complete sequential trace. -/
noncomputable def quartileSourceSequentialBatchTable
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    active → Fin (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active) →
      Bool := fun arm sample =>
  rewards ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm
    ⟨⟨round, hround⟩,
      ⟨(quartileBatchCoordinateEquiv active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
          ⟨arm, sample⟩).val,
        (quartileBatchCoordinateEquiv active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
          ⟨arm, sample⟩).isLt.trans_le
          (by
            rw [quartileBatchCoordinate_card]
            exact quartilePerArmSampleCount_total_le
              (quartileSourceRoundBudget totalBudget) round active)⟩⟩)

/-- Extract all chronological source slots belonging to one fixed QE round. -/
noncomputable def quartileSourceSequentialRoundTrace
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    Fin (quartileSourceRoundBudget totalBudget round) → Bool := fun slot =>
  rewards ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm
    ⟨round, slot⟩)

/-- The global chronological position of a slot in a specified source QE
round. -/
noncomputable def quartileSourceSequentialRoundPosition
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (slot : Fin (quartileSourceRoundBudget totalBudget round)) :
    Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) :=
  (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm ⟨round, slot⟩

@[simp]
theorem quartileSourceSequentialChronologicalSlotEquiv_roundPosition
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (slot : Fin (quartileSourceRoundBudget totalBudget round)) :
    quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
      (quartileSourceSequentialRoundPosition roundCount totalBudget round slot) = ⟨round, slot⟩ :=
  (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).apply_symm_apply _

/-- The direct position of a source-round slot is the sum of all earlier
round budgets plus its within-round coordinate. -/
theorem quartileSourceSequentialRoundPosition_val
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (slot : Fin (quartileSourceRoundBudget totalBudget round)) :
    (quartileSourceSequentialRoundPosition roundCount totalBudget round slot).val =
      quartileSourceSequentialRoundPrefixLength totalBudget round.val + slot.val := by
  unfold quartileSourceSequentialRoundPosition
  rw [quartileSourceSequentialChronologicalSlotEquiv_symm_apply]
  rfl

/-- The same source-round position constructed directly from the numerical
prefix length and within-round coordinate. -/
noncomputable def quartileSourceSequentialRoundPrefixPosition
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (slot : Fin (quartileSourceRoundBudget totalBudget round)) :
    Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) :=
  ⟨quartileSourceSequentialRoundPrefixLength totalBudget round.val + slot.val,
    (Nat.add_lt_add_left slot.isLt _).trans_le
      (quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
        roundCount totalBudget round)⟩

/-- The direct prefix-sum position is the chronology equivalence's position
for that exact source-round slot. -/
theorem quartileSourceSequentialRoundPrefixPosition_eq_roundPosition
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (slot : Fin (quartileSourceRoundBudget totalBudget round)) :
    quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round slot =
      quartileSourceSequentialRoundPosition roundCount totalBudget round slot := by
  apply Fin.ext
  exact (quartileSourceSequentialRoundPosition_val roundCount totalBudget round slot).symm

/-- Restrict one source round's slot trace to the arm/sample coordinates that
the floored QE allocation actually consumes.  The remaining round slots are
the inert padding governed by the prefix-marginal theorem. -/
noncomputable def quartileSourceSequentialAllocatedRoundTrace
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    Fin (Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))) → Bool :=
  fun coordinate =>
    quartileSourceSequentialRoundTrace roundCount totalBudget ⟨round, hround⟩ rewards
      ⟨coordinate.val, coordinate.isLt.trans_le (by
        rw [quartileBatchCoordinate_card]
        exact quartilePerArmSampleCount_total_le
          (quartileSourceRoundBudget totalBudget) round active)⟩

/-- The batch table read by the sequential QE state is exactly the curried
version of the allocated prefix of that round's chronological reward block. -/
theorem quartileSourceSequentialBatchTable_eq_curry_allocatedRoundTrace
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    quartileSourceSequentialBatchTable roundCount totalBudget round hround active rewards =
      quartileBatchCurry
        (quartileBatchTraceLabels active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
          (quartileSourceSequentialAllocatedRoundTrace roundCount totalBudget round hround active
            rewards)) := by
  funext arm sample
  unfold quartileSourceSequentialBatchTable quartileBatchCurry quartileBatchTraceLabels
    quartileSourceSequentialAllocatedRoundTrace quartileSourceSequentialRoundTrace
  congr 1

/-- The allocated chronological trace is the inequality-indexed prefix of the
literal `Q_r` source block. -/
theorem quartileSourceSequentialAllocatedRoundTrace_eq_prefixLE_roundTrace
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    quartileSourceSequentialAllocatedRoundTrace roundCount totalBudget round hround active rewards =
      rewardTracePrefixLE
        (Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))
        (quartileSourceRoundBudget totalBudget round)
        (by
          rw [quartileBatchCoordinate_card]
          exact quartilePerArmSampleCount_total_le
            (quartileSourceRoundBudget totalBudget) round active)
        (quartileSourceSequentialRoundTrace roundCount totalBudget ⟨round, hround⟩ rewards) := by
  funext coordinate
  unfold quartileSourceSequentialAllocatedRoundTrace rewardTracePrefixLE
  apply congrArg (quartileSourceSequentialRoundTrace roundCount totalBudget ⟨round, hround⟩ rewards)
  apply Fin.ext
  rfl

/-- The deterministic QE survivor set after a specified number of source
rounds, reconstructed from the corresponding coordinates of a complete trace.
The out-of-range branch makes the recurrence total; all source-policy calls
use a completed count at most `roundCount`. -/
noncomputable def quartileSourceSequentialState
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    ℕ → Finset Arm
  | 0 => initial
  | completed + 1 =>
      let active := quartileSourceSequentialState roundCount totalBudget initial rewards completed
      if hround : completed < roundCount then
        quartileEliminationFromBatch active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) completed active)
          (quartileSourceSequentialBatchTable roundCount totalBudget completed hround active rewards)
      else active

/-- Nonempty initial active sets remain nonempty throughout the deterministic
sequential QE replay. -/
theorem quartileSourceSequentialState_nonempty
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    ∀ completed, (quartileSourceSequentialState roundCount totalBudget initial rewards completed).Nonempty := by
  intro completed
  induction completed with
  | zero => simpa [quartileSourceSequentialState] using hinitial
  | succ completed ih =>
      simp only [quartileSourceSequentialState]
      split
      · exact quartileEliminationSurvivors_nonempty _ _ ih
      · exact ih

/-- The reconstructed sequential state has the same score-independent
cardinality recurrence as Quartile-Elimination itself.  This is the pathwise
termination fact used when the source switches to its small final batch. -/
theorem quartileSourceSequentialState_card_eq_iter
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    ∀ completed, completed ≤ roundCount →
      (quartileSourceSequentialState roundCount totalBudget initial rewards completed).card =
        quartileSurvivorCountIter completed initial.card := by
  intro completed
  induction completed with
  | zero =>
      intro _
      rfl
  | succ completed ih =>
      intro hcompleted
      have hprevious : completed ≤ roundCount := Nat.le_of_succ_le hcompleted
      have hround : completed < roundCount := Nat.lt_of_succ_le hcompleted
      rw [quartileSourceSequentialState, dif_pos hround,
        quartileEliminationFromBatch, quartileEliminationSurvivors_card, ih hprevious,
        quartileSurvivorCountIter_succ_eq_update]

/-- Once the source has run at least one QE round per initial arm, every
pathwise reconstructed terminal state has at most three survivors. -/
theorem quartileSourceSequentialState_card_le_three
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (hroundCount : initial.card ≤ roundCount) :
    (quartileSourceSequentialState roundCount totalBudget initial rewards roundCount).card ≤ 3 := by
  rw [quartileSourceSequentialState_card_eq_iter roundCount totalBudget initial rewards
    roundCount (Nat.le_refl _)]
  exact quartileSurvivorCountIter_le_three_of_le_roundCount roundCount initial.card hroundCount

/-- Reconstructed QE state after `completed` rounds depends only on the
source-slot rewards from strictly earlier round blocks.  This isolates the
chronological-prefix fact needed to identify the adaptive policy law. -/
theorem quartileSourceSequentialState_eq_of_agree_before
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (first second :
      Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    ∀ completed,
      (∀ slot : quartileSourceSequentialSlot roundCount totalBudget,
        slot.1.val < completed →
          first ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm slot) =
            second ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm slot)) →
      quartileSourceSequentialState roundCount totalBudget initial first completed =
        quartileSourceSequentialState roundCount totalBudget initial second completed := by
  intro completed
  induction completed with
  | zero =>
      intro _
      rfl
  | succ completed ih =>
      intro hagree
      have hprevious :
          quartileSourceSequentialState roundCount totalBudget initial first completed =
            quartileSourceSequentialState roundCount totalBudget initial second completed :=
        ih (by
          intro slot hslot
          exact hagree slot (Nat.lt_trans hslot (Nat.lt_succ_self completed)))
      simp only [quartileSourceSequentialState]
      rw [hprevious]
      split
      · rename_i hround
        have htable :
            quartileSourceSequentialBatchTable roundCount totalBudget completed hround
              (quartileSourceSequentialState roundCount totalBudget initial second completed) first =
            quartileSourceSequentialBatchTable roundCount totalBudget completed hround
              (quartileSourceSequentialState roundCount totalBudget initial second completed) second := by
          funext arm sample
          unfold quartileSourceSequentialBatchTable
          exact hagree ⟨⟨completed, hround⟩, _⟩ (Nat.lt_succ_self completed)
        rw [htable]
      · rfl

/-- The reconstructed active state at a source round depends only on the
chronological reward prefix ending before that round's budget block. -/
theorem quartileSourceSequentialState_eq_of_agree_before_roundPrefix
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (round : Fin roundCount)
    (first second :
      Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (hagree : ∀ position : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val),
      first (Fin.castLE (by
        apply Nat.le_trans (Nat.le_add_right _ _)
        exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
          roundCount totalBudget round) position) =
      second (Fin.castLE (by
        apply Nat.le_trans (Nat.le_add_right _ _)
        exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
          roundCount totalBudget round) position)) :
    quartileSourceSequentialState roundCount totalBudget initial first round.val =
      quartileSourceSequentialState roundCount totalBudget initial second round.val := by
  apply quartileSourceSequentialState_eq_of_agree_before roundCount totalBudget initial
    first second round.val
  intro earlier hearlier
  have hindex : ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm
      earlier).val < quartileSourceSequentialRoundPrefixLength totalBudget round.val := by
    rw [quartileSourceSequentialChronologicalSlotEquiv_symm_apply]
    exact quartileSourceSequentialSlotIndex_lt_roundPrefixLength_of_round_lt earlier round hearlier
  let prefixPosition : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) :=
    ⟨((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm earlier).val,
      hindex⟩
  have hcast : Fin.castLE (by
      apply Nat.le_trans (Nat.le_add_right _ _)
      exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
        roundCount totalBudget round) prefixPosition =
      (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm earlier := by
    apply Fin.ext
    rfl
  simpa only [hcast] using hagree prefixPosition

/-- At every position of a source round, the incoming reconstructed state is
unchanged by the rewards already observed in that same round.  It is the
state determined by the numerical prefix ending at that round boundary. -/
theorem quartileSourceSequentialState_prefixExtension_append_eq_completePrefix
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (round : Fin roundCount) (slot : Fin (quartileSourceRoundBudget totalBudget round))
    (prefixHistory : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (withinRound : Fin slot.val → Bool) :
    quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialPrefixExtension
        (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round slot)
        (Fin.append prefixHistory withinRound)) round.val =
      quartileSourceSequentialState roundCount totalBudget initial
        (quartileSourceSequentialCompletePrefixExtension prefixHistory) round.val := by
  apply quartileSourceSequentialState_eq_of_agree_before_roundPrefix
    roundCount totalBudget initial round
  intro prefixPosition
  have hboundary : quartileSourceSequentialRoundPrefixLength totalBudget round.val ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    apply Nat.le_trans (Nat.le_add_right _ _)
    exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  have hbefore : (Fin.castLE hboundary prefixPosition).val <
      (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round slot).val := by
    change prefixPosition.val <
      quartileSourceSequentialRoundPrefixLength totalBudget round.val + slot.val
    exact prefixPosition.isLt.trans_le (Nat.le_add_right _ _)
  unfold quartileSourceSequentialPrefixExtension
  rw [dif_pos hbefore]
  unfold quartileSourceSequentialCompletePrefixExtension
  rw [dif_pos (show (Fin.castLE hboundary prefixPosition).val <
      quartileSourceSequentialRoundPrefixLength totalBudget round.val by
        exact prefixPosition.isLt)]
  have hcast : (⟨(Fin.castLE hboundary prefixPosition).val, hbefore⟩ :
      Fin (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round slot).val) =
        Fin.castAdd slot.val prefixPosition := by
    apply Fin.ext
    rfl
  rw [hcast, Fin.append_left]
  apply congrArg prefixHistory
  apply Fin.ext
  rfl

/-- At a chronological QE position, reconstructing the active state from the
revealed reward prefix agrees with reconstructing it from the complete trace.
Only earlier source-round blocks are read, and their positions are strictly
before the current pull. -/
theorem quartileSourceSequentialState_prefixExtension_eq_completeTrace
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (position : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget))) :
    quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialPrefixExtension position (rewardPrefix rewards position))
      (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position).1.val =
      quartileSourceSequentialState roundCount totalBudget initial rewards
        (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position).1.val := by
  apply quartileSourceSequentialState_eq_of_agree_before roundCount totalBudget initial
  intro earlier hearlier
  have hposition :
      ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm earlier).val <
        position.val :=
    quartileSourceSequentialChronologicalSlotPosition_lt_of_round_lt position earlier hearlier
  unfold quartileSourceSequentialPrefixExtension
  rw [dif_pos hposition]
  unfold rewardPrefix
  congr 1

/-- The arm assigned to a slot after the active QE state is fixed.  Allocated
coordinates cycle through the active arm/sample enumeration; padding queries
a fixed active arm and is not read by the QE update. -/
noncomputable def quartileSourceSequentialSlotArm
    {Arm : Type*} [Fintype Arm]
    (totalBudget : ℕ) (round : ℕ)
    (slot : Fin (quartileSourceRoundBudget totalBudget round))
    (active : Finset Arm) (hactive : active.Nonempty) : Arm := by
  let sampleCount := quartilePerArmSampleCount
    (quartileSourceRoundBudget totalBudget) round active
  by_cases hallocated : slot.val < active.card * sampleCount
  · have hallocated' : slot.val < Fintype.card (QuartileBatchCoordinate active sampleCount) := by
      simpa [quartileBatchCoordinate_card] using hallocated
    exact ((quartileBatchCoordinateEquiv active sampleCount).symm
      ⟨slot.val, hallocated'⟩).1.val
  · exact Classical.choose hactive

/-- Both an allocated coordinate and a padding coordinate query an arm in the
current active QE state. -/
theorem quartileSourceSequentialSlotArm_mem
    {Arm : Type*} [Fintype Arm]
    (totalBudget : ℕ) (round : ℕ)
    (slot : Fin (quartileSourceRoundBudget totalBudget round))
    (active : Finset Arm) (hactive : active.Nonempty) :
    quartileSourceSequentialSlotArm totalBudget round slot active hactive ∈ active := by
  unfold quartileSourceSequentialSlotArm
  dsimp
  split
  · exact ((quartileBatchCoordinateEquiv _ _).symm _).1.property
  · exact Classical.choose_spec _

/-- Reindexing a source slot preserves its assigned arm when the incoming
active set is reconstructed from the same complete trace. -/
theorem quartileSourceSequentialSlotArm_eq_of_slot_eq
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (first second : quartileSourceSequentialSlot roundCount totalBudget) (hslot : first = second) :
    quartileSourceSequentialSlotArm totalBudget first.1.val first.2
      (quartileSourceSequentialState roundCount totalBudget initial rewards first.1.val)
      (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial rewards first.1.val) =
      quartileSourceSequentialSlotArm totalBudget second.1.val second.2
        (quartileSourceSequentialState roundCount totalBudget initial rewards second.1.val)
        (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial rewards second.1.val) := by
  subst first
  rfl

/-- Once a source slot is fixed, its assigned arm is unchanged under an
equality of the reconstructed active sets. -/
theorem quartileSourceSequentialSlotArm_eq_of_active_eq
    {Arm : Type*} [Fintype Arm]
    (totalBudget round : ℕ) (slot : Fin (quartileSourceRoundBudget totalBudget round))
    (first second : Finset Arm) (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hactive : first = second) :
    quartileSourceSequentialSlotArm totalBudget round slot first hfirst =
      quartileSourceSequentialSlotArm totalBudget round slot second hsecond := by
  subst second
  rfl

/-- One source QE round, reindexed as its allocated arm/sample prefix followed
by the exact number of inert padding pulls.  This carrier is equal in size to
the source round budget, but exposes the padding split required by the PMF
replay theorem. -/
noncomputable def quartileSourceRoundReindexedProcedure
    {Arm : Type*} [Fintype Arm]
    (totalBudget round : ℕ) (active : Finset Arm) (hactive : active.Nonempty) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)) +
        (quartileSourceRoundBudget totalBudget round -
          Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))) := by
  let sampleCount := quartilePerArmSampleCount
    (quartileSourceRoundBudget totalBudget) round active
  let coordinateCount := Fintype.card (QuartileBatchCoordinate active sampleCount)
  have hallocated : coordinateCount ≤ quartileSourceRoundBudget totalBudget round := by
    dsimp [coordinateCount]
    rw [quartileBatchCoordinate_card]
    exact quartilePerArmSampleCount_total_le
      (quartileSourceRoundBudget totalBudget) round active
  exact fixedBernoulliProcedure
    (fun position =>
      quartileSourceSequentialSlotArm totalBudget round
        (Fin.cast (Nat.add_sub_of_le hallocated) position) active hactive)
    (fun _ => Classical.choose hactive)

/-- The reindexed source round has exactly the padded QE schedule on every
relative position. -/
theorem quartileSourceRoundReindexedProcedure_pull_eq_padded
    {Arm : Type*} [Fintype Arm]
    (totalBudget round : ℕ) (active : Finset Arm) (hactive : active.Nonempty)
    (position : Fin (Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)) +
      (quartileSourceRoundBudget totalBudget round -
        Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))))
    (history : Fin position.val → Bool) :
    (quartileSourceRoundReindexedProcedure totalBudget round active hactive).pull position history =
      (quartilePaddedBernoulliBatchProcedure active hactive
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
        (quartileSourceRoundBudget totalBudget round -
          Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))).pull
        position history := by
  unfold quartileSourceRoundReindexedProcedure quartilePaddedBernoulliBatchProcedure
    fixedBernoulliProcedure
  dsimp
  unfold quartileSourceSequentialSlotArm quartilePaddedBatchSchedule
  dsimp
  by_cases hcoordinate : position.val < Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))
  · have hslot : (Fin.cast (Nat.add_sub_of_le (by
        rw [quartileBatchCoordinate_card]
        exact quartilePerArmSampleCount_total_le
          (quartileSourceRoundBudget totalBudget) round active)) position).val <
        active.card * quartilePerArmSampleCount
          (quartileSourceRoundBudget totalBudget) round active := by
      simpa [quartileBatchCoordinate_card] using hcoordinate
    have hslot' : position.val < active.card * quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active := by
      simpa using hslot
    simp [hslot']
  · have hslot : ¬ (Fin.cast (Nat.add_sub_of_le (by
        rw [quartileBatchCoordinate_card]
        exact quartilePerArmSampleCount_total_le
          (quartileSourceRoundBudget totalBudget) round active)) position).val <
        active.card * quartilePerArmSampleCount
          (quartileSourceRoundBudget totalBudget) round active := by
      simpa [quartileBatchCoordinate_card] using hcoordinate
    have hslot' : ¬ position.val < active.card * quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active := by
      simpa using hslot
    simp [hslot']

/-- The allocated coordinates of a source round have precisely the fresh QE
batch law after its reindexed padding is discarded. -/
theorem adaptiveQuartileSourceRoundReindexedProcedureRewardLaw_map_eq_flatBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (totalBudget round : ℕ) (active : Finset Arm) (hactive : active.Nonempty) :
    ((adaptiveBernoulliRewardLaw mean hmean
      (quartileSourceRoundReindexedProcedure totalBudget round active hactive)).map
        (rewardTracePrefix (Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))
          (quartileSourceRoundBudget totalBudget round -
            Fintype.card (QuartileBatchCoordinate active
              (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))))).map
      (quartileBatchTraceLabels active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)) =
      (quartileBernoulliBatchLaw mean hmean active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)).map
        quartileBatchUncurry := by
  unfold adaptiveBernoulliRewardLaw
  rw [adaptiveBernoulliRewardPrefixLaw_congr_pulls mean hmean
    (quartileSourceRoundReindexedProcedure totalBudget round active hactive)
    (quartilePaddedBernoulliBatchProcedure active hactive
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
      (quartileSourceRoundBudget totalBudget round -
        Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))))
    (by
      intro position history
      exact quartileSourceRoundReindexedProcedure_pull_eq_padded
        totalBudget round active hactive position history)
    _ (le_refl _)]
  exact adaptiveQuartilePaddedBernoulliBatchProcedureRewardLaw_map_eq_flatBatchLaw
    mean hmean active hactive
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
    (quartileSourceRoundBudget totalBudget round -
      Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))

/-- The literal fixed source schedule for one QE block, before discarding its
inert trailing positions. -/
noncomputable def quartileSourceRoundProcedure
    {Arm : Type*} [Fintype Arm]
    (totalBudget round : ℕ) (active : Finset Arm) (hactive : active.Nonempty) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm (quartileSourceRoundBudget totalBudget round) :=
  fixedBernoulliProcedure
    (fun slot => quartileSourceSequentialSlotArm totalBudget round slot active hactive)
    (fun _ => Classical.choose hactive)

/-- The allocated prefix of the literal source round has exactly the
heterogeneous fresh QE batch PMF. -/
theorem adaptiveQuartileSourceRoundProcedurePrefixLaw_map_eq_flatBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (totalBudget round : ℕ) (active : Finset Arm) (hactive : active.Nonempty) :
    (adaptiveBernoulliRewardPrefixLaw mean hmean
      (quartileSourceRoundProcedure totalBudget round active hactive)
      (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))) (by
        rw [quartileBatchCoordinate_card]
        exact quartilePerArmSampleCount_total_le
          (quartileSourceRoundBudget totalBudget) round active)).map
      (quartileBatchTraceLabels active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)) =
      (quartileBernoulliBatchLaw mean hmean active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)).map
        quartileBatchUncurry := by
  rw [quartileSourceRoundProcedure, adaptiveFixedBernoulliRewardPrefixLaw_eq_pmfPi]
  have hschedule :
      (fun coordinate : Fin (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))) =>
        bernoulliRewardLaw mean hmean
          (fixedSchedulePrefix
            (fun slot => quartileSourceSequentialSlotArm totalBudget round slot active hactive)
            (by
              rw [quartileBatchCoordinate_card]
              exact quartilePerArmSampleCount_total_le
                (quartileSourceRoundBudget totalBudget) round active) coordinate)) =
      (fun coordinate : Fin (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active))) =>
        bernoulliRewardLaw mean hmean
          ((quartileBatchCoordinateEquiv active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)).symm
              coordinate).1.val) := by
    funext coordinate
    unfold fixedSchedulePrefix quartileSourceSequentialSlotArm
    dsimp
    have hcoordinate : coordinate.val < active.card * quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active := by
      simpa [quartileBatchCoordinate_card] using coordinate.isLt
    simp [hcoordinate]
  rw [hschedule, quartileBatchTraceProductLaw_map_eq_pmfPi]
  exact (quartileBernoulliBatchLaw_map_uncurry_eq_pmfPi mean hmean active
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)).symm

/-- The arm selected at one chronological source-QE slot. -/
noncomputable def quartileSourceSequentialQEPull
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (position : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)))
    (history : Fin position.val → Bool) : Arm := by
  let rewards := quartileSourceSequentialPrefixExtension position history
  let sourceSlot := quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position
  let active := quartileSourceSequentialState roundCount totalBudget initial rewards sourceSlot.1.val
  let hactive : active.Nonempty :=
    quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial rewards sourceSlot.1.val
  exact quartileSourceSequentialSlotArm totalBudget sourceSlot.1.val sourceSlot.2 active hactive

/-- The source-QE pull read from a complete trace.  It is a deterministic
description of the current round's schedule once the preceding round blocks
are fixed; the next theorem proves that the adaptive policy evaluates to this
same arm on its realized history. -/
noncomputable def quartileSourceSequentialQEPullFromCompleteTrace
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (position : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget))) : Arm := by
  let slot := quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position
  let active := quartileSourceSequentialState roundCount totalBudget initial rewards slot.1.val
  let hactive : active.Nonempty :=
    quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial rewards slot.1.val
  exact quartileSourceSequentialSlotArm totalBudget slot.1.val slot.2 active hactive

/-- At every realized trace, the adaptive QE pull is the deterministic
current-round schedule selected by the completed earlier round blocks. -/
theorem quartileSourceSequentialQEPull_eq_pullFromCompleteTrace
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (position : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget))) :
    quartileSourceSequentialQEPull roundCount totalBudget initial hinitial position
      (rewardPrefix rewards position) =
      quartileSourceSequentialQEPullFromCompleteTrace roundCount totalBudget initial hinitial
        rewards position := by
  unfold quartileSourceSequentialQEPull quartileSourceSequentialQEPullFromCompleteTrace
  dsimp
  simp only [quartileSourceSequentialState_prefixExtension_eq_completeTrace]

/-- At every slot of a specified source round, the realized adaptive pull is
the arm assigned by that round's fixed schedule once its incoming active set
has been reconstructed from the earlier blocks. -/
theorem quartileSourceSequentialQEPull_at_roundPosition_eq_slotArm
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (round : Fin roundCount) (slot : Fin (quartileSourceRoundBudget totalBudget round)) :
    quartileSourceSequentialQEPull roundCount totalBudget initial hinitial
      (quartileSourceSequentialRoundPosition roundCount totalBudget round slot)
      (rewardPrefix rewards
        (quartileSourceSequentialRoundPosition roundCount totalBudget round slot)) =
      quartileSourceSequentialSlotArm totalBudget round.val slot
        (quartileSourceSequentialState roundCount totalBudget initial rewards round.val)
        (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial rewards round.val) := by
  rw [quartileSourceSequentialQEPull_eq_pullFromCompleteTrace]
  unfold quartileSourceSequentialQEPullFromCompleteTrace
  dsimp
  unfold quartileSourceSequentialRoundPosition
  exact quartileSourceSequentialSlotArm_eq_of_slot_eq
    roundCount totalBudget initial hinitial rewards
    (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
      ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm ⟨round, slot⟩))
    ⟨round, slot⟩
    ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).apply_symm_apply _)

/-- The source QE prefix as a literal finite adaptive Bernoulli procedure.
Its output is a surviving arm; the supplement's uniform final stage is
attached separately, after the replay-law bridge identifies this survivor
state with the source QE state law. -/
noncomputable def quartileSourceSequentialQEProcedure
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) where
  pull := quartileSourceSequentialQEPull roundCount totalBudget initial hinitial
  output := fun rewards => Classical.choose
    (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial rewards roundCount)

/-- Regard one allocated QE coordinate as a slot in its source round's full
budget block. -/
noncomputable def quartileSourceSequentialAllocatedRoundSlot
    {Arm : Type*} [Fintype Arm]
    (totalBudget : ℕ) (round : ℕ) (active : Finset Arm)
    (localSlot : Fin (Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))) :
    Fin (quartileSourceRoundBudget totalBudget round) :=
  ⟨localSlot.val, by
    have hlocal : localSlot.val < active.card *
        quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active := by
      simpa only [quartileBatchCoordinate_card] using localSlot.isLt
    exact hlocal.trans_le (quartilePerArmSampleCount_total_le
      (quartileSourceRoundBudget totalBudget) round active)⟩

/-- The same allocated coordinate is a valid relative position in the global
continuation after the preceding source rounds. -/
noncomputable def quartileSourceSequentialAllocatedContinuationSlot
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (round : Fin roundCount) (active : Finset Arm)
    (localSlot : Fin (Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)))) :
    Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) -
      quartileSourceSequentialRoundPrefixLength totalBudget round.val) :=
  ⟨localSlot.val, by
    have hlocal : localSlot.val < active.card *
        quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active := by
      simpa only [quartileBatchCoordinate_card] using localSlot.isLt
    have hround : localSlot.val < quartileSourceRoundBudget totalBudget round.val :=
      hlocal.trans_le (quartilePerArmSampleCount_total_le
        (quartileSourceRoundBudget totalBudget) round.val active)
    have hbudget : quartileSourceSequentialRoundPrefixLength totalBudget round.val +
        quartileSourceRoundBudget totalBudget round.val ≤
        Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) :=
      quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
        roundCount totalBudget round
    omega⟩

/-- After a source-round boundary is fixed, every allocated pull of the
global sequential continuation is the corresponding pull of that round's
literal fixed source schedule.  The result is pointwise in the within-round
history, so it can be lifted to an exact conditional PMF equality. -/
theorem quartileSourceSequentialQEContinuation_pull_eq_roundProcedure
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hstate : quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension history) round.val = active)
    (localSlot : Fin (Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active))))
    (suffix : Fin localSlot.val → Bool) :
    (adaptiveBernoulliContinuationProcedure
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val)
      (by
        apply Nat.le_trans (Nat.le_add_right _ _)
        exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
          roundCount totalBudget round)
      history).pull
        (quartileSourceSequentialAllocatedContinuationSlot
          roundCount totalBudget round active localSlot) suffix =
      (quartileSourceRoundProcedure totalBudget round.val active hactive).pull
        (quartileSourceSequentialAllocatedRoundSlot totalBudget round.val active localSlot) suffix := by
  let sourceSlot : Fin (quartileSourceRoundBudget totalBudget round) :=
    quartileSourceSequentialAllocatedRoundSlot totalBudget round.val active localSlot
  have hstateAtPosition :
      quartileSourceSequentialState roundCount totalBudget initial
        (quartileSourceSequentialPrefixExtension
          (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
          (Fin.append history suffix)) round.val = active := by
    rw [quartileSourceSequentialState_prefixExtension_append_eq_completePrefix]
    exact hstate
  have hsourceSlot : quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
      (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot) =
      ⟨round, sourceSlot⟩ := by
    rw [quartileSourceSequentialRoundPrefixPosition_eq_roundPosition]
    exact quartileSourceSequentialChronologicalSlotEquiv_roundPosition
      roundCount totalBudget round sourceSlot
  unfold adaptiveBernoulliContinuationProcedure quartileSourceSequentialQEProcedure
  dsimp
  change quartileSourceSequentialQEPull roundCount totalBudget initial hinitial
      (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
      (Fin.append history suffix) = _
  unfold quartileSourceSequentialQEPull
  dsimp
  unfold quartileSourceRoundProcedure fixedBernoulliProcedure
  dsimp
  calc
    quartileSourceSequentialSlotArm totalBudget
        (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
          (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)).1.val
        (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
          (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)).2
        (quartileSourceSequentialState roundCount totalBudget initial
          (quartileSourceSequentialPrefixExtension
            (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
            (Fin.append history suffix))
          (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
            (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)).1.val)
        (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
          (quartileSourceSequentialPrefixExtension
            (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
            (Fin.append history suffix))
          (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
            (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)).1.val) =
      quartileSourceSequentialSlotArm totalBudget round.val sourceSlot
        (quartileSourceSequentialState roundCount totalBudget initial
          (quartileSourceSequentialPrefixExtension
            (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
            (Fin.append history suffix)) round.val)
        (quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
          (quartileSourceSequentialPrefixExtension
            (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
            (Fin.append history suffix)) round.val) :=
      quartileSourceSequentialSlotArm_eq_of_slot_eq roundCount totalBudget initial hinitial
        (quartileSourceSequentialPrefixExtension
          (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot)
          (Fin.append history suffix))
        (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
          (quartileSourceSequentialRoundPrefixPosition roundCount totalBudget round sourceSlot))
        ⟨round, sourceSlot⟩ hsourceSlot
    _ = quartileSourceSequentialSlotArm totalBudget round.val sourceSlot active hactive := by
      exact quartileSourceSequentialSlotArm_eq_of_active_eq totalBudget round.val sourceSlot
        _ _ _ _ hstateAtPosition
    _ = quartileSourceSequentialSlotArm totalBudget round.val
        (quartileSourceSequentialAllocatedRoundSlot totalBudget round.val active localSlot)
        active hactive := by
      dsimp [sourceSlot]

/-- Conditional on the rewards through a source-round boundary, the allocated
part of the global sequential QE continuation has exactly the fresh,
heterogeneous batch PMF used by that source round.  This is the local replay
kernel needed to compose the rounds without treating adaptive blocks as
unconditionally independent. -/
theorem adaptiveQuartileSourceSequentialQERoundSuffixLaw_map_eq_flatBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hstate : quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension history) round.val = active) :
    (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)))
      (by
        have hallocated : Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) ≤
            quartileSourceRoundBudget totalBudget round.val := by
          simpa only [quartileBatchCoordinate_card] using
            (quartilePerArmSampleCount_total_le
              (quartileSourceRoundBudget totalBudget) round.val active)
        exact Nat.le_trans (Nat.add_le_add_left hallocated _)
          (quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
            roundCount totalBudget round))).map
      (quartileBatchTraceLabels active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) =
      (quartileBernoulliBatchLaw mean hmean active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)).map
        quartileBatchUncurry := by
  let allocatedCount := Fintype.card (QuartileBatchCoordinate active
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active))
  have hallocated : allocatedCount ≤ quartileSourceRoundBudget totalBudget round.val := by
    dsimp [allocatedCount]
    rw [quartileBatchCoordinate_card]
    exact quartilePerArmSampleCount_total_le
      (quartileSourceRoundBudget totalBudget) round.val active
  have hroundBudget : quartileSourceSequentialRoundPrefixLength totalBudget round.val +
      quartileSourceRoundBudget totalBudget round.val ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) :=
    quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  have hcontinuationLaw :
      adaptiveBernoulliRewardPrefixLaw mean hmean
        (adaptiveBernoulliContinuationProcedure
          (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
          (quartileSourceSequentialRoundPrefixLength totalBudget round.val)
          (by omega) history)
        allocatedCount (by omega) =
      adaptiveBernoulliRewardPrefixLaw mean hmean
        (quartileSourceRoundProcedure totalBudget round.val active hactive)
        allocatedCount (by omega) := by
    apply adaptiveBernoulliRewardPrefixLaw_congr_pulls_prefix mean hmean
    intro localSlot suffix
    change (adaptiveBernoulliContinuationProcedure
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) (by omega) history).pull
        (quartileSourceSequentialAllocatedContinuationSlot
          roundCount totalBudget round active localSlot) suffix =
      (quartileSourceRoundProcedure totalBudget round.val active hactive).pull
        (quartileSourceSequentialAllocatedRoundSlot totalBudget round.val active localSlot) suffix
    exact quartileSourceSequentialQEContinuation_pull_eq_roundProcedure
      roundCount totalBudget initial hinitial round history active hactive hstate localSlot suffix
  rw [adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix]
  dsimp [allocatedCount] at hcontinuationLaw
  rw [hcontinuationLaw]
  exact adaptiveQuartileSourceRoundProcedurePrefixLaw_map_eq_flatBatchLaw
    mean hmean totalBudget round.val active hactive

/-- The same source-round kernel remains exact when the residual source block
padding is retained and then marginalized.  This is the block-boundary form
needed for a multi-round replay induction: the next block begins only after
all `Q_r` positions, while the QE update reads just the allocated prefix. -/
theorem adaptiveQuartileSourceSequentialQERoundPaddedSuffixLaw_map_eq_flatBatchLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hstate : quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension history) round.val = active) :
    (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) +
        (quartileSourceRoundBudget totalBudget round.val -
          Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active))))
      (by
        have hallocated : Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) ≤
            quartileSourceRoundBudget totalBudget round.val := by
          simpa only [quartileBatchCoordinate_card] using
            (quartilePerArmSampleCount_total_le
              (quartileSourceRoundBudget totalBudget) round.val active)
        have hroundBudget := quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
          roundCount totalBudget round
        omega)).map
      (quartileBatchTraceLabels active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active) ∘
        rewardTracePrefix
          (Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)))
          (quartileSourceRoundBudget totalBudget round.val -
            Fintype.card (QuartileBatchCoordinate active
              (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)))) =
      (quartileBernoulliBatchLaw mean hmean active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)).map
        quartileBatchUncurry := by
  let allocatedCount := Fintype.card (QuartileBatchCoordinate active
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active))
  let paddingCount := quartileSourceRoundBudget totalBudget round.val - allocatedCount
  have hallocated : allocatedCount ≤ quartileSourceRoundBudget totalBudget round.val := by
    dsimp [allocatedCount]
    rw [quartileBatchCoordinate_card]
    exact quartilePerArmSampleCount_total_le
      (quartileSourceRoundBudget totalBudget) round.val active
  have hroundBudget : quartileSourceSequentialRoundPrefixLength totalBudget round.val +
      quartileSourceRoundBudget totalBudget round.val ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) :=
    quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  have hprefixMarginal :
      (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (allocatedCount + paddingCount) (by omega)).map
        (rewardTracePrefix allocatedCount paddingCount) =
      adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        allocatedCount (by omega) := by
    rw [adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix,
      adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix]
    exact adaptiveBernoulliRewardPrefixLaw_map_rewardTracePrefix mean hmean
      (adaptiveBernoulliContinuationProcedure
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) (by omega) history)
      allocatedCount paddingCount (by omega)
  have hallocatedLaw := adaptiveQuartileSourceSequentialQERoundSuffixLaw_map_eq_flatBatchLaw
    mean hmean roundCount totalBudget initial hinitial round history active hactive hstate
  change (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (allocatedCount + paddingCount) _).map
      (quartileBatchTraceLabels active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active) ∘
        rewardTracePrefix allocatedCount paddingCount) = _
  calc
    (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (allocatedCount + paddingCount) _).map
        (quartileBatchTraceLabels active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active) ∘
          rewardTracePrefix allocatedCount paddingCount) =
      ((adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (allocatedCount + paddingCount) _).map
        (rewardTracePrefix allocatedCount paddingCount)).map
        (quartileBatchTraceLabels active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) := by
            rw [PMF.map_comp]
    _ = (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        allocatedCount _).map
        (quartileBatchTraceLabels active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) := by
            rw [hprefixMarginal]
    _ = (quartileBernoulliBatchLaw mean hmean active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)).map
        quartileBatchUncurry := by
          simpa only [allocatedCount] using hallocatedLaw

/-- Decode the allocated prefix of a complete source-round block into the
tagged outcome used by the fresh QE state process. -/
noncomputable def quartileSourceSequentialPaddedRoundOutcome
    {Arm : Type*} [Fintype Arm]
    (totalBudget round : ℕ) (active : Finset Arm)
    (rewards : Fin (Fintype.card (QuartileBatchCoordinate active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)) +
      (quartileSourceRoundBudget totalBudget round -
        Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))) → Bool) :
    canonicalFreshQuartileOutcome Arm totalBudget :=
  canonicalFreshQuartileEmbed totalBudget
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
    (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
      totalBudget round active
      (quartileSourceRoundBudget_le_totalBudget totalBudget round)) active
    (quartileBatchCurry (quartileBatchTraceLabels active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
      (rewardTracePrefix
        (Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))
        (quartileSourceRoundBudget totalBudget round -
          Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))
        rewards)))

/-- At the literal end of a source block, decoding its allocated prefix has
exactly the tagged source outcome kernel.  The full block still includes the
source's inert padding, which is deliberately summed out rather than treated
as an extra QE sample. -/
theorem adaptiveQuartileSourceSequentialQERoundPaddedSuffixLaw_map_eq_sourceOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hstate : quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension history) round.val = active) :
    (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) +
        (quartileSourceRoundBudget totalBudget round.val -
          Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active))))
      (by
        have hallocated : Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) ≤
            quartileSourceRoundBudget totalBudget round.val := by
          simpa only [quartileBatchCoordinate_card] using
            (quartilePerArmSampleCount_total_le
              (quartileSourceRoundBudget totalBudget) round.val active)
        have hroundBudget := quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
          roundCount totalBudget round
        omega)).map
      (quartileSourceSequentialPaddedRoundOutcome totalBudget round.val active) =
      quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round.val active := by
  let sampleCount := quartilePerArmSampleCount
    (quartileSourceRoundBudget totalBudget) round.val active
  let allocatedCount := Fintype.card (QuartileBatchCoordinate active sampleCount)
  let paddingCount := quartileSourceRoundBudget totalBudget round.val - allocatedCount
  let embed : (QuartileBatchCoordinate active sampleCount → Bool) →
      canonicalFreshQuartileOutcome Arm totalBudget := fun labels =>
    canonicalFreshQuartileEmbed totalBudget sampleCount
      (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
        totalBudget round.val active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active
      (quartileBatchCurry labels)
  have hflat := adaptiveQuartileSourceSequentialQERoundPaddedSuffixLaw_map_eq_flatBatchLaw
    mean hmean roundCount totalBudget initial hinitial round history active hactive hstate
  change (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (allocatedCount + paddingCount) _).map
      (embed ∘ quartileBatchTraceLabels active sampleCount ∘
        rewardTracePrefix allocatedCount paddingCount) = _
  calc
    (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (allocatedCount + paddingCount) _).map
        (embed ∘ quartileBatchTraceLabels active sampleCount ∘
          rewardTracePrefix allocatedCount paddingCount) =
      ((adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (allocatedCount + paddingCount) _).map
        (quartileBatchTraceLabels active sampleCount ∘
          rewardTracePrefix allocatedCount paddingCount)).map embed := by
            rw [PMF.map_comp]
    _ = ((quartileBernoulliBatchLaw mean hmean active sampleCount).map
        quartileBatchUncurry).map embed := by
          simpa only [sampleCount, allocatedCount, paddingCount] using
            congrArg (PMF.map embed) hflat
    _ = (quartileBernoulliBatchLaw mean hmean active sampleCount).map
        (fun batchTable => canonicalFreshQuartileEmbed totalBudget sampleCount
          (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
            totalBudget round.val active
            (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active batchTable) := by
          rw [PMF.map_comp]
          congr 1
    _ = quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round.val active := by
          simp [quartileSourceBudgetOutcomeLaw, quartileBudgetOutcomeLaw,
            adaptiveBatchQuartileOutcomeLaw, sampleCount, round.isLt]

/-- Decode the allocated prefix of a source block in its literal `Q_r`-slot
carrier.  The inequality-indexed prefix restriction is what makes this
definition compatible with arbitrary floor-allocation remainders. -/
noncomputable def quartileSourceSequentialRoundOutcome
    {Arm : Type*} [Fintype Arm]
    (totalBudget round : ℕ) (active : Finset Arm)
    (rewards : Fin (quartileSourceRoundBudget totalBudget round) → Bool) :
    canonicalFreshQuartileOutcome Arm totalBudget :=
  canonicalFreshQuartileEmbed totalBudget
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
    (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
      totalBudget round active
      (quartileSourceRoundBudget_le_totalBudget totalBudget round)) active
    (quartileBatchCurry (quartileBatchTraceLabels active
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)
      (rewardTracePrefixLE
        (Fintype.card (QuartileBatchCoordinate active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active)))
        (quartileSourceRoundBudget totalBudget round)
        (by
          rw [quartileBatchCoordinate_card]
          exact quartilePerArmSampleCount_total_le
            (quartileSourceRoundBudget totalBudget) round active)
        rewards)))

/-- The reconstructed state advances exactly by the same deterministic tagged
outcome update used in the source fresh-round process. -/
theorem quartileSourceSequentialState_succ_eq_roundOutcomeAdvance
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (round : Fin roundCount) :
    quartileSourceSequentialState roundCount totalBudget initial rewards (round.val + 1) =
      quartileRoundAdvance
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun earlier _hEarlier active => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget earlier active
            (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
        round.val
        (quartileSourceSequentialState roundCount totalBudget initial rewards round.val)
        (quartileSourceSequentialRoundOutcome totalBudget round.val
          (quartileSourceSequentialState roundCount totalBudget initial rewards round.val)
          (quartileSourceSequentialRoundTrace roundCount totalBudget round rewards)) := by
  let active := quartileSourceSequentialState roundCount totalBudget initial rewards round.val
  let sampleCount := quartilePerArmSampleCount
    (quartileSourceRoundBudget totalBudget) round.val active
  let batchTable := quartileSourceSequentialBatchTable roundCount totalBudget round.val round.isLt
    active rewards
  let score : ℕ → Finset Arm → canonicalFreshQuartileOutcome Arm totalBudget → Arm → ℝ :=
    adaptiveBatchQuartileScore roundCount
    (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
    (fun earlier hEarlier current => quartilePerArmSampleCount_le_roundCap
      (quartileSourceRoundBudget totalBudget) totalBudget earlier current
      (quartileSourceRoundBudget_le_totalBudget totalBudget earlier))
  have htable : batchTable = quartileBatchCurry
      (quartileBatchTraceLabels active sampleCount
        (rewardTracePrefixLE
          (Fintype.card (QuartileBatchCoordinate active sampleCount))
          (quartileSourceRoundBudget totalBudget round.val)
          (by
            dsimp [sampleCount]
            rw [quartileBatchCoordinate_card]
            exact quartilePerArmSampleCount_total_le
              (quartileSourceRoundBudget totalBudget) round.val active)
          (quartileSourceSequentialRoundTrace roundCount totalBudget round rewards))) := by
    dsimp [batchTable]
    rw [quartileSourceSequentialBatchTable_eq_curry_allocatedRoundTrace,
      quartileSourceSequentialAllocatedRoundTrace_eq_prefixLE_roundTrace]
  have houtcome : quartileSourceSequentialRoundOutcome totalBudget round.val active
      (quartileSourceSequentialRoundTrace roundCount totalBudget round rewards) =
      canonicalFreshQuartileEmbed totalBudget sampleCount
        (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
          totalBudget round.val active
          (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active batchTable := by
    unfold quartileSourceSequentialRoundOutcome
    rw [htable]
  have hscore : score round.val active
      (quartileSourceSequentialRoundOutcome totalBudget round.val active
        (quartileSourceSequentialRoundTrace roundCount totalBudget round rewards)) =
      quartileBernoulliBatchScore active sampleCount batchTable := by
    rw [houtcome]
    funext arm
    exact adaptiveBatchQuartileScore_embed roundCount
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
      (fun earlier hEarlier current => quartilePerArmSampleCount_le_roundCap
        (quartileSourceRoundBudget totalBudget) totalBudget earlier current
        (quartileSourceRoundBudget_le_totalBudget totalBudget earlier))
      round.val round.isLt active batchTable arm
  simp only [quartileSourceSequentialState]
  rw [dif_pos round.isLt]
  change quartileEliminationFromBatch active sampleCount batchTable =
    quartileRoundAdvance score round.val active
      (quartileSourceSequentialRoundOutcome totalBudget round.val active
        (quartileSourceSequentialRoundTrace roundCount totalBudget round rewards))
  unfold quartileEliminationFromBatch quartileRoundAdvance
  rw [hscore]

/-- The finite state and accumulated bad-round flag decoded from a complete
sequential QE trace.  At every completed round its active component is read
from the source replay state; the Boolean is updated by the identical tagged
round event used in `freshQuartileRoundsStateLaw`. -/
noncomputable def quartileSourceSequentialStateFailure
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (completed : ℕ) : Finset Arm × Bool := by
  classical
  let score : ℕ → Finset Arm → canonicalFreshQuartileOutcome Arm totalBudget → Arm → ℝ :=
    adaptiveBatchQuartileScore roundCount
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
      (fun round _ active => quartilePerArmSampleCount_le_roundCap
        (quartileSourceRoundBudget totalBudget) totalBudget round active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round))
  letI : ∀ round active outcome,
      Decidable (quartileRoundBad mean error score round active outcome) :=
    fun _ _ _ => Classical.propDecidable _
  exact Nat.rec (initial, false) (fun round previous =>
    if hround : round < roundCount then
      let active := previous.1
      let outcome := quartileSourceSequentialRoundOutcome totalBudget round active
        (quartileSourceSequentialRoundTrace roundCount totalBudget ⟨round, hround⟩ rewards)
      (quartileRoundAdvance score round active outcome,
        previous.2 || decide (quartileRoundBad mean error score round active outcome))
    else previous) completed

/-- The decoded active component is precisely the deterministic sequential
replay state through every scheduled source round. -/
theorem quartileSourceSequentialStateFailure_fst_eq_state
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) :
    ∀ completed, completed ≤ roundCount →
      (quartileSourceSequentialStateFailure mean error roundCount totalBudget initial rewards completed).1 =
        quartileSourceSequentialState roundCount totalBudget initial rewards completed := by
  intro completed
  induction completed with
  | zero =>
      intro _
      rfl
  | succ completed ih =>
      intro hcompleted
      have hround : completed < roundCount := by omega
      have hstepFst :
          (quartileSourceSequentialStateFailure mean error roundCount totalBudget initial rewards
              (completed + 1)).1 =
            quartileRoundAdvance
              (adaptiveBatchQuartileScore roundCount
                (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
                (fun round _ active => quartilePerArmSampleCount_le_roundCap
                  (quartileSourceRoundBudget totalBudget) totalBudget round active
                  (quartileSourceRoundBudget_le_totalBudget totalBudget round)))
              completed
              (quartileSourceSequentialStateFailure mean error roundCount totalBudget initial rewards
                completed).1
              (quartileSourceSequentialRoundOutcome totalBudget completed
                (quartileSourceSequentialStateFailure mean error roundCount totalBudget initial rewards
                  completed).1
                (quartileSourceSequentialRoundTrace roundCount totalBudget ⟨completed, hround⟩ rewards)) := by
              simp [quartileSourceSequentialStateFailure, hround]
      rw [hstepFst]
      rw [ih (Nat.le_of_succ_le hcompleted)]
      exact (quartileSourceSequentialState_succ_eq_roundOutcomeAdvance
        roundCount totalBudget initial rewards ⟨completed, hround⟩).symm

/-- One scheduled source block updates the decoded state/flag pair by the
same tagged outcome transition used in the fresh adaptive process. -/
theorem quartileSourceSequentialStateFailure_succ_eq_update
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (rewards : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (round : Fin roundCount) :
    quartileSourceSequentialStateFailure mean error roundCount totalBudget initial rewards
        (round.val + 1) =
      let previous := quartileSourceSequentialStateFailure mean error roundCount totalBudget
        initial rewards round.val
      let active := previous.1
      let outcome := quartileSourceSequentialRoundOutcome totalBudget round.val active
        (quartileSourceSequentialRoundTrace roundCount totalBudget round rewards)
      (quartileRoundAdvance
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget earlier active
            (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
        round.val active outcome,
        previous.2 || @decide (quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget earlier active
              (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
          round.val active outcome) (Classical.propDecidable _)) := by
  classical
  simp [quartileSourceSequentialStateFailure, round.isLt]

/-- Restrict a boundary history through round `r + 1` to the preceding source
round boundary. -/
noncomputable def quartileSourceSequentialBoundaryPrefix
    (totalBudget round : ℕ)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget (round + 1)) → Bool) :
    Fin (quartileSourceSequentialRoundPrefixLength totalBudget round) → Bool := fun position =>
  history ⟨position.val, by
    rw [quartileSourceSequentialRoundPrefixLength_succ]
    exact position.isLt.trans_le (Nat.le_add_right _ _)⟩

/-- Read the literal fixed `Q_r` block from a boundary history through that
round. -/
noncomputable def quartileSourceSequentialBoundaryRoundBlock
    (totalBudget round : ℕ)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget (round + 1)) → Bool) :
    Fin (quartileSourceRoundBudget totalBudget round) → Bool := fun slot =>
  history ⟨quartileSourceSequentialRoundPrefixLength totalBudget round + slot.val, by
    rw [quartileSourceSequentialRoundPrefixLength_succ]
    exact Nat.add_lt_add_left slot.isLt _⟩

/-- Concatenate an earlier boundary history and the literal next source block,
transporting the result to the definitional boundary-indexed carrier. -/
noncomputable def quartileSourceSequentialBoundaryAppend
    (totalBudget round : ℕ)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round) → Bool)
    (block : Fin (quartileSourceRoundBudget totalBudget round) → Bool) :
    Fin (quartileSourceSequentialRoundPrefixLength totalBudget (round + 1)) → Bool := fun position =>
  Fin.append history block
    (Fin.cast (quartileSourceSequentialRoundPrefixLength_succ totalBudget round) position)

/-- Recovering the preceding boundary after `BoundaryAppend` returns its
original history. -/
theorem quartileSourceSequentialBoundaryPrefix_append
    (totalBudget round : ℕ)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round) → Bool)
    (block : Fin (quartileSourceRoundBudget totalBudget round) → Bool) :
    quartileSourceSequentialBoundaryPrefix totalBudget round
      (quartileSourceSequentialBoundaryAppend totalBudget round history block) = history := by
  funext position
  unfold quartileSourceSequentialBoundaryPrefix quartileSourceSequentialBoundaryAppend
  have hposition : position.val <
      quartileSourceSequentialRoundPrefixLength totalBudget (round + 1) := by
    rw [quartileSourceSequentialRoundPrefixLength_succ]
    exact position.isLt.trans_le (Nat.le_add_right _ _)
  have hcast : Fin.cast (quartileSourceSequentialRoundPrefixLength_succ totalBudget round)
      ⟨position.val, hposition⟩ = Fin.castAdd (quartileSourceRoundBudget totalBudget round) position := by
    apply Fin.ext
    rfl
  rw [hcast, Fin.append_left]

/-- Recovering the current source block after `BoundaryAppend` returns that
literal block. -/
theorem quartileSourceSequentialBoundaryRoundBlock_append
    (totalBudget round : ℕ)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round) → Bool)
    (block : Fin (quartileSourceRoundBudget totalBudget round) → Bool) :
    quartileSourceSequentialBoundaryRoundBlock totalBudget round
      (quartileSourceSequentialBoundaryAppend totalBudget round history block) = block := by
  funext slot
  unfold quartileSourceSequentialBoundaryRoundBlock quartileSourceSequentialBoundaryAppend
  have hposition : quartileSourceSequentialRoundPrefixLength totalBudget round + slot.val <
      quartileSourceSequentialRoundPrefixLength totalBudget (round + 1) := by
    rw [quartileSourceSequentialRoundPrefixLength_succ]
    exact Nat.add_lt_add_left slot.isLt _
  have hcast : Fin.cast (quartileSourceSequentialRoundPrefixLength_succ totalBudget round)
      ⟨quartileSourceSequentialRoundPrefixLength totalBudget round + slot.val, hposition⟩ =
        Fin.natAdd (quartileSourceSequentialRoundPrefixLength totalBudget round) slot := by
    apply Fin.ext
    rfl
  rw [hcast, Fin.append_right]

/-- Splitting a boundary history into its earlier boundary and literal current
block, then appending them again, is lossless. -/
theorem quartileSourceSequentialBoundaryAppend_prefix_roundBlock
    (totalBudget round : ℕ)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget (round + 1)) → Bool) :
    quartileSourceSequentialBoundaryAppend totalBudget round
      (quartileSourceSequentialBoundaryPrefix totalBudget round history)
      (quartileSourceSequentialBoundaryRoundBlock totalBudget round history) = history := by
  let trace : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round +
      quartileSourceRoundBudget totalBudget round) → Bool := fun position =>
    history (Fin.cast (quartileSourceSequentialRoundPrefixLength_succ totalBudget round).symm
      position)
  have hprefix : quartileSourceSequentialBoundaryPrefix totalBudget round history =
      fun position => trace (Fin.castAdd (quartileSourceRoundBudget totalBudget round) position) := by
    funext position
    unfold quartileSourceSequentialBoundaryPrefix trace
    apply congrArg history
    apply Fin.ext
    rfl
  have hblock : quartileSourceSequentialBoundaryRoundBlock totalBudget round history =
      fun slot => trace (Fin.natAdd (quartileSourceSequentialRoundPrefixLength totalBudget round)
        slot) := by
    funext slot
    unfold quartileSourceSequentialBoundaryRoundBlock trace
    apply congrArg history
    apply Fin.ext
    rfl
  rw [hprefix, hblock]
  funext position
  unfold quartileSourceSequentialBoundaryAppend
  rw [Fin.append_castAdd_natAdd]
  apply congrArg history
  apply Fin.ext
  rfl

/-- Completing an appended boundary history leaves the incoming replay state
unchanged: that state reads only source blocks strictly before the new one. -/
theorem quartileSourceSequentialState_completePrefix_boundaryAppend_eq
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (block : Fin (quartileSourceRoundBudget totalBudget round.val) → Bool) :
    quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension
        (quartileSourceSequentialBoundaryAppend totalBudget round.val history block)) round.val =
      quartileSourceSequentialState roundCount totalBudget initial
        (quartileSourceSequentialCompletePrefixExtension history) round.val := by
  apply quartileSourceSequentialState_eq_of_agree_before_roundPrefix
    roundCount totalBudget initial round
  intro position
  have hboundary : quartileSourceSequentialRoundPrefixLength totalBudget round.val ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    apply Nat.le_trans (Nat.le_add_right _ _)
    exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  have hnextBoundary : quartileSourceSequentialRoundPrefixLength totalBudget (round.val + 1) ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    rw [quartileSourceSequentialRoundPrefixLength_succ]
    exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  let nextPosition : Fin (quartileSourceSequentialRoundPrefixLength totalBudget (round.val + 1)) :=
    ⟨position.val, by
      rw [quartileSourceSequentialRoundPrefixLength_succ]
      exact position.isLt.trans_le (Nat.le_add_right _ _)⟩
  have hcast : Fin.castLE hnextBoundary nextPosition = Fin.castLE hboundary position := by
    apply Fin.ext
    rfl
  rw [← hcast]
  rw [quartileSourceSequentialCompletePrefixExtension_apply_castLE
    (quartileSourceSequentialBoundaryAppend totalBudget round.val history block) hnextBoundary]
  rw [hcast]
  rw [quartileSourceSequentialCompletePrefixExtension_apply_castLE history hboundary]
  change quartileSourceSequentialBoundaryPrefix totalBudget round.val
      (quartileSourceSequentialBoundaryAppend totalBudget round.val history block) position =
        history position
  exact congrFun (quartileSourceSequentialBoundaryPrefix_append totalBudget round.val history block)
    position

/-- The literal source trace of the newly completed block is exactly the
block supplied to `BoundaryAppend`. -/
theorem quartileSourceSequentialRoundTrace_completePrefix_boundaryAppend_eq
    (roundCount totalBudget : ℕ) (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (block : Fin (quartileSourceRoundBudget totalBudget round.val) → Bool) :
    quartileSourceSequentialRoundTrace roundCount totalBudget round
      (quartileSourceSequentialCompletePrefixExtension
        (quartileSourceSequentialBoundaryAppend totalBudget round.val history block)) = block := by
  funext slot
  have hboundary : quartileSourceSequentialRoundPrefixLength totalBudget (round.val + 1) ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    rw [quartileSourceSequentialRoundPrefixLength_succ]
    exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  let position : Fin (quartileSourceSequentialRoundPrefixLength totalBudget (round.val + 1)) :=
    ⟨quartileSourceSequentialRoundPrefixLength totalBudget round.val + slot.val, by
      rw [quartileSourceSequentialRoundPrefixLength_succ]
      exact Nat.add_lt_add_left slot.isLt _⟩
  have hcast : quartileSourceSequentialRoundPosition roundCount totalBudget round slot =
      Fin.castLE hboundary position := by
    apply Fin.ext
    rw [quartileSourceSequentialRoundPosition_val]
    rfl
  change quartileSourceSequentialCompletePrefixExtension
      (quartileSourceSequentialBoundaryAppend totalBudget round.val history block)
      (quartileSourceSequentialRoundPosition roundCount totalBudget round slot) = block slot
  rw [hcast, quartileSourceSequentialCompletePrefixExtension_apply_castLE
    (quartileSourceSequentialBoundaryAppend totalBudget round.val history block) hboundary]
  change quartileSourceSequentialBoundaryRoundBlock totalBudget round.val
      (quartileSourceSequentialBoundaryAppend totalBudget round.val history block) slot = block slot
  exact congrFun (quartileSourceSequentialBoundaryRoundBlock_append totalBudget round.val history block)
    slot

/-- The state and accumulated bad-round flag decoded directly from a
chronological boundary history.  Its dependent input length is exactly the
sum of the source blocks completed so far, which makes it match the PMF
disintegration at each induction step. -/
noncomputable def quartileSourceSequentialBoundaryStateFailure
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) :
    (completed : ℕ) →
      (Fin (quartileSourceSequentialRoundPrefixLength totalBudget completed) → Bool) →
        Finset Arm × Bool
  | 0, _ => (initial, false)
  | completed + 1, history => by
      classical
      let previous := quartileSourceSequentialBoundaryStateFailure mean error roundCount
        totalBudget initial completed
        (quartileSourceSequentialBoundaryPrefix totalBudget completed history)
      by_cases hround : completed < roundCount
      · let active := previous.1
        let outcome := quartileSourceSequentialRoundOutcome totalBudget completed active
          (quartileSourceSequentialBoundaryRoundBlock totalBudget completed history)
        let score : ℕ → Finset Arm → canonicalFreshQuartileOutcome Arm totalBudget → Arm → ℝ :=
          adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun round _ current => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget round current
            (quartileSourceRoundBudget_le_totalBudget totalBudget round))
        letI : Decidable (quartileRoundBad mean error score completed active outcome) :=
          Classical.propDecidable _
        exact (quartileRoundAdvance score completed active outcome,
          previous.2 || decide (quartileRoundBad mean error score completed active outcome))
      · exact previous

/-- Extending a boundary history by a scheduled literal source block performs
exactly the next fresh-round state and failure-flag update. -/
theorem quartileSourceSequentialBoundaryStateFailure_succ_append_eq_update
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (block : Fin (quartileSourceRoundBudget totalBudget round.val) → Bool) :
    quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
      (round.val + 1)
      (quartileSourceSequentialBoundaryAppend totalBudget round.val history block) =
      let previous := quartileSourceSequentialBoundaryStateFailure mean error roundCount
        totalBudget initial round.val history
      let active := previous.1
      let outcome := quartileSourceSequentialRoundOutcome totalBudget round.val active block
      (quartileRoundAdvance
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun earlier _ current => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget earlier current
            (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
        round.val active outcome,
        previous.2 || @decide (quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun earlier _ current => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget earlier current
              (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
          round.val active outcome) (Classical.propDecidable _)) := by
  classical
  simp [quartileSourceSequentialBoundaryStateFailure, round.isLt,
    quartileSourceSequentialBoundaryPrefix_append,
    quartileSourceSequentialBoundaryRoundBlock_append]

/-- The active component decoded from every boundary prefix is the ordinary
sequential replay state on its completed finite extension. -/
theorem quartileSourceSequentialBoundaryStateFailure_fst_eq_completePrefixState
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) :
    ∀ (completed : ℕ)
      (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget completed) → Bool),
      completed ≤ roundCount →
      (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
        completed history).1 =
        quartileSourceSequentialState roundCount totalBudget initial
          (quartileSourceSequentialCompletePrefixExtension history) completed := by
  intro completed
  induction completed with
  | zero =>
      intro history _
      rfl
  | succ completed ih =>
      intro history hcompleted
      have hround : completed < roundCount := by omega
      let priorHistory := quartileSourceSequentialBoundaryPrefix totalBudget completed history
      let sourceBlock := quartileSourceSequentialBoundaryRoundBlock totalBudget completed history
      have hdecompose : quartileSourceSequentialBoundaryAppend totalBudget completed priorHistory sourceBlock =
          history := by
        exact quartileSourceSequentialBoundaryAppend_prefix_roundBlock totalBudget completed history
      rw [← hdecompose]
      have hprevious := ih priorHistory (Nat.le_of_succ_le hcompleted)
      calc
        (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
            (completed + 1)
            (quartileSourceSequentialBoundaryAppend totalBudget completed priorHistory sourceBlock)).1 =
            quartileRoundAdvance
              (adaptiveBatchQuartileScore roundCount
                (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
                (fun earlier _ current => quartilePerArmSampleCount_le_roundCap
                  (quartileSourceRoundBudget totalBudget) totalBudget earlier current
                  (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
              completed
              (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
                completed priorHistory).1
              (quartileSourceSequentialRoundOutcome totalBudget completed
                (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
                  completed priorHistory).1 sourceBlock) := by
                rw [quartileSourceSequentialBoundaryStateFailure_succ_append_eq_update
                  mean error roundCount totalBudget initial ⟨completed, hround⟩ priorHistory sourceBlock]
        _ = quartileRoundAdvance
              (adaptiveBatchQuartileScore roundCount
                (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
                (fun earlier _ current => quartilePerArmSampleCount_le_roundCap
                  (quartileSourceRoundBudget totalBudget) totalBudget earlier current
                  (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
              completed
              (quartileSourceSequentialState roundCount totalBudget initial
                (quartileSourceSequentialCompletePrefixExtension priorHistory) completed)
              (quartileSourceSequentialRoundOutcome totalBudget completed
                (quartileSourceSequentialState roundCount totalBudget initial
                  (quartileSourceSequentialCompletePrefixExtension priorHistory) completed) sourceBlock) := by
                rw [hprevious]
        _ = quartileSourceSequentialState roundCount totalBudget initial
              (quartileSourceSequentialCompletePrefixExtension
                (quartileSourceSequentialBoundaryAppend totalBudget completed priorHistory sourceBlock))
              (completed + 1) := by
                rw [quartileSourceSequentialState_succ_eq_roundOutcomeAdvance
                  roundCount totalBudget initial
                  (quartileSourceSequentialCompletePrefixExtension
                    (quartileSourceSequentialBoundaryAppend totalBudget completed priorHistory sourceBlock))
                  ⟨completed, hround⟩]
                rw [quartileSourceSequentialState_completePrefix_boundaryAppend_eq
                  roundCount totalBudget initial ⟨completed, hround⟩ priorHistory sourceBlock,
                  quartileSourceSequentialRoundTrace_completePrefix_boundaryAppend_eq
                    roundCount totalBudget ⟨completed, hround⟩ priorHistory sourceBlock]

/-- The next boundary decoder expressed on the additive carrier used by the
prefix/suffix PMF factorization. -/
noncomputable def quartileSourceSequentialBoundaryStateFailureAfterBlock
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (round : Fin roundCount) :
    (Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val +
      quartileSourceRoundBudget totalBudget round.val) → Bool) → Finset Arm × Bool := fun trace =>
  quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
    (round.val + 1)
    (fun position => trace
      (Fin.cast (quartileSourceSequentialRoundPrefixLength_succ totalBudget round.val) position))

/-- On an appended source block, the additive-carrier decoder has the exact
fresh-round state/flag update. -/
theorem quartileSourceSequentialBoundaryStateFailureAfterBlock_append_eq_update
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (sourceBlock : Fin (quartileSourceRoundBudget totalBudget round.val) → Bool) :
    quartileSourceSequentialBoundaryStateFailureAfterBlock mean error roundCount totalBudget initial
      round (Fin.append history sourceBlock) =
      let previous := quartileSourceSequentialBoundaryStateFailure mean error roundCount
        totalBudget initial round.val history
      let active := previous.1
      let outcome := quartileSourceSequentialRoundOutcome totalBudget round.val active sourceBlock
      (quartileRoundAdvance
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun earlier _ current => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget earlier current
            (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
        round.val active outcome,
        previous.2 || @decide (quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun earlier _ current => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget earlier current
              (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
          round.val active outcome) (Classical.propDecidable _)) := by
  unfold quartileSourceSequentialBoundaryStateFailureAfterBlock
  exact quartileSourceSequentialBoundaryStateFailure_succ_append_eq_update
    mean error roundCount totalBudget initial round history sourceBlock

/-- At the literal end of any source block, its decoded allocated coordinates
have exactly the source fresh-outcome kernel.  This incorporates padding in
the conditional PMF rather than silently dropping it. -/
theorem adaptiveQuartileSourceSequentialQERoundBlockSuffixLaw_map_eq_sourceOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hstate : quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension history) round.val = active) :
    (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (quartileSourceRoundBudget totalBudget round.val)
      (quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
        roundCount totalBudget round)).map
      (quartileSourceSequentialRoundOutcome totalBudget round.val active) =
      quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round.val active := by
  let sampleCount := quartilePerArmSampleCount
    (quartileSourceRoundBudget totalBudget) round.val active
  let allocatedCount := Fintype.card (QuartileBatchCoordinate active sampleCount)
  let embed : (QuartileBatchCoordinate active sampleCount → Bool) →
      canonicalFreshQuartileOutcome Arm totalBudget := fun labels =>
    canonicalFreshQuartileEmbed totalBudget sampleCount
      (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
        totalBudget round.val active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active
      (quartileBatchCurry labels)
  have hallocated : allocatedCount ≤ quartileSourceRoundBudget totalBudget round.val := by
    dsimp [allocatedCount, sampleCount]
    rw [quartileBatchCoordinate_card]
    exact quartilePerArmSampleCount_total_le
      (quartileSourceRoundBudget totalBudget) round.val active
  have hroundBudget : quartileSourceSequentialRoundPrefixLength totalBudget round.val +
      quartileSourceRoundBudget totalBudget round.val ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) :=
    quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
      roundCount totalBudget round
  have hprefixMarginal :
      (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (quartileSourceRoundBudget totalBudget round.val)
        (quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
          roundCount totalBudget round)).map
        (rewardTracePrefixLE allocatedCount (quartileSourceRoundBudget totalBudget round.val)
          hallocated) =
      adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        allocatedCount (by
          apply Nat.le_trans (Nat.add_le_add_left hallocated _)
          exact quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
            roundCount totalBudget round) := by
    rw [adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix,
      adaptiveBernoulliRewardSuffixLaw_eq_continuationPrefix]
    exact adaptiveBernoulliRewardPrefixLaw_map_rewardTracePrefixLE mean hmean
      (adaptiveBernoulliContinuationProcedure
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val)
        (Nat.le_trans (Nat.le_add_right _ _) hroundBudget) history)
      allocatedCount (quartileSourceRoundBudget totalBudget round.val) hallocated
      (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hroundBudget))
  have hallocatedLaw := adaptiveQuartileSourceSequentialQERoundSuffixLaw_map_eq_flatBatchLaw
    mean hmean roundCount totalBudget initial hinitial round history active hactive hstate
  change (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (quartileSourceRoundBudget totalBudget round.val) _).map
      (embed ∘ quartileBatchTraceLabels active sampleCount ∘
        rewardTracePrefixLE allocatedCount
          (quartileSourceRoundBudget totalBudget round.val) hallocated) = _
  calc
    (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (quartileSourceRoundBudget totalBudget round.val) _).map
        (embed ∘ quartileBatchTraceLabels active sampleCount ∘
          rewardTracePrefixLE allocatedCount
            (quartileSourceRoundBudget totalBudget round.val) hallocated) =
      ((adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (quartileSourceRoundBudget totalBudget round.val) _).map
        (rewardTracePrefixLE allocatedCount
          (quartileSourceRoundBudget totalBudget round.val) hallocated)).map
        (embed ∘ quartileBatchTraceLabels active sampleCount) := by
            rw [PMF.map_comp]
            rfl
    _ = (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        allocatedCount _).map (embed ∘ quartileBatchTraceLabels active sampleCount) := by
          rw [hprefixMarginal]
    _ = ((quartileBernoulliBatchLaw mean hmean active sampleCount).map
        quartileBatchUncurry).map embed := by
          rw [← PMF.map_comp]
          simpa only [sampleCount, allocatedCount] using congrArg (PMF.map embed) hallocatedLaw
    _ = (quartileBernoulliBatchLaw mean hmean active sampleCount).map
        (fun batchTable => canonicalFreshQuartileEmbed totalBudget sampleCount
          (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
            totalBudget round.val active
            (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active batchTable) := by
          rw [PMF.map_comp]
          congr 1
    _ = quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round.val active := by
          simp [quartileSourceBudgetOutcomeLaw, quartileBudgetOutcomeLaw,
            adaptiveBatchQuartileOutcomeLaw, sampleCount, round.isLt]

/-- The preceding conditional replay law packaged in the tagged outcome
carrier used by the source's finite adaptive QE-round composition. -/
theorem adaptiveQuartileSourceSequentialQERoundSuffixLaw_map_eq_sourceOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (round : Fin roundCount)
    (history : Fin (quartileSourceSequentialRoundPrefixLength totalBudget round.val) → Bool)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hstate : quartileSourceSequentialState roundCount totalBudget initial
      (quartileSourceSequentialCompletePrefixExtension history) round.val = active) :
    (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (Fintype.card (QuartileBatchCoordinate active
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)))
      (by
        have hallocated : Fintype.card (QuartileBatchCoordinate active
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)) ≤
            quartileSourceRoundBudget totalBudget round.val := by
          simpa only [quartileBatchCoordinate_card] using
            (quartilePerArmSampleCount_total_le
              (quartileSourceRoundBudget totalBudget) round.val active)
        exact Nat.le_trans (Nat.add_le_add_left hallocated _)
          (quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
            roundCount totalBudget round))).map
      (fun rewardTrace => canonicalFreshQuartileEmbed totalBudget
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)
        (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
          totalBudget round.val active
          (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active
        (quartileBatchCurry (quartileBatchTraceLabels active
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round.val active)
          rewardTrace))) =
      quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round.val active := by
  let sampleCount := quartilePerArmSampleCount
    (quartileSourceRoundBudget totalBudget) round.val active
  let embed : (QuartileBatchCoordinate active sampleCount → Bool) →
      canonicalFreshQuartileOutcome Arm totalBudget := fun labels =>
    canonicalFreshQuartileEmbed totalBudget sampleCount
      (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
        totalBudget round.val active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active
      (quartileBatchCurry labels)
  have hflat := adaptiveQuartileSourceSequentialQERoundSuffixLaw_map_eq_flatBatchLaw
    mean hmean roundCount totalBudget initial hinitial round history active hactive hstate
  change (adaptiveBernoulliRewardSuffixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
      (Fintype.card (QuartileBatchCoordinate active sampleCount)) _).map
      (embed ∘ quartileBatchTraceLabels active sampleCount) = _
  calc
    (adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (Fintype.card (QuartileBatchCoordinate active sampleCount)) _).map
        (embed ∘ quartileBatchTraceLabels active sampleCount) =
      ((adaptiveBernoulliRewardSuffixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget round.val) history
        (Fintype.card (QuartileBatchCoordinate active sampleCount)) _).map
        (quartileBatchTraceLabels active sampleCount)).map embed := by
          rw [PMF.map_comp]
    _ = ((quartileBernoulliBatchLaw mean hmean active sampleCount).map
        quartileBatchUncurry).map embed := by
          simpa only [sampleCount] using congrArg (PMF.map embed) hflat
    _ = (quartileBernoulliBatchLaw mean hmean active sampleCount).map
        (fun batchTable => canonicalFreshQuartileEmbed totalBudget sampleCount
          (quartilePerArmSampleCount_le_roundCap (quartileSourceRoundBudget totalBudget)
            totalBudget round.val active
            (quartileSourceRoundBudget_le_totalBudget totalBudget round.val)) active batchTable) := by
          rw [PMF.map_comp]
          congr 1
    _ = quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round.val active := by
          simp [quartileSourceBudgetOutcomeLaw, quartileBudgetOutcomeLaw,
            adaptiveBatchQuartileOutcomeLaw, sampleCount, round.isLt]

/-- Reindexing a finite adaptive reward prefix along an equality of its
lengths preserves its PMF exactly.  This isolates the dependent transport at
the source boundary equation `P_(r+1) = P_r + Q_r`. -/
theorem adaptiveBernoulliRewardPrefixLaw_map_cast_eq
    {Arm : Type*} {pullBudget sourceCount targetCount : ℕ}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (procedure : FiniteAdaptiveBernoulliBestArmProcedure Arm pullBudget)
    (hlength : sourceCount = targetCount)
    (hsource : sourceCount ≤ pullBudget) (htarget : targetCount ≤ pullBudget) :
    (adaptiveBernoulliRewardPrefixLaw mean hmean procedure sourceCount hsource).map
      (fun trace position => trace (Fin.cast hlength.symm position)) =
      adaptiveBernoulliRewardPrefixLaw mean hmean procedure targetCount htarget := by
  cases hlength
  calc
    (adaptiveBernoulliRewardPrefixLaw mean hmean procedure sourceCount hsource).map
        (fun trace position => trace (Fin.cast (by rfl) position)) =
        (adaptiveBernoulliRewardPrefixLaw mean hmean procedure sourceCount hsource).map id := by
          congr 1
    _ = adaptiveBernoulliRewardPrefixLaw mean hmean procedure sourceCount hsource := PMF.map_id _
    _ = adaptiveBernoulliRewardPrefixLaw mean hmean procedure sourceCount htarget := by rfl

/-- At every source-round boundary, mapping the literal sequential reward
prefix to its decoded active state and bad-round flag gives the fresh QE
round-state law.  The supplied budget witness keeps this reusable at every
intermediate boundary. -/
theorem adaptiveQuartileSourceSequentialQERewardPrefixLaw_map_boundaryStateFailure_eq_freshQuartileRoundsStateLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty) :
    ∀ (completed : ℕ) (hcompleted : completed ≤ roundCount)
      (hbudget : quartileSourceSequentialRoundPrefixLength totalBudget completed ≤
        Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)),
      (adaptiveBernoulliRewardPrefixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength totalBudget completed) hbudget).map
        (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
          completed) =
        freshQuartileRoundsStateLaw mean error initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round _ active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) completed := by
  classical
  intro completed
  induction completed with
  | zero =>
      intro _ _
      simp [quartileSourceSequentialRoundPrefixLength,
        adaptiveBernoulliRewardPrefixLaw, freshQuartileRoundsStateLaw,
        adaptiveQueryStateLaw, quartileSourceSequentialBoundaryStateFailure]
      simpa only [PMF.pure_map]
  | succ completed ih =>
      intro hcompleted hbudget
      have hround : completed < roundCount := by omega
      have hstepBudget : quartileSourceSequentialRoundPrefixLength totalBudget completed +
          quartileSourceRoundBudget totalBudget completed ≤
          Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
        rw [← quartileSourceSequentialRoundPrefixLength_succ]
        exact hbudget
      have hpreviousBudget : quartileSourceSequentialRoundPrefixLength totalBudget completed ≤
          Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) :=
        Nat.le_trans (Nat.le_add_right _ _) hstepBudget
      let round : Fin roundCount := ⟨completed, hround⟩
      let castTrace :
          (Fin (quartileSourceSequentialRoundPrefixLength totalBudget (completed + 1)) → Bool) →
            Fin (quartileSourceSequentialRoundPrefixLength totalBudget completed +
              quartileSourceRoundBudget totalBudget completed) → Bool := fun trace position =>
        trace (Fin.cast (quartileSourceSequentialRoundPrefixLength_succ totalBudget completed).symm
          position)
      have hcastLaw := adaptiveBernoulliRewardPrefixLaw_map_cast_eq mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (quartileSourceSequentialRoundPrefixLength_succ totalBudget completed)
        hbudget hstepBudget
      have hdecoder : quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
          roundCount totalBudget initial round ∘ castTrace =
          quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
            (completed + 1) := by
        funext trace
        dsimp [Function.comp, quartileSourceSequentialBoundaryStateFailureAfterBlock, castTrace]
      calc
        (adaptiveBernoulliRewardPrefixLaw mean hmean
            (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
            (quartileSourceSequentialRoundPrefixLength totalBudget (completed + 1)) hbudget).map
            (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
              (completed + 1)) =
            ((adaptiveBernoulliRewardPrefixLaw mean hmean
              (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
              (quartileSourceSequentialRoundPrefixLength totalBudget (completed + 1)) hbudget).map
              castTrace).map
              (quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
                roundCount totalBudget initial round) := by
                rw [PMF.map_comp, hdecoder]
        _ = (adaptiveBernoulliRewardPrefixLaw mean hmean
              (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
              (quartileSourceSequentialRoundPrefixLength totalBudget completed +
                quartileSourceRoundBudget totalBudget completed) hstepBudget).map
              (quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
                roundCount totalBudget initial round) := by
                exact congrArg
                  (PMF.map (quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
                    roundCount totalBudget initial round)) hcastLaw
        _ = ((adaptiveBernoulliRewardPrefixLaw mean hmean
              (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
              (quartileSourceSequentialRoundPrefixLength totalBudget completed) hpreviousBudget).map
              (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
                completed)).bind
                (fun previous =>
                  (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget completed
                    previous.1).map
                    (fun outcome =>
                      (quartileRoundAdvance
                        (adaptiveBatchQuartileScore roundCount
                          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget))
                          totalBudget
                          (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
                            (quartileSourceRoundBudget totalBudget) totalBudget earlier active
                            (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
                        completed previous.1 outcome,
                        previous.2 || @decide (quartileRoundBad mean error
                          (adaptiveBatchQuartileScore roundCount
                            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget))
                            totalBudget
                            (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
                              (quartileSourceRoundBudget totalBudget) totalBudget earlier active
                              (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
                          completed previous.1 outcome) (Classical.propDecidable _)))) := by
                let update : (Finset Arm × Bool) →
                    canonicalFreshQuartileOutcome Arm totalBudget → Finset Arm × Bool :=
                  fun previous outcome =>
                    (quartileRoundAdvance
                      (adaptiveBatchQuartileScore roundCount
                        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
                        (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
                          (quartileSourceRoundBudget totalBudget) totalBudget earlier active
                          (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
                      completed previous.1 outcome,
                      previous.2 || @decide (quartileRoundBad mean error
                        (adaptiveBatchQuartileScore roundCount
                          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
                          (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
                            (quartileSourceRoundBudget totalBudget) totalBudget earlier active
                            (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
                        completed previous.1 outcome) (Classical.propDecidable _))
                have hstep :
                    (adaptiveBernoulliRewardPrefixLaw mean hmean
                      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                      (quartileSourceSequentialRoundPrefixLength totalBudget completed +
                        quartileSourceRoundBudget totalBudget completed) hstepBudget).map
                      (quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
                        roundCount totalBudget initial round) =
                    ((adaptiveBernoulliRewardPrefixLaw mean hmean
                      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                      (quartileSourceSequentialRoundPrefixLength totalBudget completed)
                      hpreviousBudget).map
                      (quartileSourceSequentialBoundaryStateFailure mean error roundCount
                        totalBudget initial completed)).bind
                      (fun previous =>
                        (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget completed
                          previous.1).map (update previous)) := by
                  rw [adaptiveBernoulliRewardPrefixLaw_eq_bind_suffix mean hmean
                    (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                    (quartileSourceSequentialRoundPrefixLength totalBudget completed)
                    (quartileSourceRoundBudget totalBudget completed) hstepBudget]
                  rw [PMF.map_bind, PMF.bind_map]
                  congr 1
                  funext history
                  let previous := quartileSourceSequentialBoundaryStateFailure mean error
                    roundCount totalBudget initial completed history
                  have hstate : quartileSourceSequentialState roundCount totalBudget initial
                      (quartileSourceSequentialCompletePrefixExtension history) completed = previous.1 := by
                    simpa [previous] using
                      (quartileSourceSequentialBoundaryStateFailure_fst_eq_completePrefixState
                        mean error roundCount totalBudget initial completed history
                        (Nat.le_of_succ_le hcompleted)).symm
                  have hactive : previous.1.Nonempty := by
                    rw [← hstate]
                    exact quartileSourceSequentialState_nonempty roundCount totalBudget initial hinitial
                      (quartileSourceSequentialCompletePrefixExtension history) completed
                  have hkernel :=
                    adaptiveQuartileSourceSequentialQERoundBlockSuffixLaw_map_eq_sourceOutcomeLaw
                      mean hmean roundCount totalBudget initial hinitial ⟨completed, hround⟩ history
                      previous.1 hactive hstate
                  have htransition :
                      quartileSourceSequentialBoundaryStateFailureAfterBlock mean error roundCount
                        totalBudget initial round ∘ Fin.append history =
                        update previous ∘
                          quartileSourceSequentialRoundOutcome totalBudget completed previous.1 := by
                    funext sourceBlock
                    simpa [update, previous] using
                      (quartileSourceSequentialBoundaryStateFailureAfterBlock_append_eq_update
                        mean error roundCount totalBudget initial round history sourceBlock)
                  calc
                    ((adaptiveBernoulliRewardSuffixLaw mean hmean
                      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                      (quartileSourceSequentialRoundPrefixLength totalBudget completed) history
                      (quartileSourceRoundBudget totalBudget completed) hstepBudget).map
                      (Fin.append history)).map
                      (quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
                        roundCount totalBudget initial round) =
                      (adaptiveBernoulliRewardSuffixLaw mean hmean
                        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                        (quartileSourceSequentialRoundPrefixLength totalBudget completed) history
                        (quartileSourceRoundBudget totalBudget completed) hstepBudget).map
                        (quartileSourceSequentialBoundaryStateFailureAfterBlock mean error
                          roundCount totalBudget initial round ∘ Fin.append history) := by
                          rw [PMF.map_comp]
                    _ = (adaptiveBernoulliRewardSuffixLaw mean hmean
                        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                        (quartileSourceSequentialRoundPrefixLength totalBudget completed) history
                        (quartileSourceRoundBudget totalBudget completed) hstepBudget).map
                        (update previous ∘
                          quartileSourceSequentialRoundOutcome totalBudget completed previous.1) := by
                          rw [htransition]
                    _ = ((adaptiveBernoulliRewardSuffixLaw mean hmean
                        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
                        (quartileSourceSequentialRoundPrefixLength totalBudget completed) history
                        (quartileSourceRoundBudget totalBudget completed) hstepBudget).map
                        (quartileSourceSequentialRoundOutcome totalBudget completed previous.1)).map
                        (update previous) := by
                          rw [PMF.map_comp]
                    _ = (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget completed
                        previous.1).map (update previous) := by
                          exact congrArg (PMF.map (update previous)) hkernel
                exact hstep
        _ = freshQuartileRoundsStateLaw mean error initial
              (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
              (adaptiveBatchQuartileScore roundCount
                (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
                (fun earlier _ active => quartilePerArmSampleCount_le_roundCap
                  (quartileSourceRoundBudget totalBudget) totalBudget earlier active
                  (quartileSourceRoundBudget_le_totalBudget totalBudget earlier)))
              (completed + 1) := by
                rw [ih (Nat.le_of_succ_le hcompleted) hpreviousBudget]
                rfl

/-- At the complete source QE horizon, the literal sequential pull trace,
decoded into its active state and accumulated round-failure flag, has exactly
the fresh adaptive QE-round PMF. -/
theorem adaptiveQuartileSourceSequentialQERewardLaw_map_boundaryStateFailure_eq_freshQuartileRoundsStateLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (error : ℕ → ℝ)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty) :
    let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount =
        Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
      simpa [quartileSourceSequentialRoundPrefixLength] using
        (quartileSourceSequentialSlot_card roundCount totalBudget).symm
    (adaptiveBernoulliRewardPrefixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) (Nat.le_refl _)).map
      (fun trace =>
        quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
          roundCount (fun position => trace (Fin.cast hboundary position))) =
      freshQuartileRoundsStateLaw mean error initial
        (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun round _ active => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget round active
            (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount := by
  classical
  dsimp
  let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount =
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
    simpa [quartileSourceSequentialRoundPrefixLength] using
      (quartileSourceSequentialSlot_card roundCount totalBudget).symm
  let castTrace :
      (Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool) →
        Fin (quartileSourceSequentialRoundPrefixLength totalBudget roundCount) → Bool := fun trace position =>
    trace (Fin.cast hboundary position)
  have hcastLaw := adaptiveBernoulliRewardPrefixLaw_map_cast_eq mean hmean
    (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial) hboundary.symm
    (Nat.le_refl _) hboundary.le
  calc
    (adaptiveBernoulliRewardPrefixLaw mean hmean
        (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
        (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) (Nat.le_refl _)).map
        (fun trace =>
          quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
            roundCount (fun position => trace (Fin.cast hboundary position))) =
        ((adaptiveBernoulliRewardPrefixLaw mean hmean
          (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
          (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget))
          (Nat.le_refl _)).map castTrace).map
          (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
            roundCount) := by
              rw [PMF.map_comp]
              rfl
    _ = (adaptiveBernoulliRewardPrefixLaw mean hmean
          (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
          (quartileSourceSequentialRoundPrefixLength totalBudget roundCount) hboundary.le).map
          (quartileSourceSequentialBoundaryStateFailure mean error roundCount totalBudget initial
            roundCount) := by
              exact congrArg
                (PMF.map (quartileSourceSequentialBoundaryStateFailure mean error roundCount
                  totalBudget initial roundCount)) hcastLaw
    _ = freshQuartileRoundsStateLaw mean error initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round _ active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount := by
              exact adaptiveQuartileSourceSequentialQERewardPrefixLaw_map_boundaryStateFailure_eq_freshQuartileRoundsStateLaw
                mean hmean error roundCount totalBudget initial hinitial roundCount (Nat.le_refl _)
                hboundary.le

/-- Every pull of the sequential QE prefix is an arm of the active set
reconstructed from its revealed history.  In particular, padding never
introduces an arm outside the current QE state. -/
theorem quartileSourceSequentialQEPull_mem_reconstructedState
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (position : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)))
    (history : Fin position.val → Bool) :
    quartileSourceSequentialQEPull roundCount totalBudget initial hinitial position history ∈
      quartileSourceSequentialState roundCount totalBudget initial
        (quartileSourceSequentialPrefixExtension position history)
        (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position).1.val := by
  unfold quartileSourceSequentialQEPull
  dsimp
  exact quartileSourceSequentialSlotArm_mem _ _ _ _ _

/-- The concrete sequential QE procedure uses at most the source's declared
total round allocation. -/
theorem quartileSourceSequentialQEProcedure_pullBudget_le_totalBudget
    (roundCount totalBudget : ℕ) :
    Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) ≤ totalBudget := by
  exact quartileSourceSequentialSlot_card_le_totalBudget roundCount totalBudget

end

end ZhouChenLi2014OptimalPACMultipleArm
