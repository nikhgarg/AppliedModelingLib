import ZhouChenLi2014OptimalPACMultipleArm.QuartileSourceSchedule

/-!
# Finite slots for a sequential QE replay

The source allocates a fixed total `Q_r` to each QE round before the active
set is known. This carrier contains exactly those round slots. A later replay
uses an active arm on the allocated prefix of each round and ignores the
remaining slots; its cardinality therefore preserves the source allocation
rather than charging a rectangular `roundCount * Q` budget.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open scoped BigOperators

/-- One potential source-QE pull, indexed first by its scheduled round and
then by its position inside that round's fixed source budget. -/
abbrev quartileSourceSequentialSlot (roundCount totalBudget : ℕ) :=
  Σ round : Fin roundCount, Fin (quartileSourceRoundBudget totalBudget round)

/-- Number of chronological source slots strictly before a given QE round. -/
noncomputable def quartileSourceSequentialRoundPrefixLength
    (totalBudget round : ℕ) : ℕ :=
  ∑ earlier ∈ Finset.range round, quartileSourceRoundBudget totalBudget earlier

/-- Completing source round `r` advances the chronological boundary by its
literal fixed block budget. -/
theorem quartileSourceSequentialRoundPrefixLength_succ
    (totalBudget round : ℕ) :
    quartileSourceSequentialRoundPrefixLength totalBudget (round + 1) =
      quartileSourceSequentialRoundPrefixLength totalBudget round +
        quartileSourceRoundBudget totalBudget round := by
  simp [quartileSourceSequentialRoundPrefixLength, Finset.sum_range_succ]

/-- The chronological source-slot order: finish every slot in round `r`
before beginning round `r + 1`. -/
noncomputable def quartileSourceSequentialSlotList (roundCount totalBudget : ℕ) :
    List (quartileSourceSequentialSlot roundCount totalBudget) :=
  (List.ofFn fun round : Fin roundCount =>
    List.ofFn fun slot : Fin (quartileSourceRoundBudget totalBudget round) =>
      ⟨round, slot⟩).flatten

/-- The source slot queried at a chronological trace position. -/
noncomputable def quartileSourceSequentialSlotAt (roundCount totalBudget : ℕ) :
    Fin (quartileSourceSequentialSlotList roundCount totalBudget).length →
      quartileSourceSequentialSlot roundCount totalBudget :=
  (quartileSourceSequentialSlotList roundCount totalBudget).get

/-- The slot carrier has exactly the sum of the source's per-round budgets. -/
theorem quartileSourceSequentialSlot_card
    (roundCount totalBudget : ℕ) :
    Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) =
      ∑ round ∈ Finset.range roundCount,
        quartileSourceRoundBudget totalBudget round := by
  calc
    Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) =
        ∑ round : Fin roundCount,
          Fintype.card (Fin (quartileSourceRoundBudget totalBudget round)) :=
      Fintype.card_sigma
    _ = ∑ round : Fin roundCount,
          quartileSourceRoundBudget totalBudget round := by simp
    _ = ∑ round ∈ Finset.range roundCount,
        quartileSourceRoundBudget totalBudget round := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro round hround
      simp [Finset.mem_range.mp hround]

/-- The chronological prefix through any scheduled source round fits in the
fixed sequential horizon. -/
theorem quartileSourceSequentialRoundPrefixLength_add_roundBudget_le_card
    (roundCount totalBudget : ℕ) (round : Fin roundCount) :
    quartileSourceSequentialRoundPrefixLength totalBudget round.val +
      quartileSourceRoundBudget totalBudget round.val ≤
        Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
  rw [quartileSourceSequentialSlot_card]
  have hprefix : quartileSourceSequentialRoundPrefixLength totalBudget round.val +
      quartileSourceRoundBudget totalBudget round.val =
        ∑ earlier ∈ Finset.range (round.val + 1),
          quartileSourceRoundBudget totalBudget earlier := by
    simp [quartileSourceSequentialRoundPrefixLength, Finset.sum_range_succ]
  rw [hprefix]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (Nat.succ_le_of_lt round.isLt)
  · intro _ _ _
    omega

/-- The direct chronological position of a source slot.  This is the prefix
sum of earlier round budgets plus the slot's coordinate within its own round. -/
noncomputable def quartileSourceSequentialSlotIndex
    (roundCount totalBudget : ℕ)
    (slot : quartileSourceSequentialSlot roundCount totalBudget) :
    Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) :=
  ⟨quartileSourceSequentialRoundPrefixLength totalBudget slot.1.val + slot.2.val, by
    rw [quartileSourceSequentialSlot_card]
    have hslot : quartileSourceSequentialRoundPrefixLength totalBudget slot.1.val + slot.2.val <
        quartileSourceSequentialRoundPrefixLength totalBudget slot.1.val +
          quartileSourceRoundBudget totalBudget slot.1.val :=
      Nat.add_lt_add_left slot.2.isLt _
    have hprefix : quartileSourceSequentialRoundPrefixLength totalBudget slot.1.val +
        quartileSourceRoundBudget totalBudget slot.1.val =
        ∑ earlier ∈ Finset.range (slot.1.val + 1),
          quartileSourceRoundBudget totalBudget earlier := by
      simp [quartileSourceSequentialRoundPrefixLength, Finset.sum_range_succ]
    have hsum : (∑ earlier ∈ Finset.range (slot.1.val + 1),
        quartileSourceRoundBudget totalBudget earlier) ≤
        ∑ earlier ∈ Finset.range roundCount,
          quartileSourceRoundBudget totalBudget earlier := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_subset_range.mpr (Nat.succ_le_of_lt slot.1.isLt)
      · intro _ _ _
        omega
    exact hslot.trans_le (hprefix.trans_le hsum)⟩

/-- Earlier source rounds occupy strictly earlier direct chronological slots. -/
theorem quartileSourceSequentialSlotIndex_lt_of_round_lt
    {roundCount totalBudget : ℕ}
    (first second : quartileSourceSequentialSlot roundCount totalBudget)
    (hround : first.1.val < second.1.val) :
    (quartileSourceSequentialSlotIndex roundCount totalBudget first).val <
      (quartileSourceSequentialSlotIndex roundCount totalBudget second).val := by
  let firstPrefix := quartileSourceSequentialRoundPrefixLength totalBudget first.1.val
  let secondPrefix := quartileSourceSequentialRoundPrefixLength totalBudget second.1.val
  have hfirstSlot : firstPrefix + first.2.val <
      firstPrefix + quartileSourceRoundBudget totalBudget first.1.val :=
    Nat.add_lt_add_left first.2.isLt _
  have hfirstPrefix : firstPrefix + quartileSourceRoundBudget totalBudget first.1.val =
      ∑ earlier ∈ Finset.range (first.1.val + 1),
        quartileSourceRoundBudget totalBudget earlier := by
    dsimp [firstPrefix, quartileSourceSequentialRoundPrefixLength]
    rw [Finset.sum_range_succ]
  have hsum : (∑ earlier ∈ Finset.range (first.1.val + 1),
      quartileSourceRoundBudget totalBudget earlier) ≤
      ∑ earlier ∈ Finset.range second.1.val,
        quartileSourceRoundBudget totalBudget earlier := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (Nat.succ_le_of_lt hround)
    · intro _ _ _
      omega
  have hsecondPrefix : secondPrefix =
      ∑ earlier ∈ Finset.range second.1.val,
        quartileSourceRoundBudget totalBudget earlier := by
    rfl
  have horder : firstPrefix + first.2.val < secondPrefix + second.2.val :=
    hfirstSlot.trans_le
      (hfirstPrefix.trans_le (hsum.trans (by simp [hsecondPrefix])))
  simpa [quartileSourceSequentialSlotIndex, firstPrefix, secondPrefix] using horder

/-- Every source slot from a strictly earlier round lies before the prefix
boundary of a later round. -/
theorem quartileSourceSequentialSlotIndex_lt_roundPrefixLength_of_round_lt
    {roundCount totalBudget : ℕ}
    (earlier : quartileSourceSequentialSlot roundCount totalBudget)
    (round : Fin roundCount) (hround : earlier.1.val < round.val) :
    (quartileSourceSequentialSlotIndex roundCount totalBudget earlier).val <
      quartileSourceSequentialRoundPrefixLength totalBudget round.val := by
  let earlierPrefix := quartileSourceSequentialRoundPrefixLength totalBudget earlier.1.val
  have hslot : earlierPrefix + earlier.2.val <
      earlierPrefix + quartileSourceRoundBudget totalBudget earlier.1.val :=
    Nat.add_lt_add_left earlier.2.isLt _
  have hprevious : earlierPrefix + quartileSourceRoundBudget totalBudget earlier.1.val =
      ∑ index ∈ Finset.range (earlier.1.val + 1),
        quartileSourceRoundBudget totalBudget index := by
    dsimp [earlierPrefix, quartileSourceSequentialRoundPrefixLength]
    rw [Finset.sum_range_succ]
  have hsum : (∑ index ∈ Finset.range (earlier.1.val + 1),
      quartileSourceRoundBudget totalBudget index) ≤
      ∑ index ∈ Finset.range round.val,
        quartileSourceRoundBudget totalBudget index := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (Nat.succ_le_of_lt hround)
    · intro _ _ _
      omega
  simpa [quartileSourceSequentialSlotIndex, earlierPrefix,
    quartileSourceSequentialRoundPrefixLength] using hslot.trans_le (hprevious.trans_le hsum)

/-- Direct chronological slot positions are injective. -/
theorem quartileSourceSequentialSlotIndex_injective
    (roundCount totalBudget : ℕ) :
    Function.Injective (quartileSourceSequentialSlotIndex roundCount totalBudget) := by
  rintro ⟨firstRound, firstSlot⟩ ⟨secondRound, secondSlot⟩ hequal
  have hroundLe : firstRound.val ≤ secondRound.val := by
    by_contra hnot
    have hlt : secondRound.val < firstRound.val := Nat.lt_of_not_ge hnot
    have horder := quartileSourceSequentialSlotIndex_lt_of_round_lt
      ⟨secondRound, secondSlot⟩ ⟨firstRound, firstSlot⟩ hlt
    have hvalue :
        (quartileSourceSequentialSlotIndex roundCount totalBudget
          ⟨secondRound, secondSlot⟩).val =
          (quartileSourceSequentialSlotIndex roundCount totalBudget
            ⟨firstRound, firstSlot⟩).val :=
      congrArg Fin.val hequal.symm
    exact (ne_of_lt horder) hvalue
  have hroundGe : secondRound.val ≤ firstRound.val := by
    by_contra hnot
    have hlt : firstRound.val < secondRound.val := Nat.lt_of_not_ge hnot
    have horder := quartileSourceSequentialSlotIndex_lt_of_round_lt
      ⟨firstRound, firstSlot⟩ ⟨secondRound, secondSlot⟩ hlt
    have hvalue :
        (quartileSourceSequentialSlotIndex roundCount totalBudget
          ⟨firstRound, firstSlot⟩).val =
          (quartileSourceSequentialSlotIndex roundCount totalBudget
            ⟨secondRound, secondSlot⟩).val :=
      congrArg Fin.val hequal
    exact (ne_of_lt horder) hvalue
  have hround : firstRound = secondRound := Fin.ext (Nat.le_antisymm hroundLe hroundGe)
  subst secondRound
  have hslot : firstSlot.val = secondSlot.val := by
    apply Nat.add_left_cancel
      (n := quartileSourceSequentialRoundPrefixLength totalBudget firstRound.val)
    simpa [quartileSourceSequentialSlotIndex] using congrArg Fin.val hequal
  congr
  exact Fin.ext hslot

/-- The direct prefix-sum indexing is a chronological equivalence from the
fixed policy horizon to the source's round slots. -/
noncomputable def quartileSourceSequentialChronologicalSlotEquiv
    (roundCount totalBudget : ℕ) :
    Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) ≃
      quartileSourceSequentialSlot roundCount totalBudget := by
  let index := quartileSourceSequentialSlotIndex roundCount totalBudget
  have hbijective : Function.Bijective index :=
    (Fintype.bijective_iff_injective_and_card index).mpr
      ⟨quartileSourceSequentialSlotIndex_injective roundCount totalBudget, by simp⟩
  exact (Equiv.ofBijective index hbijective).symm

/-- A source slot's inverse chronological-equivalence coordinate is its
explicit prefix-sum index. -/
@[simp]
theorem quartileSourceSequentialChronologicalSlotEquiv_symm_apply
    (roundCount totalBudget : ℕ)
    (slot : quartileSourceSequentialSlot roundCount totalBudget) :
    (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm slot =
      quartileSourceSequentialSlotIndex roundCount totalBudget slot := by
  rfl

/-- Applying the chronological slot equivalence at a direct slot index
recovers that exact source slot. -/
@[simp]
theorem quartileSourceSequentialChronologicalSlotEquiv_apply_index
    (roundCount totalBudget : ℕ)
    (slot : quartileSourceSequentialSlot roundCount totalBudget) :
    quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
      (quartileSourceSequentialSlotIndex roundCount totalBudget slot) = slot := by
  calc
    quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
        (quartileSourceSequentialSlotIndex roundCount totalBudget slot) =
        quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget
          ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm slot) := by
            rw [quartileSourceSequentialChronologicalSlotEquiv_symm_apply]
    _ = slot :=
      (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).apply_symm_apply slot

/-- A slot from an earlier source round lies strictly before every position in
a later round's chronological block. -/
theorem quartileSourceSequentialChronologicalSlotPosition_lt_of_round_lt
    {roundCount totalBudget : ℕ}
    (position : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)))
    (earlier : quartileSourceSequentialSlot roundCount totalBudget)
    (hround : earlier.1.val <
      (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position).1.val) :
    ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm earlier).val <
      position.val := by
  calc
    ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm earlier).val =
        (quartileSourceSequentialSlotIndex roundCount totalBudget earlier).val := by
          rw [quartileSourceSequentialChronologicalSlotEquiv_symm_apply]
    _ < (quartileSourceSequentialSlotIndex roundCount totalBudget
          (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position)).val :=
      quartileSourceSequentialSlotIndex_lt_of_round_lt earlier
        (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position) hround
    _ = ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm
          (quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget position)).val := by
            rw [quartileSourceSequentialChronologicalSlotEquiv_symm_apply]
    _ = position.val := congrArg Fin.val
      ((quartileSourceSequentialChronologicalSlotEquiv roundCount totalBudget).symm_apply_apply position)

/-- The chronological slot list has exactly the cardinality of the finite
source-slot carrier.  This is the length bridge needed to use the list as a
fixed finite adaptive-policy horizon without charging unused rectangular
round/arm coordinates. -/
theorem quartileSourceSequentialSlotList_length
    (roundCount totalBudget : ℕ) :
    (quartileSourceSequentialSlotList roundCount totalBudget).length =
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
  rw [quartileSourceSequentialSlot_card]
  unfold quartileSourceSequentialSlotList
  simp only [List.length_flatten]
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  simp only [List.length_ofFn]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro round hround
  simp [Finset.mem_range.mp hround]

/-- Every source slot occurs exactly once in the chronological list. -/
theorem quartileSourceSequentialSlotList_nodup
    (roundCount totalBudget : ℕ) :
    (quartileSourceSequentialSlotList roundCount totalBudget).Nodup := by
  unfold quartileSourceSequentialSlotList
  rw [List.nodup_flatten]
  constructor
  · intro slotList hslotList
    rcases (List.mem_ofFn.mp hslotList) with ⟨round, rfl⟩
    apply List.nodup_ofFn_ofInjective
    intro first second hequal
    simpa only [Sigma.mk.inj_iff, true_and, heq_eq_eq] using hequal
  · rw [List.pairwise_ofFn]
    intro first second hfirstSecond
    rw [List.disjoint_left]
    intro slot hfirst hsecond
    rcases (List.mem_ofFn.mp hfirst) with ⟨firstSlot, rfl⟩
    rcases (List.mem_ofFn.mp hsecond) with ⟨secondSlot, hequal⟩
    apply (ne_of_lt hfirstSecond)
    exact congrArg Sigma.fst hequal.symm

/-- Every element of the finite source-slot carrier appears in chronological
order in the sequential slot list. -/
theorem mem_quartileSourceSequentialSlotList
    (roundCount totalBudget : ℕ)
    (slot : quartileSourceSequentialSlot roundCount totalBudget) :
    slot ∈ quartileSourceSequentialSlotList roundCount totalBudget := by
  rcases slot with ⟨round, position⟩
  unfold quartileSourceSequentialSlotList
  apply List.mem_flatten.mpr
  refine ⟨List.ofFn (fun position : Fin (quartileSourceRoundBudget totalBudget round) =>
    ⟨round, position⟩), ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨round, rfl⟩
  · exact List.mem_ofFn.mpr ⟨position, rfl⟩

/-- The chronological list gives a concrete bijection from a fixed finite
policy horizon to the source's round-budget slot carrier. -/
noncomputable def quartileSourceSequentialSlotEquiv
    (roundCount totalBudget : ℕ) :
    Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) ≃
      quartileSourceSequentialSlot roundCount totalBudget := by
  classical
  exact (finCongr (quartileSourceSequentialSlotList_length roundCount totalBudget).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (quartileSourceSequentialSlotList roundCount totalBudget)
      (quartileSourceSequentialSlotList_nodup roundCount totalBudget)
      (mem_quartileSourceSequentialSlotList roundCount totalBudget))

/-- The fixed slot carrier never exceeds the source's total QE allocation. -/
theorem quartileSourceSequentialSlot_card_le_totalBudget
    (roundCount totalBudget : ℕ) :
    Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) ≤ totalBudget := by
  rw [quartileSourceSequentialSlot_card]
  exact quartileSourceRoundBudget_sum_le_totalBudget totalBudget roundCount

/-- Along every active-set path, the samples actually consumed by the floored
QE allocation fit within the fixed source slot carrier. -/
theorem quartileSourceAllocation_total_le_sequentialSlot_card
    {Arm : Type*} (totalBudget roundCount : ℕ) (active : ℕ → Finset Arm) :
    ∑ round ∈ Finset.range roundCount,
      (active round).card *
        quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round
          (active round) ≤
      Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
  rw [quartileSourceSequentialSlot_card]
  apply Finset.sum_le_sum
  intro round hround
  exact quartilePerArmSampleCount_total_le
    (quartileSourceRoundBudget totalBudget) round (active round)

end ZhouChenLi2014OptimalPACMultipleArm
