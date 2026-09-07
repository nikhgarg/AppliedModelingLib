import LMMS04FairDivision.Theorem41SourceCertificate

open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem41

noncomputable section

/-!
# Explicit Envy-Free Witnesses for LMMS Theorem 4.1

This module constructs the finite witness allocations used by the source proof:
player 1 receives good `a` plus a chosen set of eggs, and player 2 receives
good `b` plus all remaining eggs.
-/

/-- Canonical source allocation from a chosen set of eggs for player 1. -/
def lmms41CanonicalAllocation
    (eggsForPlayer1 : Bundle LMMS41Item) :
    Allocation LMMS41Agent LMMS41Item :=
  fun agent =>
    if agent = LMMS41Agent.player1 then
      insert LMMS41Item.a eggsForPlayer1
    else
      insert LMMS41Item.b (lmms41EggItems \ eggsForPlayer1)

theorem lmms41EggOnlyBundle_of_subset_eggItems
    {eggs : Bundle LMMS41Item}
    (hsub : eggs ⊆ lmms41EggItems) :
    lmms41EggOnlyBundle eggs := by
  constructor
  · intro ha
    exact (lmms41_mem_eggItems_iff.mp (hsub ha)).1 rfl
  · intro hb
    exact (lmms41_mem_eggItems_iff.mp (hsub hb)).2 rfl

theorem lmms41EggOnlyBundle_sdiff_eggItems
    (eggs : Bundle LMMS41Item) :
    lmms41EggOnlyBundle (lmms41EggItems \ eggs) := by
  apply lmms41EggOnlyBundle_of_subset_eggItems
  exact Finset.sdiff_subset

theorem lmms41CanonicalAllocation_isAllocationOf
    {eggs : Bundle LMMS41Item}
    (hsub : eggs ⊆ lmms41EggItems) :
    IsAllocationOf (lmms41CanonicalAllocation eggs) lmms41Goods := by
  constructor
  · intro agent item hmem
    simp [lmms41Goods]
  · intro item _hgoods
    by_cases ha : item = LMMS41Item.a
    · subst ha
      refine ⟨LMMS41Agent.player1, ?_, ?_⟩
      · simp [lmms41CanonicalAllocation]
      · intro owner howner
        rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
        · rfl
        · have hne : LMMS41Item.a ≠ LMMS41Item.b :=
            Ne.symm lmms41_item_b_ne_a
          simp [lmms41CanonicalAllocation, hne] at howner
    · by_cases hb : item = LMMS41Item.b
      · subst hb
        refine ⟨LMMS41Agent.player2, ?_, ?_⟩
        · simp [lmms41CanonicalAllocation]
        · intro owner howner
          rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
          · simp [lmms41CanonicalAllocation, lmms41_item_b_ne_a] at howner
            exact False.elim ((lmms41_mem_eggItems_iff.mp (hsub howner)).2 rfl)
          · rfl
      · have hegg : item ∈ lmms41EggItems :=
          (lmms41_mem_eggItems_iff).mpr ⟨ha, hb⟩
        by_cases hin : item ∈ eggs
        · refine ⟨LMMS41Agent.player1, ?_, ?_⟩
          · simp [lmms41CanonicalAllocation, hin, ha]
          · intro owner howner
            rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
            · rfl
            · simp [lmms41CanonicalAllocation, ha, hb, hin] at howner
        · refine ⟨LMMS41Agent.player2, ?_, ?_⟩
          · simp [lmms41CanonicalAllocation, hegg, hin, hb]
          · intro owner howner
            rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
            · simp [lmms41CanonicalAllocation, ha, hin] at howner
            · rfl

theorem lmms41CanonicalAllocation_player1
    (eggs : Bundle LMMS41Item) :
    lmms41CanonicalAllocation eggs LMMS41Agent.player1 =
      insert LMMS41Item.a eggs := by
  simp [lmms41CanonicalAllocation]

theorem lmms41CanonicalAllocation_player2
    (eggs : Bundle LMMS41Item) :
    lmms41CanonicalAllocation eggs LMMS41Agent.player2 =
      insert LMMS41Item.b (lmms41EggItems \ eggs) := by
  simp [lmms41CanonicalAllocation]

theorem lmms41CanonicalAllocation_remaining_eggs_card
    {eggs : Bundle LMMS41Item}
    (hsub : eggs ⊆ lmms41EggItems) :
    (lmms41EggItems \ eggs).card = 8 - eggs.card := by
  rw [Finset.card_sdiff_of_subset hsub, lmms41EggItems_card]

theorem lmms41CanonicalAllocation_trueReport_envyFree_of_card_eq_two
    {eggs : Bundle LMMS41Item}
    (hsub : eggs ⊆ lmms41EggItems)
    (hcard : eggs.card = 2) :
    ReportEnvyFree lmms41TrueReport (lmms41CanonicalAllocation eggs) := by
  have heggs : lmms41EggOnlyBundle eggs :=
    lmms41EggOnlyBundle_of_subset_eggItems hsub
  have hrem_eggs : lmms41EggOnlyBundle (lmms41EggItems \ eggs) :=
    lmms41EggOnlyBundle_sdiff_eggItems eggs
  have hrem_card : (lmms41EggItems \ eggs).card = 6 := by
    rw [lmms41CanonicalAllocation_remaining_eggs_card hsub, hcard]
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change
      lmms41TrueReport LMMS41Agent.player1
          (lmms41CanonicalAllocation eggs LMMS41Agent.player2) ≤
        lmms41TrueReport LMMS41Agent.player1
          (lmms41CanonicalAllocation eggs LMMS41Agent.player1)
    rw [lmms41CanonicalAllocation_player2, lmms41CanonicalAllocation_player1,
      lmms41TrueReport_player1_insert_b_eggOnly _ hrem_eggs,
      lmms41TrueReport_player1_insert_a_eggOnly _ heggs,
      hrem_card, hcard]
    norm_num
  · change
      lmms41TrueReport LMMS41Agent.player2
          (lmms41CanonicalAllocation eggs LMMS41Agent.player1) ≤
        lmms41TrueReport LMMS41Agent.player2
          (lmms41CanonicalAllocation eggs LMMS41Agent.player2)
    rw [lmms41CanonicalAllocation_player1, lmms41CanonicalAllocation_player2,
      lmms41TrueReport_player2_insert_a_eggOnly _ heggs,
      lmms41TrueReport_player2_insert_b_eggOnly _ hrem_eggs,
      hrem_card, hcard]
    norm_num
  · rfl

theorem lmms41_truthfulExists : LMMS41TruthfulExists := by
  obtain ⟨eggs, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq (s := lmms41EggItems) (n := 2)
      (by simp [lmms41EggItems_card])
  exact
    ⟨lmms41CanonicalAllocation eggs,
      lmms41CanonicalAllocation_isAllocationOf hsub,
      lmms41CanonicalAllocation_trueReport_envyFree_of_card_eq_two hsub hcard⟩

theorem lmms41CanonicalAllocation_player1Shifted_envyFree_of_card_eq_succ
    {T : ℕ} {eggs : Bundle LMMS41Item}
    (hTle : T ≤ 4)
    (hsub : eggs ⊆ lmms41EggItems)
    (hcard : eggs.card = T + 1) :
    ReportEnvyFree
      (Function.update lmms41TrueReport LMMS41Agent.player1
        (lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40)))
      (lmms41CanonicalAllocation eggs) := by
  let delta : ℝ := ((T : ℝ) - 1) / 40
  have heggs : lmms41EggOnlyBundle eggs :=
    lmms41EggOnlyBundle_of_subset_eggItems hsub
  have hrem_eggs : lmms41EggOnlyBundle (lmms41EggItems \ eggs) :=
    lmms41EggOnlyBundle_sdiff_eggItems eggs
  have hsumNat : eggs.card + (lmms41EggItems \ eggs).card = 8 := by
    rw [lmms41CanonicalAllocation_remaining_eggs_card hsub, hcard]
    omega
  have hsumReal :
      (eggs.card : ℝ) + ((lmms41EggItems \ eggs).card : ℝ) = 8 := by
    exact_mod_cast hsumNat
  have hcardReal : (eggs.card : ℝ) = (T : ℝ) + 1 := by
    exact_mod_cast hcard
  have hTleReal : (T : ℝ) ≤ 4 := by
    exact_mod_cast hTle
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change
      lmms41Player1ShiftedReport delta
          (lmms41CanonicalAllocation eggs LMMS41Agent.player2) ≤
        lmms41Player1ShiftedReport delta
          (lmms41CanonicalAllocation eggs LMMS41Agent.player1)
    rw [lmms41CanonicalAllocation_player2, lmms41CanonicalAllocation_player1,
      lmms41Player1ShiftedReport_insert_b_eggOnly delta _ hrem_eggs,
      lmms41Player1ShiftedReport_insert_a_eggOnly delta _ heggs]
    dsimp [delta]
    linarith
  · change
      lmms41TrueReport LMMS41Agent.player2
          (lmms41CanonicalAllocation eggs LMMS41Agent.player1) ≤
        lmms41TrueReport LMMS41Agent.player2
          (lmms41CanonicalAllocation eggs LMMS41Agent.player2)
    rw [lmms41CanonicalAllocation_player1, lmms41CanonicalAllocation_player2,
      lmms41TrueReport_player2_insert_a_eggOnly _ heggs,
      lmms41TrueReport_player2_insert_b_eggOnly _ hrem_eggs]
    linarith
  · rfl

theorem lmms41_player1ShiftedExistsFor (T : ℕ) (hTle : T ≤ 4) :
    LMMS41Player1ShiftedExistsFor T := by
  have hcard_le : T + 1 ≤ lmms41EggItems.card := by
    rw [lmms41EggItems_card]
    omega
  obtain ⟨eggs, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq (s := lmms41EggItems) (n := T + 1)
      hcard_le
  exact
    ⟨lmms41CanonicalAllocation eggs,
      lmms41CanonicalAllocation_isAllocationOf hsub,
      lmms41CanonicalAllocation_player1Shifted_envyFree_of_card_eq_succ
        hTle hsub hcard⟩

theorem lmms41CanonicalAllocation_player2Shifted_envyFree_of_card_eq
    {U : ℕ} {eggs : Bundle LMMS41Item}
    (hUle : U ≤ 3)
    (hsub : eggs ⊆ lmms41EggItems)
    (hcard : eggs.card = 7 - U) :
    ReportEnvyFree
      (Function.update lmms41TrueReport LMMS41Agent.player2
        (lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)))
      (lmms41CanonicalAllocation eggs) := by
  let delta : ℝ := ((U : ℝ) - 1) / 40
  have heggs : lmms41EggOnlyBundle eggs :=
    lmms41EggOnlyBundle_of_subset_eggItems hsub
  have hrem_eggs : lmms41EggOnlyBundle (lmms41EggItems \ eggs) :=
    lmms41EggOnlyBundle_sdiff_eggItems eggs
  have hsumNat : eggs.card + (lmms41EggItems \ eggs).card = 8 := by
    rw [lmms41CanonicalAllocation_remaining_eggs_card hsub, hcard]
    omega
  have hsumReal :
      (eggs.card : ℝ) + ((lmms41EggItems \ eggs).card : ℝ) = 8 := by
    exact_mod_cast hsumNat
  have hcardReal : (eggs.card : ℝ) = 7 - (U : ℝ) := by
    have hcardRealNat : (eggs.card : ℝ) = (7 - U : ℕ) := by
      exact_mod_cast hcard
    have hUle7 : U ≤ 7 := by omega
    rw [hcardRealNat, Nat.cast_sub hUle7]
    norm_num
  have hUleReal : (U : ℝ) ≤ 3 := by
    exact_mod_cast hUle
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change
      lmms41TrueReport LMMS41Agent.player1
          (lmms41CanonicalAllocation eggs LMMS41Agent.player2) ≤
        lmms41TrueReport LMMS41Agent.player1
          (lmms41CanonicalAllocation eggs LMMS41Agent.player1)
    rw [lmms41CanonicalAllocation_player2, lmms41CanonicalAllocation_player1,
      lmms41TrueReport_player1_insert_b_eggOnly _ hrem_eggs,
      lmms41TrueReport_player1_insert_a_eggOnly _ heggs]
    linarith
  · change
      lmms41Player2ShiftedReport delta
          (lmms41CanonicalAllocation eggs LMMS41Agent.player1) ≤
        lmms41Player2ShiftedReport delta
          (lmms41CanonicalAllocation eggs LMMS41Agent.player2)
    rw [lmms41CanonicalAllocation_player1, lmms41CanonicalAllocation_player2,
      lmms41Player2ShiftedReport_insert_a_eggOnly delta _ heggs,
      lmms41Player2ShiftedReport_insert_b_eggOnly delta _ hrem_eggs]
    dsimp [delta]
    linarith
  · rfl

theorem lmms41_player2ShiftedExistsFor (U : ℕ) (hUle : U ≤ 3) :
    LMMS41Player2ShiftedExistsFor U := by
  have hcard_le : 7 - U ≤ lmms41EggItems.card := by
    rw [lmms41EggItems_card]
    omega
  obtain ⟨eggs, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq (s := lmms41EggItems) (n := 7 - U)
      hcard_le
  exact
    ⟨lmms41CanonicalAllocation eggs,
      lmms41CanonicalAllocation_isAllocationOf hsub,
      lmms41CanonicalAllocation_player2Shifted_envyFree_of_card_eq
        hUle hsub hcard⟩

def lmms41_sourceCounterexampleCertificate
    (M : LMMS41Mechanism)
    (halloc : ReturnsAllocationOf M lmms41Goods)
    (hef : ReturnsEnvyFreeWheneverExists M lmms41Goods) :
    LMMS41SourceCounterexampleCertificate M :=
  lmms41_sourceCounterexampleCertificate_of_shifted_exists
    M halloc hef lmms41_truthfulExists
    lmms41_player1ShiftedExistsFor
    lmms41_player2ShiftedExistsFor

theorem lmms41_not_truthful_of_returnsEnvyFreeWheneverExists
    (M : LMMS41Mechanism)
    (halloc : ReturnsAllocationOf M lmms41Goods)
    (hef : ReturnsEnvyFreeWheneverExists M lmms41Goods) :
    ¬ M.Truthful := by
  exact
    lmms41_not_truthful_of_sourceCounterexampleCertificate M
      (lmms41_sourceCounterexampleCertificate M halloc hef)

end

end Theorem41
end LMMS04FairDivision
