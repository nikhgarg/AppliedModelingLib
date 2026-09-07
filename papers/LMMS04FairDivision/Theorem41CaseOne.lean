import LMMS04FairDivision.Theorem41

open scoped BigOperators
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem41

noncomputable section

/-!
# Player-1 Case Split for LMMS Theorem 4.1

This sidecar proves the first source-proof case: when the truthful allocation
gives player 1 at most four eggs along with good `a`, player 1's shifted report
forces any exact shifted-profile envy-free allocation to give player 1 good `a`
and at least one additional egg.
-/

/-- Player 1's first-case shifted report profile with `delta = (T - 1) / 40`. -/
def lmms41Player1CaseReport (T : ℕ) : LMMS41Report :=
  Function.update lmms41TrueReport LMMS41Agent.player1
    (lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40))

theorem lmms41Player1ShiftedReport_eggOnly_le_fifth
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player1ShiftedReport delta eggs ≤ (1 : ℝ) / 5 := by
  rw [lmms41Player1ShiftedReport_eggOnly delta eggs heggs]
  have hcard : (eggs.card : ℝ) ≤ 8 := by
    exact_mod_cast lmms41EggOnly_card_le_eight heggs
  linarith

theorem lmms41Player1ShiftedReport_insert_a_insert_b_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player1ShiftedReport delta
        (insert LMMS41Item.a (insert LMMS41Item.b eggs)) =
      (4 : ℝ) / 5 + (eggs.card : ℝ) / 40 := by
  rw [lmms41Player1ShiftedReport, lmms41AdditiveReport]
  have ha_not : LMMS41Item.a ∉ insert LMMS41Item.b eggs := by
    simp [heggs.1, Ne.symm lmms41_item_b_ne_a]
  rw [Finset.sum_insert ha_not]
  rw [Finset.sum_insert heggs.2]
  change
    lmms41Player1ShiftedWeight delta LMMS41Agent.player1 LMMS41Item.a +
        (lmms41Player1ShiftedWeight delta LMMS41Agent.player1 LMMS41Item.b +
          lmms41Player1ShiftedReport delta eggs) =
      (4 : ℝ) / 5 + (eggs.card : ℝ) / 40
  rw [lmms41Player1ShiftedReport_eggOnly delta eggs heggs]
  simp
  ring

theorem lmms41_player1CaseReport_envyFree_namedGoods_of_T_le_four
    {B : Allocation LMMS41Agent LMMS41Item} {T : ℕ}
    (hTle : T ≤ 4)
    (halloc : IsAllocationOf B lmms41Goods)
    (hef : ReportEnvyFree (lmms41Player1CaseReport T) B) :
    LMMS41Item.a ∈ B LMMS41Agent.player1 ∧
      LMMS41Item.b ∈ B LMMS41Agent.player2 ∧
      LMMS41Item.b ∉ B LMMS41Agent.player1 ∧
      LMMS41Item.a ∉ B LMMS41Agent.player2 := by
  let delta : ℝ := ((T : ℝ) - 1) / 40
  by_cases ha1 : LMMS41Item.a ∈ B LMMS41Agent.player1
  · have hnot_a2 : LMMS41Item.a ∉ B LMMS41Agent.player2 :=
      lmms41_not_mem_player2_of_mem_player1_of_alloc halloc ha1
    by_cases hb1 : LMMS41Item.b ∈ B LMMS41Agent.player1
    · have hnot_b2 : LMMS41Item.b ∉ B LMMS41Agent.player2 :=
        lmms41_not_mem_player2_of_mem_player1_of_alloc halloc hb1
      have hp2_eggs : lmms41EggOnlyBundle (B LMMS41Agent.player2) :=
        ⟨hnot_a2, hnot_b2⟩
      have hown :
          lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player2) ≤
            (1 : ℝ) / 5 :=
        lmms41TrueReport_player2_eggOnly_le_fifth _ hp2_eggs
      have hother :
          (4 : ℝ) / 5 ≤
            lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player1) :=
        lmms41TrueReport_player2_pair_ab_le_of_mem ha1 hb1
      have hnoenvy :
          lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player1) ≤
            lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player2) := by
        simpa [lmms41Player1CaseReport, LMMS41Agent.player1,
          LMMS41Agent.player2] using
          hef LMMS41Agent.player2 LMMS41Agent.player1
      linarith
    · have hb2 : LMMS41Item.b ∈ B LMMS41Agent.player2 :=
        lmms41_mem_player2_of_not_mem_player1_of_alloc halloc hb1
      exact ⟨ha1, hb2, hb1, hnot_a2⟩
  · have ha2 : LMMS41Item.a ∈ B LMMS41Agent.player2 :=
      lmms41_mem_player2_of_not_mem_player1_of_alloc halloc ha1
    by_cases hb1 : LMMS41Item.b ∈ B LMMS41Agent.player1
    · let eggs1 := lmms41EggRemainder B LMMS41Agent.player1
      let eggs2 := lmms41EggRemainder B LMMS41Agent.player2
      have hnot_b2 : LMMS41Item.b ∉ B LMMS41Agent.player2 :=
        lmms41_not_mem_player2_of_mem_player1_of_alloc halloc hb1
      have heggs1 : lmms41EggOnlyBundle eggs1 :=
        lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player1
      have heggs2 : lmms41EggOnlyBundle eggs2 :=
        lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player2
      have hB1 :
          insert LMMS41Item.b eggs1 = B LMMS41Agent.player1 :=
        lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb1 ha1
      have hB2 :
          insert LMMS41Item.a eggs2 = B LMMS41Agent.player2 :=
        lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b ha2 hnot_b2
      have hp1_noenvy :
          lmms41Player1ShiftedReport delta (B LMMS41Agent.player2) ≤
            lmms41Player1ShiftedReport delta (B LMMS41Agent.player1) := by
        simpa [lmms41Player1CaseReport, delta] using
          hef LMMS41Agent.player1 LMMS41Agent.player2
      rw [← hB2, ← hB1,
        lmms41Player1ShiftedReport_insert_a_eggOnly delta eggs2 heggs2,
        lmms41Player1ShiftedReport_insert_b_eggOnly delta eggs1 heggs1] at hp1_noenvy
      have hp2_noenvy :
          lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player1) ≤
            lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player2) := by
        simpa [lmms41Player1CaseReport, LMMS41Agent.player1,
          LMMS41Agent.player2] using
          hef LMMS41Agent.player2 LMMS41Agent.player1
      rw [← hB1, ← hB2,
        lmms41TrueReport_player2_insert_b_eggOnly eggs1 heggs1,
        lmms41TrueReport_player2_insert_a_eggOnly eggs2 heggs2] at hp2_noenvy
      have hsumNat : eggs1.card + eggs2.card = 8 :=
        lmms41_eggRemainder_card_sum halloc
      have hsumReal : (eggs1.card : ℝ) + (eggs2.card : ℝ) = 8 := by
        exact_mod_cast hsumNat
      have hTleReal : (T : ℝ) ≤ 4 := by
        exact_mod_cast hTle
      dsimp [delta] at hp1_noenvy
      linarith
    · have hb2 : LMMS41Item.b ∈ B LMMS41Agent.player2 :=
        lmms41_mem_player2_of_not_mem_player1_of_alloc halloc hb1
      have hp1_eggs : lmms41EggOnlyBundle (B LMMS41Agent.player1) :=
        ⟨ha1, hb1⟩
      let eggs2 := lmms41EggRemainder B LMMS41Agent.player2
      have heggs2 : lmms41EggOnlyBundle eggs2 :=
        lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player2
      have hB2 :
          insert LMMS41Item.a (insert LMMS41Item.b eggs2) =
            B LMMS41Agent.player2 :=
        lmms41_insert_a_insert_b_eggRemainder_eq_of_mem_a_mem_b ha2 hb2
      have hown :
          lmms41Player1ShiftedReport delta (B LMMS41Agent.player1) ≤
            (1 : ℝ) / 5 :=
        lmms41Player1ShiftedReport_eggOnly_le_fifth delta
          (B LMMS41Agent.player1) hp1_eggs
      have hother :
          (4 : ℝ) / 5 ≤
            lmms41Player1ShiftedReport delta (B LMMS41Agent.player2) := by
        rw [← hB2,
          lmms41Player1ShiftedReport_insert_a_insert_b_eggOnly
            delta eggs2 heggs2]
        have hnonneg : 0 ≤ (eggs2.card : ℝ) / 40 := by positivity
        linarith
      have hnoenvy :
          lmms41Player1ShiftedReport delta (B LMMS41Agent.player2) ≤
            lmms41Player1ShiftedReport delta (B LMMS41Agent.player1) := by
        simpa [lmms41Player1CaseReport, delta] using
          hef LMMS41Agent.player1 LMMS41Agent.player2
      linarith

theorem lmms41_player1CaseReport_envyFree_player1_egg_card_ge_succ
    {B : Allocation LMMS41Agent LMMS41Item} {T : ℕ}
    (hTle : T ≤ 4)
    (halloc : IsAllocationOf B lmms41Goods)
    (hef : ReportEnvyFree (lmms41Player1CaseReport T) B) :
    T + 1 ≤ (lmms41EggRemainder B LMMS41Agent.player1).card := by
  let delta : ℝ := ((T : ℝ) - 1) / 40
  let eggs1 := lmms41EggRemainder B LMMS41Agent.player1
  let eggs2 := lmms41EggRemainder B LMMS41Agent.player2
  obtain ⟨ha1, hb2, hnot_b1, hnot_a2⟩ :=
    lmms41_player1CaseReport_envyFree_namedGoods_of_T_le_four
      hTle halloc hef
  have heggs1 : lmms41EggOnlyBundle eggs1 :=
    lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player1
  have heggs2 : lmms41EggOnlyBundle eggs2 :=
    lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player2
  have hB1 :
      insert LMMS41Item.a eggs1 = B LMMS41Agent.player1 :=
    lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b ha1 hnot_b1
  have hB2 :
      insert LMMS41Item.b eggs2 = B LMMS41Agent.player2 :=
    lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb2 hnot_a2
  have hp1_noenvy :
      lmms41Player1ShiftedReport delta (B LMMS41Agent.player2) ≤
        lmms41Player1ShiftedReport delta (B LMMS41Agent.player1) := by
    simpa [lmms41Player1CaseReport, delta] using
      hef LMMS41Agent.player1 LMMS41Agent.player2
  rw [← hB2, ← hB1,
    lmms41Player1ShiftedReport_insert_b_eggOnly delta eggs2 heggs2,
    lmms41Player1ShiftedReport_insert_a_eggOnly delta eggs1 heggs1] at hp1_noenvy
  have hsumNat : eggs1.card + eggs2.card = 8 :=
    lmms41_eggRemainder_card_sum halloc
  have hsumReal : (eggs1.card : ℝ) + (eggs2.card : ℝ) = 8 := by
    exact_mod_cast hsumNat
  have hlowerReal : (T : ℝ) + 1 ≤ (eggs1.card : ℝ) := by
    dsimp [delta] at hp1_noenvy
    linarith
  exact_mod_cast hlowerReal

theorem lmms41_case_one_player1_deviation_better
    {A B : Allocation LMMS41Agent LMMS41Item}
    (hAalloc : IsAllocationOf A lmms41Goods)
    (hAef : ReportEnvyFree lmms41TrueReport A)
    (hTle : (lmms41EggRemainder A LMMS41Agent.player1).card ≤ 4)
    (hBalloc : IsAllocationOf B lmms41Goods)
    (hBef :
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player1
          (lmms41Player1ShiftedReport
            ((((lmms41EggRemainder A LMMS41Agent.player1).card : ℝ) - 1) /
              40)))
        B) :
    lmms41TrueReport LMMS41Agent.player1 (A LMMS41Agent.player1) <
      lmms41TrueReport LMMS41Agent.player1 (B LMMS41Agent.player1) := by
  let T := (lmms41EggRemainder A LMMS41Agent.player1).card
  change ReportEnvyFree (lmms41Player1CaseReport T) B at hBef
  let eggsA := lmms41EggRemainder A LMMS41Agent.player1
  let eggsB := lmms41EggRemainder B LMMS41Agent.player1
  obtain ⟨haA, _hb2A, hnot_bA, _hnot_a2A⟩ :=
    lmms41_trueReport_envyFree_namedGoods hAalloc hAef
  obtain ⟨haB, _hb2B, hnot_bB, _hnot_a2B⟩ :=
    lmms41_player1CaseReport_envyFree_namedGoods_of_T_le_four
      hTle hBalloc hBef
  have heggsA : lmms41EggOnlyBundle eggsA :=
    lmms41EggOnlyBundle_eggRemainder A LMMS41Agent.player1
  have heggsB : lmms41EggOnlyBundle eggsB :=
    lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player1
  have hA1 :
      insert LMMS41Item.a eggsA = A LMMS41Agent.player1 :=
    lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b haA hnot_bA
  have hB1 :
      insert LMMS41Item.a eggsB = B LMMS41Agent.player1 :=
    lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b haB hnot_bB
  have hcard_ge :
      T + 1 ≤ eggsB.card :=
    lmms41_player1CaseReport_envyFree_player1_egg_card_ge_succ
      hTle hBalloc hBef
  have hcard_lt : eggsA.card < eggsB.card := by
    exact Nat.lt_of_succ_le hcard_ge
  have hstrict :=
    lmms41TrueReport_player1_insert_a_strict_mono_egg_card
      heggsA heggsB hcard_lt
  simpa [hA1, hB1] using hstrict

end

end Theorem41
end LMMS04FairDivision
