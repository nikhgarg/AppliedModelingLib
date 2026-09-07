import LMMS04FairDivision.Theorem41
import LMMS04FairDivision.Theorem41Symmetric

open scoped BigOperators
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem41

noncomputable section

/-!
# Player-2 Case of LMMS Theorem 4.1

This sidecar module keeps the symmetric case-two work disjoint from the shared
Theorem 4.1 files.  The first compiled endpoints isolate the core arithmetic:
under player 2's shifted report, envy-freeness plus ownership of `b` forces
player 2 to gain at least one egg relative to the truthful allocation's
player-2 egg count.
-/

/-- Player 2's shifted value for both named goods plus an egg-only bundle. -/
theorem lmms41Player2ShiftedReport_insert_a_insert_b_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player2ShiftedReport delta
        (insert LMMS41Item.a (insert LMMS41Item.b eggs)) =
      (4 : ℝ) / 5 + (eggs.card : ℝ) / 40 := by
  rw [lmms41Player2ShiftedReport, lmms41AdditiveReport]
  have ha_not_mem : LMMS41Item.a ∉ insert LMMS41Item.b eggs := by
    simp [heggs.1, Ne.symm lmms41_item_b_ne_a]
  rw [Finset.sum_insert ha_not_mem]
  have hb_not_mem : LMMS41Item.b ∉ eggs := heggs.2
  rw [Finset.sum_insert hb_not_mem]
  change
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2 LMMS41Item.a +
        (lmms41Player2ShiftedWeight delta LMMS41Agent.player2 LMMS41Item.b +
          lmms41Player2ShiftedReport delta eggs) =
      (4 : ℝ) / 5 + (eggs.card : ℝ) / 40
  rw [lmms41Player2ShiftedReport_eggOnly delta eggs heggs]
  simp
  ring

/-- Player 2's shifted value for an egg-only bundle is at most one fifth. -/
theorem lmms41Player2ShiftedReport_eggOnly_le_fifth
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player2ShiftedReport delta eggs ≤ (1 : ℝ) / 5 := by
  rw [lmms41Player2ShiftedReport_eggOnly delta eggs heggs]
  have hcard : (eggs.card : ℝ) ≤ 8 := by
    exact_mod_cast lmms41EggOnly_card_le_eight heggs
  linarith

/--
Under the second-case shifted profile with `U ≤ 3`, any exact report-envy-free
allocation must assign named good `b` to player 2 and named good `a` to
player 1.
-/
theorem lmms41_caseTwo_shiftedEF_namedGoods
    {B : Allocation LMMS41Agent LMMS41Item} {U : ℕ}
    (halloc : IsAllocationOf B lmms41Goods)
    (hUle : U ≤ 3)
    (hef :
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player2
          (lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40))) B) :
    LMMS41Item.a ∈ B LMMS41Agent.player1 ∧
      LMMS41Item.b ∈ B LMMS41Agent.player2 ∧
      LMMS41Item.b ∉ B LMMS41Agent.player1 ∧
      LMMS41Item.a ∉ B LMMS41Agent.player2 := by
  by_cases hb2 : LMMS41Item.b ∈ B LMMS41Agent.player2
  · have hnot_b1 : LMMS41Item.b ∉ B LMMS41Agent.player1 :=
      lmms41_not_mem_player1_of_mem_player2_of_alloc halloc hb2
    by_cases ha2 : LMMS41Item.a ∈ B LMMS41Agent.player2
    · have hnot_a1 : LMMS41Item.a ∉ B LMMS41Agent.player1 :=
        lmms41_not_mem_player1_of_mem_player2_of_alloc halloc ha2
      have hp1_eggs : lmms41EggOnlyBundle (B LMMS41Agent.player1) :=
        ⟨hnot_a1, hnot_b1⟩
      have hown :
          lmms41TrueReport LMMS41Agent.player1 (B LMMS41Agent.player1) ≤
            (1 : ℝ) / 5 :=
        lmms41TrueReport_player1_eggOnly_le_fifth _ hp1_eggs
      have hother :
          (4 : ℝ) / 5 ≤
            lmms41TrueReport LMMS41Agent.player1 (B LMMS41Agent.player2) :=
        lmms41TrueReport_player1_pair_ab_le_of_mem ha2 hb2
      have hp1_noenvy := hef LMMS41Agent.player1 LMMS41Agent.player2
      simp [Function.update, LMMS41Agent.player1, LMMS41Agent.player2] at hp1_noenvy
      have hp1_noenvy' :
          lmms41TrueReport LMMS41Agent.player1 (B LMMS41Agent.player2) ≤
            lmms41TrueReport LMMS41Agent.player1 (B LMMS41Agent.player1) := by
        simpa [LMMS41Agent.player1, LMMS41Agent.player2] using hp1_noenvy
      exact False.elim (by linarith)
    · have ha1 : LMMS41Item.a ∈ B LMMS41Agent.player1 :=
        lmms41_mem_player1_of_not_mem_player2_of_alloc halloc ha2
      exact ⟨ha1, hb2, hnot_b1, ha2⟩
  · have hb1 : LMMS41Item.b ∈ B LMMS41Agent.player1 :=
      lmms41_mem_player1_of_not_mem_player2_of_alloc halloc hb2
    by_cases ha2 : LMMS41Item.a ∈ B LMMS41Agent.player2
    · let eggs1 := lmms41EggRemainder B LMMS41Agent.player1
      let eggs2 := lmms41EggRemainder B LMMS41Agent.player2
      have hnot_a1 : LMMS41Item.a ∉ B LMMS41Agent.player1 :=
        lmms41_not_mem_player1_of_mem_player2_of_alloc halloc ha2
      have hnot_b2 : LMMS41Item.b ∉ B LMMS41Agent.player2 := hb2
      have heggs1 : lmms41EggOnlyBundle eggs1 :=
        lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player1
      have heggs2 : lmms41EggOnlyBundle eggs2 :=
        lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player2
      have hB1 : insert LMMS41Item.b eggs1 = B LMMS41Agent.player1 :=
        lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb1 hnot_a1
      have hB2 : insert LMMS41Item.a eggs2 = B LMMS41Agent.player2 :=
        lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b ha2 hnot_b2
      have hsumNat : eggs1.card + eggs2.card = 8 :=
        lmms41_eggRemainder_card_sum halloc
      have hsumReal : (eggs1.card : ℝ) + (eggs2.card : ℝ) = 8 := by
        exact_mod_cast hsumNat
      have hp1_noenvy := hef LMMS41Agent.player1 LMMS41Agent.player2
      rw [← hB2, ← hB1] at hp1_noenvy
      simp [Function.update, LMMS41Agent.player1, LMMS41Agent.player2] at hp1_noenvy
      change
        lmms41TrueReport LMMS41Agent.player1 (insert LMMS41Item.a eggs2) ≤
          lmms41TrueReport LMMS41Agent.player1 (insert LMMS41Item.b eggs1) at hp1_noenvy
      rw [lmms41TrueReport_player1_insert_a_eggOnly eggs2 heggs2,
        lmms41TrueReport_player1_insert_b_eggOnly eggs1 heggs1] at hp1_noenvy
      have hp2_noenvy := hef LMMS41Agent.player2 LMMS41Agent.player1
      rw [← hB1, ← hB2] at hp2_noenvy
      simp [Function.update, LMMS41Agent.player2] at hp2_noenvy
      change
        lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)
            (insert LMMS41Item.b eggs1) ≤
          lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)
            (insert LMMS41Item.a eggs2) at hp2_noenvy
      rw [
        lmms41Player2ShiftedReport_insert_b_eggOnly (((U : ℝ) - 1) / 40)
          eggs1 heggs1,
        lmms41Player2ShiftedReport_insert_a_eggOnly (((U : ℝ) - 1) / 40)
          eggs2 heggs2] at hp2_noenvy
      have hUleReal : (U : ℝ) ≤ 3 := by
        exact_mod_cast hUle
      exact False.elim (by linarith)
    · have ha1 : LMMS41Item.a ∈ B LMMS41Agent.player1 :=
        lmms41_mem_player1_of_not_mem_player2_of_alloc halloc ha2
      let eggs1 := lmms41EggRemainder B LMMS41Agent.player1
      have hnot_a2 : LMMS41Item.a ∉ B LMMS41Agent.player2 := ha2
      have heggs1 : lmms41EggOnlyBundle eggs1 :=
        lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player1
      have hB1 :
          insert LMMS41Item.a (insert LMMS41Item.b eggs1) =
            B LMMS41Agent.player1 := by
        exact
          lmms41_insert_a_insert_b_eggRemainder_eq_of_mem_a_mem_b
            ha1 hb1
      have hp2_eggs : lmms41EggOnlyBundle (B LMMS41Agent.player2) :=
        ⟨hnot_a2, hb2⟩
      have hown :
          lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)
              (B LMMS41Agent.player2) ≤
            (1 : ℝ) / 5 :=
        lmms41Player2ShiftedReport_eggOnly_le_fifth _ _ hp2_eggs
      have hother_eq :
          lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)
              (B LMMS41Agent.player1) =
            (4 : ℝ) / 5 + (eggs1.card : ℝ) / 40 := by
        rw [← hB1]
        exact
          lmms41Player2ShiftedReport_insert_a_insert_b_eggOnly
            (((U : ℝ) - 1) / 40) eggs1 heggs1
      have hp2_noenvy := hef LMMS41Agent.player2 LMMS41Agent.player1
      simp [Function.update, LMMS41Agent.player1, LMMS41Agent.player2] at hp2_noenvy
      change
        lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)
            (B LMMS41Agent.player1) ≤
          lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40)
            (B LMMS41Agent.player2) at hp2_noenvy
      rw [hother_eq] at hp2_noenvy
      have hcard_nonneg : (0 : ℝ) ≤ (eggs1.card : ℝ) := by
        exact_mod_cast Nat.zero_le eggs1.card
      exact False.elim (by linarith)

/--
In the second case, if the deviating envy-free allocation gives player 2 the
named good `b` and player 1 the named good `a`, player 2's no-envy inequality
under the shifted report forces player 2 to receive strictly more than `U`
eggs.
-/
theorem lmms41_caseTwo_player2_egg_card_gt_of_shiftedEF_namedGoods
    {B : Allocation LMMS41Agent LMMS41Item} {U : ℕ}
    (halloc : IsAllocationOf B lmms41Goods)
    (ha1 : LMMS41Item.a ∈ B LMMS41Agent.player1)
    (hb2 : LMMS41Item.b ∈ B LMMS41Agent.player2)
    (hnot_b1 : LMMS41Item.b ∉ B LMMS41Agent.player1)
    (hnot_a2 : LMMS41Item.a ∉ B LMMS41Agent.player2)
    (hef :
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player2
          (lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40))) B) :
    U < (lmms41EggRemainder B LMMS41Agent.player2).card := by
  let eggs1 := lmms41EggRemainder B LMMS41Agent.player1
  let eggs2 := lmms41EggRemainder B LMMS41Agent.player2
  have heggs1 : lmms41EggOnlyBundle eggs1 :=
    lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player1
  have heggs2 : lmms41EggOnlyBundle eggs2 :=
    lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player2
  have hB1 : insert LMMS41Item.a eggs1 = B LMMS41Agent.player1 :=
    lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b ha1 hnot_b1
  have hB2 : insert LMMS41Item.b eggs2 = B LMMS41Agent.player2 :=
    lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb2 hnot_a2
  have hsumNat : eggs1.card + eggs2.card = 8 :=
    lmms41_eggRemainder_card_sum halloc
  have hsumReal : (eggs1.card : ℝ) + (eggs2.card : ℝ) = 8 := by
    exact_mod_cast hsumNat
  have hp2_noenvy := hef LMMS41Agent.player2 LMMS41Agent.player1
  rw [← hB1, ← hB2] at hp2_noenvy
  simp [Function.update] at hp2_noenvy
  rw [
    lmms41Player2ShiftedReport_insert_a_eggOnly (((U : ℝ) - 1) / 40)
      eggs1 heggs1,
    lmms41Player2ShiftedReport_insert_b_eggOnly (((U : ℝ) - 1) / 40)
      eggs2 heggs2] at hp2_noenvy
  have hsuccReal : (U : ℝ) + 1 ≤ eggs2.card := by
    linarith
  have hsuccNat : U + 1 ≤ eggs2.card := by
    exact_mod_cast hsuccReal
  exact Nat.lt_of_succ_le hsuccNat

/--
Same egg-gain conclusion with the named-good facts reduced to the player-2
bundle statement `b ∈ B₂` and `a ∉ B₂`.
-/
theorem lmms41_caseTwo_player2_egg_card_gt_of_shiftedEF_player2_gets_b
    {B : Allocation LMMS41Agent LMMS41Item} {U : ℕ}
    (halloc : IsAllocationOf B lmms41Goods)
    (hb2 : LMMS41Item.b ∈ B LMMS41Agent.player2)
    (hnot_a2 : LMMS41Item.a ∉ B LMMS41Agent.player2)
    (hef :
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player2
          (lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40))) B) :
    U < (lmms41EggRemainder B LMMS41Agent.player2).card := by
  have ha1 : LMMS41Item.a ∈ B LMMS41Agent.player1 :=
    lmms41_mem_player1_of_not_mem_player2_of_alloc halloc hnot_a2
  have hnot_b1 : LMMS41Item.b ∉ B LMMS41Agent.player1 :=
    lmms41_not_mem_player1_of_mem_player2_of_alloc halloc hb2
  exact
    lmms41_caseTwo_player2_egg_card_gt_of_shiftedEF_namedGoods
      halloc ha1 hb2 hnot_b1 hnot_a2 hef

/--
If the shifted envy-free allocation gives player 2 `b` and not `a`, then in
case two player 2's true utility is strictly larger than in the exact truthful
envy-free allocation.
-/
theorem lmms41_caseTwo_player2_trueReport_strict_of_shiftedEF_player2_gets_b
    {A B : Allocation LMMS41Agent LMMS41Item}
    (hAalloc : IsAllocationOf A lmms41Goods)
    (hAef : ReportEnvyFree lmms41TrueReport A)
    (hBalloc : IsAllocationOf B lmms41Goods)
    (hb2 : LMMS41Item.b ∈ B LMMS41Agent.player2)
    (hnot_a2 : LMMS41Item.a ∉ B LMMS41Agent.player2)
    (hefB :
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player2
          (lmms41Player2ShiftedReport
            ((((lmms41EggRemainder A LMMS41Agent.player2).card : ℝ) - 1) /
              40))) B) :
    lmms41TrueReport LMMS41Agent.player2 (A LMMS41Agent.player2) <
      lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player2) := by
  let oldEggs := lmms41EggRemainder A LMMS41Agent.player2
  let newEggs := lmms41EggRemainder B LMMS41Agent.player2
  obtain ⟨_ha1A, hb2A, _hnot_b1A, hnot_a2A⟩ :=
    lmms41_trueReport_envyFree_namedGoods hAalloc hAef
  have hA2 : insert LMMS41Item.b oldEggs = A LMMS41Agent.player2 :=
    lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb2A hnot_a2A
  have hB2 : insert LMMS41Item.b newEggs = B LMMS41Agent.player2 :=
    lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb2 hnot_a2
  have hold : lmms41EggOnlyBundle oldEggs :=
    lmms41EggOnlyBundle_eggRemainder A LMMS41Agent.player2
  have hnew : lmms41EggOnlyBundle newEggs :=
    lmms41EggOnlyBundle_eggRemainder B LMMS41Agent.player2
  have hcard : oldEggs.card < newEggs.card :=
    lmms41_caseTwo_player2_egg_card_gt_of_shiftedEF_player2_gets_b
      (B := B) (U := oldEggs.card) hBalloc hb2 hnot_a2 hefB
  rw [← hA2, ← hB2]
  exact
    lmms41TrueReport_player2_insert_b_strict_mono_egg_card
      hold hnew hcard

/--
Full second-case improvement theorem: if player 2's truthful egg count is at
most three, her shifted report makes every exact shifted-profile envy-free
allocation strictly better for her in true utility.
-/
theorem lmms41_case_two_player2_deviation_better
    {A B : Allocation LMMS41Agent LMMS41Item}
    (hAalloc : IsAllocationOf A lmms41Goods)
    (hAef : ReportEnvyFree lmms41TrueReport A)
    (hUle : (lmms41EggRemainder A LMMS41Agent.player2).card ≤ 3)
    (hBalloc : IsAllocationOf B lmms41Goods)
    (hBef :
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player2
          (lmms41Player2ShiftedReport
            ((((lmms41EggRemainder A LMMS41Agent.player2).card : ℝ) - 1) /
              40)))
        B) :
    lmms41TrueReport LMMS41Agent.player2 (A LMMS41Agent.player2) <
      lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player2) := by
  let U := (lmms41EggRemainder A LMMS41Agent.player2).card
  obtain ⟨_ha1, hb2, _hnot_b1, hnot_a2⟩ :=
    lmms41_caseTwo_shiftedEF_namedGoods
      (B := B) (U := U) hBalloc hUle hBef
  exact
    lmms41_caseTwo_player2_trueReport_strict_of_shiftedEF_player2_gets_b
      hAalloc hAef hBalloc hb2 hnot_a2 hBef

end

end Theorem41
end LMMS04FairDivision
