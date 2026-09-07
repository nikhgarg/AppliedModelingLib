import LMMS04FairDivision.Theorem41

open scoped BigOperators
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem41

noncomputable section

/-!
# Symmetric Player-2 Arithmetic for LMMS Theorem 4.1

This sidecar module mirrors the player-1 shifted-report arithmetic from
`Theorem41.lean` for the symmetric player-2 case.
-/

@[simp] theorem lmms41Player2ShiftedWeight_player2_a (delta : ℝ) :
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2 LMMS41Item.a =
      (7 : ℝ) / 20 + delta := by
  simp [lmms41Player2ShiftedWeight]

@[simp] theorem lmms41Player2ShiftedWeight_player2_b (delta : ℝ) :
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2 LMMS41Item.b =
      (9 : ℝ) / 20 - delta := by
  simp [lmms41Player2ShiftedWeight]

theorem lmms41Player2ShiftedWeight_player2_of_not_a_not_b
    (delta : ℝ) {item : LMMS41Item}
    (ha : item ≠ LMMS41Item.a) (hb : item ≠ LMMS41Item.b) :
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2 item =
      (1 : ℝ) / 40 := by
  simp [lmms41Player2ShiftedWeight, ha, hb]

@[simp] theorem lmms41Player2ShiftedWeight_player2_egg
    (delta : ℝ) (idx : Fin 8) :
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2
        (LMMS41Item.egg idx) =
      (1 : ℝ) / 40 := by
  exact lmms41Player2ShiftedWeight_player2_of_not_a_not_b delta
    (lmms41_item_egg_ne_a idx) (lmms41_item_egg_ne_b idx)

theorem lmms41Player2ShiftedReport_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player2ShiftedReport delta eggs = (eggs.card : ℝ) / 40 := by
  rw [lmms41Player2ShiftedReport, lmms41AdditiveReport]
  have hsum :
      eggs.sum
          (fun item =>
            lmms41Player2ShiftedWeight delta LMMS41Agent.player2 item) =
        eggs.sum (fun _item => (1 : ℝ) / 40) := by
    apply Finset.sum_congr rfl
    intro item hitem
    have ha : item ≠ LMMS41Item.a := by
      intro h
      exact heggs.1 (by simpa [h] using hitem)
    have hb : item ≠ LMMS41Item.b := by
      intro h
      exact heggs.2 (by simpa [h] using hitem)
    exact lmms41Player2ShiftedWeight_player2_of_not_a_not_b delta ha hb
  rw [hsum]
  simp
  ring

theorem lmms41Player2ShiftedReport_insert_a_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player2ShiftedReport delta (insert LMMS41Item.a eggs) =
      (7 : ℝ) / 20 + delta + (eggs.card : ℝ) / 40 := by
  rw [lmms41Player2ShiftedReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.1]
  change
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2 LMMS41Item.a +
        lmms41Player2ShiftedReport delta eggs =
      (7 : ℝ) / 20 + delta + (eggs.card : ℝ) / 40
  rw [lmms41Player2ShiftedReport_eggOnly delta eggs heggs]
  simp

theorem lmms41Player2ShiftedReport_insert_b_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player2ShiftedReport delta (insert LMMS41Item.b eggs) =
      (9 : ℝ) / 20 - delta + (eggs.card : ℝ) / 40 := by
  rw [lmms41Player2ShiftedReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.2]
  change
    lmms41Player2ShiftedWeight delta LMMS41Agent.player2 LMMS41Item.b +
        lmms41Player2ShiftedReport delta eggs =
      (9 : ℝ) / 20 - delta + (eggs.card : ℝ) / 40
  rw [lmms41Player2ShiftedReport_eggOnly delta eggs heggs]
  simp

/--
If player 2 keeps good `b`, one additional egg gives strictly higher true
utility. This is the symmetric arithmetic core of the second LMMS Theorem 4.1
case split.
-/
theorem lmms41TrueReport_player2_insert_b_strict_mono_egg_card
    {oldEggs newEggs : Bundle LMMS41Item}
    (hold : lmms41EggOnlyBundle oldEggs)
    (hnew : lmms41EggOnlyBundle newEggs)
    (hcard : oldEggs.card < newEggs.card) :
    lmms41TrueReport LMMS41Agent.player2 (insert LMMS41Item.b oldEggs) <
      lmms41TrueReport LMMS41Agent.player2 (insert LMMS41Item.b newEggs) := by
  rw [lmms41TrueReport_player2_insert_b_eggOnly oldEggs hold,
    lmms41TrueReport_player2_insert_b_eggOnly newEggs hnew]
  have hcardReal : (oldEggs.card : ℝ) < newEggs.card := by
    exact_mod_cast hcard
  linarith

/--
With the symmetric second-case shift `delta = (T - 1) / 40`, player 2's
declared value for `b` plus `T + 1` eggs is exactly one half.
-/
theorem lmms41Player2ShiftedReport_insert_b_eq_half_of_card_eq_succ
    (T : ℕ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs)
    (hcard : eggs.card = T + 1) :
    lmms41Player2ShiftedReport (((T : ℝ) - 1) / 40)
        (insert LMMS41Item.b eggs) =
      (1 : ℝ) / 2 := by
  rw [lmms41Player2ShiftedReport_insert_b_eggOnly
    (((T : ℝ) - 1) / 40) eggs heggs]
  have hcardReal : (eggs.card : ℝ) = (T : ℝ) + 1 := by
    exact_mod_cast hcard
  rw [hcardReal]
  ring

end

end Theorem41
end LMMS04FairDivision
