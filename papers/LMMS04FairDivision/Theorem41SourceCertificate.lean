import LMMS04FairDivision.Theorem41CaseOne
import LMMS04FairDivision.Theorem41CaseTwo

open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem41

noncomputable section

/-!
# Source Certificate Assembly for LMMS Theorem 4.1

This module combines the two finite case splits with the reusable direct
mechanism API.  The remaining source-model existence work is isolated in the
two shifted-profile envy-free witness hypotheses.
-/

/-- Existence of an exact envy-free allocation for the truthful source profile. -/
def LMMS41TruthfulExists : Prop :=
  ∃ A : Allocation LMMS41Agent LMMS41Item,
    IsAllocationOf A lmms41Goods ∧ ReportEnvyFree lmms41TrueReport A

/-- Existence of the shifted envy-free witness needed in player 1's case. -/
def LMMS41Player1ShiftedExistsFor (T : ℕ) : Prop :=
  ∃ B : Allocation LMMS41Agent LMMS41Item,
    IsAllocationOf B lmms41Goods ∧
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player1
          (lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40))) B

/-- Existence of the shifted envy-free witness needed in player 2's case. -/
def LMMS41Player2ShiftedExistsFor (U : ℕ) : Prop :=
  ∃ B : Allocation LMMS41Agent LMMS41Item,
    IsAllocationOf B lmms41Goods ∧
      ReportEnvyFree
        (Function.update lmms41TrueReport LMMS41Agent.player2
          (lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40))) B

/--
Assemble the finite source counterexample certificate from the two case
witness-existence facts.  The case split follows the paper: if the truthful
output gives player 1 at most four eggs, player 1 deviates; otherwise player 2
deviates.
-/
def lmms41_sourceCounterexampleCertificate_of_shifted_exists
    (M : LMMS41Mechanism)
    (halloc : ReturnsAllocationOf M lmms41Goods)
    (hef : ReturnsEnvyFreeWheneverExists M lmms41Goods)
    (htrue_exists : LMMS41TruthfulExists)
    (hcase1_exists :
      ∀ T : ℕ, T ≤ 4 → LMMS41Player1ShiftedExistsFor T)
    (hcase2_exists :
      ∀ U : ℕ, U ≤ 3 → LMMS41Player2ShiftedExistsFor U) :
    LMMS41SourceCounterexampleCertificate M := by
  let A := M.allocation lmms41TrueReport
  have hAalloc : IsAllocationOf A lmms41Goods := halloc lmms41TrueReport
  have hAef : ReportEnvyFree lmms41TrueReport A :=
    hef lmms41TrueReport htrue_exists
  let T := (lmms41EggRemainder A LMMS41Agent.player1).card
  by_cases hlow : T ≤ 4
  · refine
      { agent := LMMS41Agent.player1
        deviationReport := lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40)
        improves := ?_ }
    let reports :=
      Function.update lmms41TrueReport LMMS41Agent.player1
        (lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40))
    let B := M.allocation reports
    have hBalloc : IsAllocationOf B lmms41Goods := halloc reports
    have hBef : ReportEnvyFree reports B :=
      hef reports (hcase1_exists T hlow)
    have hbetter :
        lmms41TrueReport LMMS41Agent.player1 (A LMMS41Agent.player1) <
          lmms41TrueReport LMMS41Agent.player1 (B LMMS41Agent.player1) :=
      lmms41_case_one_player1_deviation_better
        hAalloc hAef hlow hBalloc hBef
    simpa [DirectFairDivisionMechanism.utility, A, B, reports, T]
      using hbetter
  · refine
      { agent := LMMS41Agent.player2
        deviationReport :=
          lmms41Player2ShiftedReport
            ((((lmms41EggRemainder A LMMS41Agent.player2).card : ℝ) - 1) / 40)
        improves := ?_ }
    let U := (lmms41EggRemainder A LMMS41Agent.player2).card
    have hUle : U ≤ 3 :=
      lmms41_trueReport_envyFree_player2_egg_card_le_three_of_not_player1_le_four
        hAalloc hlow
    let reports :=
      Function.update lmms41TrueReport LMMS41Agent.player2
        (lmms41Player2ShiftedReport (((U : ℝ) - 1) / 40))
    let B := M.allocation reports
    have hBalloc : IsAllocationOf B lmms41Goods := halloc reports
    have hBef : ReportEnvyFree reports B :=
      hef reports (hcase2_exists U hUle)
    have hbetter :
        lmms41TrueReport LMMS41Agent.player2 (A LMMS41Agent.player2) <
          lmms41TrueReport LMMS41Agent.player2 (B LMMS41Agent.player2) :=
      lmms41_case_two_player2_deviation_better
        hAalloc hAef hUle hBalloc hBef
    simpa [DirectFairDivisionMechanism.utility, A, B, reports, U]
      using hbetter

theorem lmms41_not_truthful_of_shifted_exists
    (M : LMMS41Mechanism)
    (halloc : ReturnsAllocationOf M lmms41Goods)
    (hef : ReturnsEnvyFreeWheneverExists M lmms41Goods)
    (htrue_exists : LMMS41TruthfulExists)
    (hcase1_exists :
      ∀ T : ℕ, T ≤ 4 → LMMS41Player1ShiftedExistsFor T)
    (hcase2_exists :
      ∀ U : ℕ, U ≤ 3 → LMMS41Player2ShiftedExistsFor U) :
    ¬ M.Truthful := by
  exact
    lmms41_not_truthful_of_sourceCounterexampleCertificate M
      (lmms41_sourceCounterexampleCertificate_of_shifted_exists
        M halloc hef htrue_exists hcase1_exists hcase2_exists)

end

end Theorem41
end LMMS04FairDivision
