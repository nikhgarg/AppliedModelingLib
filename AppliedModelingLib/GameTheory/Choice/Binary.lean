import AppliedModelingLib.GameTheory.Choice.Equilibrium
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace AppliedModelingLib

/-!
# Binary Choice Best Responses

Reusable two-action best-response predicates and contradiction lemmas.

## Main declarations

- `NoProfitableBinaryChoiceDeviation`
- `NoProfitableUnchosenDeviation`
- `not_all_choose_of_noProfitableBinaryChoiceDeviation_exists_other_better`
- `not_no_choose_of_noProfitableBinaryChoiceDeviation_exists_choose_better`
- `exists_chosen_and_unchosen_of_noProfitableBinaryChoiceDeviation_crosses`
- `choice_rule_iff_threshold_of_noProfitableBinaryChoiceDeviation_tiebreak`
- `binaryChoiceEquilibriumData`
- `noProfitableUnchosenDeviation_of_binaryChoiceEquilibrium`
- `noProfitableBinaryChoiceDeviation_of_binaryChoiceEquilibrium`
- `noProfitableUnchosenDeviation_of_choiceEquilibrium_payoff_projection`
- `noProfitableBinaryChoiceDeviation_of_choiceEquilibrium_payoff_projection`
- `not_noProfitableBinaryChoiceDeviation_of_chosen_other_better`
- `not_noProfitableBinaryChoiceDeviation_of_unchosen_choose_better`
- `false_of_noProfitableUnchosenDeviation_exists_profitable_unchosen`
- `false_of_lowerCutoff_noProfitableUnchosenDeviation_exists_below_cutoff_profitable`
-/

/--
Two-sided binary best-response condition: choosing weakly dominates not
choosing at chosen values, and not choosing weakly dominates choosing at
unchosen values.
-/
def NoProfitableBinaryChoiceDeviation
    {α : Type*} (chooses : α → Prop)
    (choosePayoff otherPayoff : α → ℝ) : Prop :=
  (∀ a, chooses a → otherPayoff a ≤ choosePayoff a) ∧
    (∀ a, ¬ chooses a → choosePayoff a ≤ otherPayoff a)

/--
One-sided binary best-response condition: unchosen values do not profit by
switching to the chosen action.
-/
def NoProfitableUnchosenDeviation
    {α : Type*} (chooses : α → Prop)
    (choosePayoff otherPayoff : α → ℝ) : Prop :=
  ∀ a, ¬ chooses a → choosePayoff a ≤ otherPayoff a

/--
Exact payoff-threshold choice rules are two-sided binary best responses:
choose exactly when the chosen-action payoff weakly dominates the outside
option.
-/
theorem noProfitableBinaryChoiceDeviation_of_choice_iff_payoff_le
    {α : Type*} {chooses : α → Prop}
    {choosePayoff otherPayoff : α → ℝ}
    (hchoice :
      ∀ a, chooses a ↔ otherPayoff a ≤ choosePayoff a) :
    NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff := by
  constructor
  · intro a hchoose
    exact (hchoice a).1 hchoose
  · intro a hnot
    have hnot_le : ¬ otherPayoff a ≤ choosePayoff a := by
      intro hle
      exact hnot ((hchoice a).2 hle)
    exact le_of_lt (lt_of_not_ge hnot_le)

/--
Binary choice subgame as a static choice-equilibrium problem.  The `true`
action receives `choosePayoff`; the `false` action receives `otherPayoff`.
-/
def binaryChoiceEquilibriumData
    {α : Type*} (chooses : α → Prop) [DecidablePred chooses]
    (choosePayoff otherPayoff : α → ℝ) :
    ChoiceEquilibriumData α Bool where
  actionFeasible := fun _ _ => True
  chosenAction := fun a => if chooses a then true else false
  payoff := fun a choose =>
    if choose = true then choosePayoff a else otherPayoff a
  consistency := True

/-- The two-sided binary condition includes the one-sided unchosen condition. -/
theorem noProfitableUnchosenDeviation_of_noProfitableBinaryChoiceDeviation
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff) :
    NoProfitableUnchosenDeviation chooses choosePayoff otherPayoff :=
  hbest.2

/--
A binary static choice equilibrium supplies the one-sided no-profitable
unchosen-deviation condition.
-/
theorem noProfitableUnchosenDeviation_of_binaryChoiceEquilibrium
    {α : Type*} {chooses : α → Prop} [DecidablePred chooses]
    {choosePayoff otherPayoff : α → ℝ}
    (hEq :
      IsChoiceEquilibrium
        (binaryChoiceEquilibriumData chooses choosePayoff otherPayoff)) :
    NoProfitableUnchosenDeviation chooses choosePayoff otherPayoff := by
  intro a hnotChoose
  have hbest :=
    isChoiceEquilibrium_best_response hEq a true trivial
  dsimp [binaryChoiceEquilibriumData] at hbest
  simpa [hnotChoose] using hbest

/--
A binary static choice equilibrium supplies the two-sided binary
best-response condition.
-/
theorem noProfitableBinaryChoiceDeviation_of_binaryChoiceEquilibrium
    {α : Type*} {chooses : α → Prop} [DecidablePred chooses]
    {choosePayoff otherPayoff : α → ℝ}
    (hEq :
      IsChoiceEquilibrium
        (binaryChoiceEquilibriumData chooses choosePayoff otherPayoff)) :
    NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff := by
  constructor
  · intro a hchoose
    have hbest :=
      isChoiceEquilibrium_best_response hEq a false trivial
    dsimp [binaryChoiceEquilibriumData] at hbest
    simpa [hchoose] using hbest
  · exact noProfitableUnchosenDeviation_of_binaryChoiceEquilibrium hEq

/--
Project a static choice equilibrium onto a one-sided binary no-deviation
condition by naming the profitable deviation action and rewriting the chosen
payoff at unchosen indices.
-/
theorem noProfitableUnchosenDeviation_of_choiceEquilibrium_payoff_projection
    {α Info Action : Type*} {chooses : α → Prop}
    {choosePayoff otherPayoff : α → ℝ}
    {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E)
    (infoOf : α → Info) (chooseAction : α → Action)
    (hchooseFeasible :
      ∀ a, E.actionFeasible (infoOf a) (chooseAction a))
    (hchoosePayoff :
      ∀ a, E.payoff (infoOf a) (chooseAction a) = choosePayoff a)
    (hchosenOtherPayoff :
      ∀ a, ¬ chooses a →
        E.payoff (infoOf a) (E.chosenAction (infoOf a)) =
          otherPayoff a) :
    NoProfitableUnchosenDeviation chooses choosePayoff otherPayoff := by
  intro a hnotChoose
  have hbest :=
    isChoiceEquilibrium_best_response hEq
      (infoOf a) (chooseAction a) (hchooseFeasible a)
  rw [hchoosePayoff a, hchosenOtherPayoff a hnotChoose] at hbest
  exact hbest

/--
Project a static choice equilibrium onto a two-sided binary best-response
condition by naming the two deviation actions and rewriting the chosen payoff
in the chosen and unchosen cases.
-/
theorem noProfitableBinaryChoiceDeviation_of_choiceEquilibrium_payoff_projection
    {α Info Action : Type*} {chooses : α → Prop}
    {choosePayoff otherPayoff : α → ℝ}
    {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E)
    (infoOf : α → Info)
    (chooseAction otherAction : α → Action)
    (hchooseFeasible :
      ∀ a, E.actionFeasible (infoOf a) (chooseAction a))
    (hotherFeasible :
      ∀ a, E.actionFeasible (infoOf a) (otherAction a))
    (hchoosePayoff :
      ∀ a, E.payoff (infoOf a) (chooseAction a) = choosePayoff a)
    (hotherPayoff :
      ∀ a, E.payoff (infoOf a) (otherAction a) = otherPayoff a)
    (hchosenChoosePayoff :
      ∀ a, chooses a →
        E.payoff (infoOf a) (E.chosenAction (infoOf a)) =
          choosePayoff a)
    (hchosenOtherPayoff :
      ∀ a, ¬ chooses a →
        E.payoff (infoOf a) (E.chosenAction (infoOf a)) =
          otherPayoff a) :
    NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff := by
  constructor
  · intro a hchoose
    have hbest :=
      isChoiceEquilibrium_best_response hEq
        (infoOf a) (otherAction a) (hotherFeasible a)
    rw [hotherPayoff a, hchosenChoosePayoff a hchoose] at hbest
    exact hbest
  · exact
      noProfitableUnchosenDeviation_of_choiceEquilibrium_payoff_projection
        hEq infoOf chooseAction hchooseFeasible hchoosePayoff
        hchosenOtherPayoff

/--
If the outside option strictly beats choosing somewhere, then a two-sided best
response cannot choose everywhere.
-/
theorem not_all_choose_of_noProfitableBinaryChoiceDeviation_exists_other_better
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff)
    (hbetter : ∃ a, choosePayoff a < otherPayoff a) :
    ¬ ∀ a, chooses a := by
  rintro hall
  rcases hbetter with ⟨a, hvalue⟩
  have hbest_value := hbest.1 a (hall a)
  linarith

/--
If choosing strictly beats the outside option somewhere, then a two-sided best
response cannot choose the outside option everywhere.
-/
theorem not_no_choose_of_noProfitableBinaryChoiceDeviation_exists_choose_better
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff)
    (hbetter : ∃ a, otherPayoff a < choosePayoff a) :
    ¬ ∀ a, ¬ chooses a := by
  rintro hnone
  rcases hbetter with ⟨a, hvalue⟩
  have hbest_value := hbest.2 a (hnone a)
  linarith

/--
If choosing is strictly better somewhere and the outside option is strictly
better somewhere, then a two-sided binary best response chooses at least one
value and leaves at least one value unchosen.
-/
theorem exists_chosen_and_unchosen_of_noProfitableBinaryChoiceDeviation_crosses
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff)
    (hchoose_better : ∃ a, otherPayoff a < choosePayoff a)
    (hother_better : ∃ a, choosePayoff a < otherPayoff a) :
    (∃ a, chooses a) ∧ ∃ a, ¬ chooses a := by
  have hnotAll : ¬ ∀ a, chooses a :=
    not_all_choose_of_noProfitableBinaryChoiceDeviation_exists_other_better
      hbest hother_better
  have hnotNone : ¬ ∀ a, ¬ chooses a :=
    not_no_choose_of_noProfitableBinaryChoiceDeviation_exists_choose_better
      hbest hchoose_better
  constructor
  · by_contra hnoExists
    exact hnotNone (fun a hchoose => hnoExists ⟨a, hchoose⟩)
  · by_contra hnoExists
    exact hnotAll (fun a => by
      by_contra hnotChoose
      exact hnoExists ⟨a, hnotChoose⟩)

/--
If two-sided binary best response is paired with a payoff-threshold
characterization and the rule chooses at indifference, the choice rule is
exactly the threshold predicate.
-/
theorem choice_rule_iff_threshold_of_noProfitableBinaryChoiceDeviation_tiebreak
    {α : Type*} {chooses threshold : α → Prop}
    {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff)
    (hthreshold :
      ∀ a, otherPayoff a ≤ choosePayoff a ↔ threshold a)
    (htie : ∀ a, choosePayoff a = otherPayoff a → chooses a) :
    ∀ a, chooses a ↔ threshold a := by
  intro a
  constructor
  · intro hchoose
    exact (hthreshold a).1 (hbest.1 a hchoose)
  · intro hthreshold_a
    by_cases hchoose : chooses a
    · exact hchoose
    · have hchoose_le_other := hbest.2 a hchoose
      have hother_le_choose := (hthreshold a).2 hthreshold_a
      exact htie a (le_antisymm hchoose_le_other hother_le_choose)

/--
If a chosen value strictly prefers the outside option, then the two-sided
binary best-response condition fails.
-/
theorem not_noProfitableBinaryChoiceDeviation_of_chosen_other_better
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    {a : α} (hchosen : chooses a) (hbetter : choosePayoff a < otherPayoff a) :
    ¬ NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff := by
  intro hbest
  have hbest_value := hbest.1 a hchosen
  linarith

/--
If an unchosen value strictly prefers choosing, then the two-sided binary
best-response condition fails.
-/
theorem not_noProfitableBinaryChoiceDeviation_of_unchosen_choose_better
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    {a : α} (hnotChoose : ¬ chooses a)
    (hbetter : otherPayoff a < choosePayoff a) :
    ¬ NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff := by
  intro hbest
  have hbest_value := hbest.2 a hnotChoose
  linarith

/--
One-sided no-deviation contradiction: if an unchosen value strictly prefers
choosing, the "unchosen values do not profit by choosing" condition is false.
-/
theorem false_of_noProfitableUnchosenDeviation_exists_profitable_unchosen
    {α : Type*} {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hnoDeviation :
      NoProfitableUnchosenDeviation chooses choosePayoff otherPayoff)
    (hprofitable : ∃ a, ¬ chooses a ∧ otherPayoff a < choosePayoff a) :
    False := by
  rcases hprofitable with ⟨a, hnotChoose, hbetter⟩
  have hnoProfit := hnoDeviation a hnotChoose
  linarith

/--
Lower-cutoff version of the one-sided contradiction: if some value strictly
below the cutoff strictly prefers choosing, then a lower-cutoff rule cannot
satisfy no profitable deviation among unchosen values.
-/
theorem false_of_lowerCutoff_noProfitableUnchosenDeviation_exists_below_cutoff_profitable
    {chooses : ℝ → Prop} {choosePayoff otherPayoff : ℝ → ℝ} {cutoff : ℝ}
    (hcutoff : ∀ value : ℝ, chooses value ↔ cutoff ≤ value)
    (hnoDeviation :
      NoProfitableUnchosenDeviation chooses choosePayoff otherPayoff)
    (hprofitable :
      ∃ value, value < cutoff ∧ otherPayoff value < choosePayoff value) :
    False := by
  apply false_of_noProfitableUnchosenDeviation_exists_profitable_unchosen
    hnoDeviation
  rcases hprofitable with ⟨value, hbelow, hbetter⟩
  refine ⟨value, ?_, hbetter⟩
  intro hchoose
  exact not_le_of_gt hbelow ((hcutoff value).1 hchoose)

end AppliedModelingLib
