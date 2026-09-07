import AppliedModelingLib.SocialChoice.FairDivision.Mechanisms
import Mathlib.Tactic

open scoped BigOperators
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem41

noncomputable section

/-!
Finite support for the source counterexample in LMMS Theorem 4.1.

The source proof uses two players, two named goods, and many identical "eggs"
as an almost divisible good.  This module fixes a small eight-egg version and
packages the mechanism-design endpoint that a concrete profitable deviation
refutes dominant-strategy truthfulness.
-/

/-- The two players in the LMMS Theorem 4.1 counterexample. -/
abbrev LMMS41Agent := Fin 2

namespace LMMS41Agent

/-- Player 1 in the source proof. -/
def player1 : LMMS41Agent := 0

/-- Player 2 in the source proof. -/
def player2 : LMMS41Agent := 1

end LMMS41Agent

/-- The two named goods plus eight egg goods. -/
abbrev LMMS41Item := Fin 10

namespace LMMS41Item

/-- The source proof's named good `a`. -/
def a : LMMS41Item := 0

/-- The source proof's named good `b`. -/
def b : LMMS41Item := 1

/-- The eight egg goods, indexed separately from `a` and `b`. -/
def egg (idx : Fin 8) : LMMS41Item :=
  ⟨idx.val + 2, by
    have h := Nat.add_lt_add_right idx.isLt 2
    simpa using h⟩

end LMMS41Item

@[simp] theorem lmms41_player2_ne_player1 :
    LMMS41Agent.player2 ≠ LMMS41Agent.player1 := by
  decide

@[simp] theorem lmms41_item_b_ne_a :
    LMMS41Item.b ≠ LMMS41Item.a := by
  decide

@[simp] theorem lmms41_item_egg_ne_a (idx : Fin 8) :
    LMMS41Item.egg idx ≠ LMMS41Item.a := by
  intro h
  have hval := congrArg Fin.val h
  simp [LMMS41Item.egg, LMMS41Item.a] at hval

@[simp] theorem lmms41_item_egg_ne_b (idx : Fin 8) :
    LMMS41Item.egg idx ≠ LMMS41Item.b := by
  intro h
  have hval := congrArg Fin.val h
  simp [LMMS41Item.egg, LMMS41Item.b] at hval

abbrev LMMS41Report :=
  FairDivisionReport LMMS41Agent LMMS41Item

abbrev LMMS41Mechanism :=
  DirectFairDivisionMechanism LMMS41Agent LMMS41Item

/-- The full finite goods set for the eight-egg source model. -/
def lmms41Goods : Finset LMMS41Item :=
  Finset.univ

/-- The eight egg goods as a finite subset of the source goods. -/
def lmms41EggItems : Finset LMMS41Item :=
  Finset.univ.filter fun item => item ≠ LMMS41Item.a ∧ item ≠ LMMS41Item.b

@[simp] theorem lmms41_mem_eggItems_iff {item : LMMS41Item} :
    item ∈ lmms41EggItems ↔ item ≠ LMMS41Item.a ∧ item ≠ LMMS41Item.b := by
  simp [lmms41EggItems]

@[simp] theorem lmms41EggItems_card :
    lmms41EggItems.card = 8 := by
  decide

theorem lmms41_agent_eq_player1_or_player2 (agent : LMMS41Agent) :
    agent = LMMS41Agent.player1 ∨ agent = LMMS41Agent.player2 := by
  fin_cases agent <;> simp [LMMS41Agent.player1, LMMS41Agent.player2]

theorem lmms41_exactAllocation_existsUnique_owner
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) (item : LMMS41Item) :
    ∃! agent : LMMS41Agent, item ∈ A agent := by
  exact halloc.2 item (by simp [lmms41Goods])

theorem lmms41_mem_player2_of_not_mem_player1_of_alloc
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) {item : LMMS41Item}
    (hnot : item ∉ A LMMS41Agent.player1) :
    item ∈ A LMMS41Agent.player2 := by
  have hgoods : item ∈ lmms41Goods := by
    simp [lmms41Goods]
  obtain ⟨owner, howner⟩ :=
    isAllocationOf_exists_owner (A := A) (goods := lmms41Goods)
      halloc hgoods
  rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
  · exact False.elim (hnot howner)
  · exact howner

theorem lmms41_mem_player1_of_not_mem_player2_of_alloc
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) {item : LMMS41Item}
    (hnot : item ∉ A LMMS41Agent.player2) :
    item ∈ A LMMS41Agent.player1 := by
  have hgoods : item ∈ lmms41Goods := by
    simp [lmms41Goods]
  obtain ⟨owner, howner⟩ :=
    isAllocationOf_exists_owner (A := A) (goods := lmms41Goods)
      halloc hgoods
  rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
  · exact howner
  · exact False.elim (hnot howner)

theorem lmms41_not_mem_player2_of_mem_player1_of_alloc
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) {item : LMMS41Item}
    (hmem : item ∈ A LMMS41Agent.player1) :
    item ∉ A LMMS41Agent.player2 := by
  have hgoods : item ∈ lmms41Goods := by
    simp [lmms41Goods]
  exact
    isAllocationOf_not_mem_of_mem_ne
      (A := A) (goods := lmms41Goods) halloc hgoods hmem
      lmms41_player2_ne_player1

theorem lmms41_not_mem_player1_of_mem_player2_of_alloc
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) {item : LMMS41Item}
    (hmem : item ∈ A LMMS41Agent.player2) :
    item ∉ A LMMS41Agent.player1 := by
  have hgoods : item ∈ lmms41Goods := by
    simp [lmms41Goods]
  exact
    isAllocationOf_not_mem_of_mem_ne
      (A := A) (goods := lmms41Goods) halloc hgoods hmem
      (Ne.symm lmms41_player2_ne_player1)

theorem lmms41_mem_player2_iff_not_mem_player1_of_alloc
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) {item : LMMS41Item} :
    item ∈ A LMMS41Agent.player2 ↔
      item ∉ A LMMS41Agent.player1 := by
  constructor
  · intro hmem
    exact lmms41_not_mem_player1_of_mem_player2_of_alloc halloc hmem
  · intro hnot
    exact lmms41_mem_player2_of_not_mem_player1_of_alloc halloc hnot

theorem lmms41_mem_player1_iff_not_mem_player2_of_alloc
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) {item : LMMS41Item} :
    item ∈ A LMMS41Agent.player1 ↔
      item ∉ A LMMS41Agent.player2 := by
  constructor
  · intro hmem
    exact lmms41_not_mem_player2_of_mem_player1_of_alloc halloc hmem
  · intro hnot
    exact lmms41_mem_player1_of_not_mem_player2_of_alloc halloc hnot

/-- The egg-only remainder of an agent's bundle after removing named goods. -/
def lmms41EggRemainder
    (A : Allocation LMMS41Agent LMMS41Item) (agent : LMMS41Agent) :
    Bundle LMMS41Item :=
  ((A agent).erase LMMS41Item.a).erase LMMS41Item.b

/-- Additive extension from singleton item weights to bundle reports. -/
def lmms41AdditiveReport
    (w : LMMS41Agent → LMMS41Item → ℝ) : LMMS41Report :=
  fun agent bundle => bundle.sum (fun item => w agent item)

/-- The truthful item weights from the paper's Theorem 4.1 example, with eight eggs. -/
def lmms41TrueWeight : LMMS41Agent → LMMS41Item → ℝ :=
  fun agent item =>
    if agent = LMMS41Agent.player1 then
      if item = LMMS41Item.a then (9 : ℝ) / 20
      else if item = LMMS41Item.b then (7 : ℝ) / 20
      else (1 : ℝ) / 40
    else
      if item = LMMS41Item.a then (7 : ℝ) / 20
      else if item = LMMS41Item.b then (9 : ℝ) / 20
      else (1 : ℝ) / 40

/-- Truthful reports for the eight-egg source model. -/
noncomputable def lmms41TrueReport : LMMS41Report :=
  lmms41AdditiveReport lmms41TrueWeight

/--
Player 1's shifted report family from the first source-proof case.  The future
source-model proof should instantiate `delta` from the egg count in the
truthful allocation.
-/
def lmms41Player1ShiftedWeight (delta : ℝ) :
    LMMS41Agent → LMMS41Item → ℝ :=
  fun agent item =>
    if agent = LMMS41Agent.player1 then
      if item = LMMS41Item.a then (9 : ℝ) / 20 - delta
      else if item = LMMS41Item.b then (7 : ℝ) / 20 + delta
      else (1 : ℝ) / 40
    else
      lmms41TrueWeight LMMS41Agent.player2 item

/-- Player 1's additive shifted bundle report. -/
noncomputable def lmms41Player1ShiftedReport (delta : ℝ) :
    Bundle LMMS41Item → ℝ :=
  fun bundle =>
    lmms41AdditiveReport (lmms41Player1ShiftedWeight delta)
      LMMS41Agent.player1 bundle

/--
Player 2's symmetric shifted report family from the second source-proof case.
The exact `delta` is a future source-model arithmetic obligation.
-/
def lmms41Player2ShiftedWeight (delta : ℝ) :
    LMMS41Agent → LMMS41Item → ℝ :=
  fun agent item =>
    if agent = LMMS41Agent.player2 then
      if item = LMMS41Item.a then (7 : ℝ) / 20 + delta
      else if item = LMMS41Item.b then (9 : ℝ) / 20 - delta
      else (1 : ℝ) / 40
    else
      lmms41TrueWeight LMMS41Agent.player1 item

/-- Player 2's additive shifted bundle report. -/
noncomputable def lmms41Player2ShiftedReport (delta : ℝ) :
    Bundle LMMS41Item → ℝ :=
  fun bundle =>
    lmms41AdditiveReport (lmms41Player2ShiftedWeight delta)
      LMMS41Agent.player2 bundle

/-- Player 1's first-case deviating bundle report, parameterized by an egg count. -/
noncomputable def lmms41Player1DeviationReport (T : ℕ) :
    Bundle LMMS41Item → ℝ :=
  lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40)

/-- Full reported profile after player 1 makes the first-case deviation. -/
noncomputable def lmms41Player1DeviationProfile (T : ℕ) : LMMS41Report :=
  Function.update lmms41TrueReport LMMS41Agent.player1
    (lmms41Player1DeviationReport T)

/-- Player 2's second-case deviating bundle report, parameterized by an egg count. -/
noncomputable def lmms41Player2DeviationReport (T : ℕ) :
    Bundle LMMS41Item → ℝ :=
  lmms41Player2ShiftedReport (((T : ℝ) - 1) / 40)

/-- Full reported profile after player 2 makes the second-case deviation. -/
noncomputable def lmms41Player2DeviationProfile (T : ℕ) : LMMS41Report :=
  Function.update lmms41TrueReport LMMS41Agent.player2
    (lmms41Player2DeviationReport T)

@[simp] theorem lmms41Player1DeviationProfile_player1 (T : ℕ) :
    lmms41Player1DeviationProfile T LMMS41Agent.player1 =
      lmms41Player1DeviationReport T := by
  simp [lmms41Player1DeviationProfile]

@[simp] theorem lmms41Player1DeviationProfile_player2 (T : ℕ) :
    lmms41Player1DeviationProfile T LMMS41Agent.player2 =
      lmms41TrueReport LMMS41Agent.player2 := by
  simp [lmms41Player1DeviationProfile]

@[simp] theorem lmms41Player2DeviationProfile_player1 (T : ℕ) :
    lmms41Player2DeviationProfile T LMMS41Agent.player1 =
      lmms41TrueReport LMMS41Agent.player1 := by
  simp [lmms41Player2DeviationProfile, Ne.symm lmms41_player2_ne_player1]

@[simp] theorem lmms41Player2DeviationProfile_player2 (T : ℕ) :
    lmms41Player2DeviationProfile T LMMS41Agent.player2 =
      lmms41Player2DeviationReport T := by
  simp [lmms41Player2DeviationProfile]

@[simp] theorem lmms41TrueReport_player1_a :
    lmms41TrueReport LMMS41Agent.player1 {LMMS41Item.a} = (9 : ℝ) / 20 := by
  simp [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight]

@[simp] theorem lmms41TrueReport_player1_b :
    lmms41TrueReport LMMS41Agent.player1 {LMMS41Item.b} = (7 : ℝ) / 20 := by
  simp [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight]

@[simp] theorem lmms41TrueReport_player2_a :
    lmms41TrueReport LMMS41Agent.player2 {LMMS41Item.a} = (7 : ℝ) / 20 := by
  simp [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight]

@[simp] theorem lmms41TrueReport_player2_b :
    lmms41TrueReport LMMS41Agent.player2 {LMMS41Item.b} = (9 : ℝ) / 20 := by
  simp [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight]

@[simp] theorem lmms41TrueReport_player1_egg (idx : Fin 8) :
    lmms41TrueReport LMMS41Agent.player1 {LMMS41Item.egg idx} = (1 : ℝ) / 40 := by
  simp [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight]

@[simp] theorem lmms41TrueReport_player2_egg (idx : Fin 8) :
    lmms41TrueReport LMMS41Agent.player2 {LMMS41Item.egg idx} = (1 : ℝ) / 40 := by
  simp [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight]

@[simp] theorem lmms41TrueReport_player1_pair_ab :
    lmms41TrueReport LMMS41Agent.player1
        ({LMMS41Item.a, LMMS41Item.b} : Bundle LMMS41Item) =
      (4 : ℝ) / 5 := by
  norm_num [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight,
    LMMS41Item.a, LMMS41Item.b]

@[simp] theorem lmms41TrueReport_player2_pair_ab :
    lmms41TrueReport LMMS41Agent.player2
        ({LMMS41Item.a, LMMS41Item.b} : Bundle LMMS41Item) =
      (4 : ℝ) / 5 := by
  norm_num [lmms41TrueReport, lmms41AdditiveReport, lmms41TrueWeight,
    LMMS41Item.a, LMMS41Item.b]

/-! ## Additive arithmetic for the eight-egg source model -/

/-- Bundles containing only egg goods, i.e. neither named good `a` nor `b`. -/
def lmms41EggOnlyBundle (bundle : Bundle LMMS41Item) : Prop :=
  LMMS41Item.a ∉ bundle ∧ LMMS41Item.b ∉ bundle

theorem lmms41EggOnlyBundle_eggRemainder
    (A : Allocation LMMS41Agent LMMS41Item) (agent : LMMS41Agent) :
    lmms41EggOnlyBundle (lmms41EggRemainder A agent) := by
  simp [lmms41EggRemainder, lmms41EggOnlyBundle]

theorem lmms41_mem_eggRemainder_iff
    (A : Allocation LMMS41Agent LMMS41Item) (agent : LMMS41Agent)
    {item : LMMS41Item} :
    item ∈ lmms41EggRemainder A agent ↔
      item ∈ A agent ∧ item ≠ LMMS41Item.a ∧ item ≠ LMMS41Item.b := by
  constructor
  · intro hmem
    simp [lmms41EggRemainder] at hmem
    exact ⟨hmem.2.2, hmem.2.1, hmem.1⟩
  · intro hmem
    simp [lmms41EggRemainder, hmem.1, hmem.2.1, hmem.2.2]

theorem lmms41_eggRemainder_disjoint
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) :
    Disjoint (lmms41EggRemainder A LMMS41Agent.player1)
      (lmms41EggRemainder A LMMS41Agent.player2) := by
  refine Finset.disjoint_left.mpr ?_
  intro item hitem1 hitem2
  have hmem1 : item ∈ A LMMS41Agent.player1 :=
    ((lmms41_mem_eggRemainder_iff A LMMS41Agent.player1).mp hitem1).1
  have hmem2 : item ∈ A LMMS41Agent.player2 :=
    ((lmms41_mem_eggRemainder_iff A LMMS41Agent.player2).mp hitem2).1
  exact (lmms41_not_mem_player2_of_mem_player1_of_alloc halloc hmem1) hmem2

theorem lmms41_eggRemainder_union_eq_eggItems
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) :
    lmms41EggRemainder A LMMS41Agent.player1 ∪
        lmms41EggRemainder A LMMS41Agent.player2 =
      lmms41EggItems := by
  ext item
  constructor
  · intro hmem
    rcases Finset.mem_union.mp hmem with hitem | hitem
    · exact (lmms41_mem_eggItems_iff).mpr
        ⟨((lmms41_mem_eggRemainder_iff A LMMS41Agent.player1).mp hitem).2.1,
          ((lmms41_mem_eggRemainder_iff A LMMS41Agent.player1).mp hitem).2.2⟩
    · exact (lmms41_mem_eggItems_iff).mpr
        ⟨((lmms41_mem_eggRemainder_iff A LMMS41Agent.player2).mp hitem).2.1,
          ((lmms41_mem_eggRemainder_iff A LMMS41Agent.player2).mp hitem).2.2⟩
  · intro hitem
    have ha : item ≠ LMMS41Item.a := (lmms41_mem_eggItems_iff.mp hitem).1
    have hb : item ≠ LMMS41Item.b := (lmms41_mem_eggItems_iff.mp hitem).2
    obtain ⟨owner, howner⟩ :=
      isAllocationOf_exists_owner (A := A) (goods := lmms41Goods)
        halloc (by simp [lmms41Goods])
    rcases lmms41_agent_eq_player1_or_player2 owner with rfl | rfl
    · exact Finset.mem_union_left _ <|
        (lmms41_mem_eggRemainder_iff A LMMS41Agent.player1).mpr
          ⟨howner, ha, hb⟩
    · exact Finset.mem_union_right _ <|
        (lmms41_mem_eggRemainder_iff A LMMS41Agent.player2).mpr
          ⟨howner, ha, hb⟩

theorem lmms41_eggRemainder_card_sum
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods) :
    (lmms41EggRemainder A LMMS41Agent.player1).card +
        (lmms41EggRemainder A LMMS41Agent.player2).card =
      8 := by
  have hcard :=
    Finset.card_union_of_disjoint (lmms41_eggRemainder_disjoint halloc)
      (s := lmms41EggRemainder A LMMS41Agent.player1)
      (t := lmms41EggRemainder A LMMS41Agent.player2)
  rw [lmms41_eggRemainder_union_eq_eggItems halloc, lmms41EggItems_card] at hcard
  exact hcard.symm

theorem lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b
    {A : Allocation LMMS41Agent LMMS41Item} {agent : LMMS41Agent}
    (ha : LMMS41Item.a ∈ A agent) (hb : LMMS41Item.b ∉ A agent) :
    insert LMMS41Item.a (lmms41EggRemainder A agent) = A agent := by
  ext item
  by_cases hia : item = LMMS41Item.a
  · subst hia
    simp [ha]
  · by_cases hib : item = LMMS41Item.b
    · subst hib
      simp [lmms41EggRemainder, hb]
    · simp [lmms41EggRemainder, hia, hib]

theorem lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a
    {A : Allocation LMMS41Agent LMMS41Item} {agent : LMMS41Agent}
    (hb : LMMS41Item.b ∈ A agent) (ha : LMMS41Item.a ∉ A agent) :
    insert LMMS41Item.b (lmms41EggRemainder A agent) = A agent := by
  ext item
  by_cases hib : item = LMMS41Item.b
  · subst hib
    simp [hb]
  · by_cases hia : item = LMMS41Item.a
    · subst hia
      have hab : LMMS41Item.a ≠ LMMS41Item.b :=
        Ne.symm lmms41_item_b_ne_a
      simp [lmms41EggRemainder, ha, hab]
    · simp [lmms41EggRemainder, hia, hib]

theorem lmms41_insert_a_insert_b_eggRemainder_eq_of_mem_a_mem_b
    {A : Allocation LMMS41Agent LMMS41Item} {agent : LMMS41Agent}
    (ha : LMMS41Item.a ∈ A agent) (hb : LMMS41Item.b ∈ A agent) :
    insert LMMS41Item.a (insert LMMS41Item.b (lmms41EggRemainder A agent)) =
      A agent := by
  ext item
  by_cases hia : item = LMMS41Item.a
  · subst hia
    simp [ha]
  · by_cases hib : item = LMMS41Item.b
    · subst hib
      simp [lmms41EggRemainder, hb]
    · simp [lmms41EggRemainder, hia, hib]

@[simp] theorem lmms41TrueWeight_player1_a :
    lmms41TrueWeight LMMS41Agent.player1 LMMS41Item.a = (9 : ℝ) / 20 := by
  simp [lmms41TrueWeight]

@[simp] theorem lmms41TrueWeight_player1_b :
    lmms41TrueWeight LMMS41Agent.player1 LMMS41Item.b = (7 : ℝ) / 20 := by
  simp [lmms41TrueWeight]

@[simp] theorem lmms41TrueWeight_player2_a :
    lmms41TrueWeight LMMS41Agent.player2 LMMS41Item.a = (7 : ℝ) / 20 := by
  simp [lmms41TrueWeight]

@[simp] theorem lmms41TrueWeight_player2_b :
    lmms41TrueWeight LMMS41Agent.player2 LMMS41Item.b = (9 : ℝ) / 20 := by
  simp [lmms41TrueWeight]

theorem lmms41TrueWeight_player1_of_not_a_not_b
    {item : LMMS41Item}
    (ha : item ≠ LMMS41Item.a) (hb : item ≠ LMMS41Item.b) :
    lmms41TrueWeight LMMS41Agent.player1 item = (1 : ℝ) / 40 := by
  simp [lmms41TrueWeight, ha, hb]

theorem lmms41TrueWeight_player2_of_not_a_not_b
    {item : LMMS41Item}
    (ha : item ≠ LMMS41Item.a) (hb : item ≠ LMMS41Item.b) :
    lmms41TrueWeight LMMS41Agent.player2 item = (1 : ℝ) / 40 := by
  simp [lmms41TrueWeight, ha, hb]

theorem lmms41TrueWeight_nonneg (agent : LMMS41Agent) (item : LMMS41Item) :
    0 ≤ lmms41TrueWeight agent item := by
  fin_cases agent <;> fin_cases item <;>
    norm_num [lmms41TrueWeight, LMMS41Agent.player1, LMMS41Agent.player2,
      LMMS41Item.a, LMMS41Item.b]

theorem lmms41TrueReport_mono
    (agent : LMMS41Agent) {S T : Bundle LMMS41Item}
    (hsub : S ⊆ T) :
    lmms41TrueReport agent S ≤ lmms41TrueReport agent T := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by intro item _ _; exact lmms41TrueWeight_nonneg agent item)

theorem lmms41TrueReport_player1_pair_ab_le_of_mem
    {bundle : Bundle LMMS41Item}
    (ha : LMMS41Item.a ∈ bundle) (hb : LMMS41Item.b ∈ bundle) :
    (4 : ℝ) / 5 ≤ lmms41TrueReport LMMS41Agent.player1 bundle := by
  have hsub :
      ({LMMS41Item.a, LMMS41Item.b} : Bundle LMMS41Item) ⊆ bundle := by
    intro item hitem
    simp at hitem
    rcases hitem with rfl | rfl
    · exact ha
    · exact hb
  simpa using lmms41TrueReport_mono LMMS41Agent.player1 hsub

theorem lmms41TrueReport_player2_pair_ab_le_of_mem
    {bundle : Bundle LMMS41Item}
    (ha : LMMS41Item.a ∈ bundle) (hb : LMMS41Item.b ∈ bundle) :
    (4 : ℝ) / 5 ≤ lmms41TrueReport LMMS41Agent.player2 bundle := by
  have hsub :
      ({LMMS41Item.a, LMMS41Item.b} : Bundle LMMS41Item) ⊆ bundle := by
    intro item hitem
    simp at hitem
    rcases hitem with rfl | rfl
    · exact ha
    · exact hb
  simpa using lmms41TrueReport_mono LMMS41Agent.player2 hsub

theorem lmms41EggOnly_subset_eggItems
    {eggs : Bundle LMMS41Item}
    (heggs : lmms41EggOnlyBundle eggs) :
    eggs ⊆ lmms41EggItems := by
  intro item hitem
  exact
    (lmms41_mem_eggItems_iff).mpr
      (by
        constructor
        · intro h
          exact heggs.1 (by simpa [h] using hitem)
        · intro h
          exact heggs.2 (by simpa [h] using hitem))

theorem lmms41EggOnly_card_le_eight
    {eggs : Bundle LMMS41Item}
    (heggs : lmms41EggOnlyBundle eggs) :
    eggs.card ≤ 8 := by
  have hcard := Finset.card_le_card (lmms41EggOnly_subset_eggItems heggs)
  simpa using hcard

theorem lmms41TrueReport_player1_eggOnly
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player1 eggs = (eggs.card : ℝ) / 40 := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  have hsum :
      eggs.sum (fun item => lmms41TrueWeight LMMS41Agent.player1 item) =
        eggs.sum (fun _item => (1 : ℝ) / 40) := by
    apply Finset.sum_congr rfl
    intro item hitem
    have ha : item ≠ LMMS41Item.a := by
      intro h
      exact heggs.1 (by simpa [h] using hitem)
    have hb : item ≠ LMMS41Item.b := by
      intro h
      exact heggs.2 (by simpa [h] using hitem)
    exact lmms41TrueWeight_player1_of_not_a_not_b ha hb
  rw [hsum]
  simp
  ring

theorem lmms41TrueReport_player2_eggOnly
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player2 eggs = (eggs.card : ℝ) / 40 := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  have hsum :
      eggs.sum (fun item => lmms41TrueWeight LMMS41Agent.player2 item) =
        eggs.sum (fun _item => (1 : ℝ) / 40) := by
    apply Finset.sum_congr rfl
    intro item hitem
    have ha : item ≠ LMMS41Item.a := by
      intro h
      exact heggs.1 (by simpa [h] using hitem)
    have hb : item ≠ LMMS41Item.b := by
      intro h
      exact heggs.2 (by simpa [h] using hitem)
    exact lmms41TrueWeight_player2_of_not_a_not_b ha hb
  rw [hsum]
  simp
  ring

theorem lmms41TrueReport_player1_eggOnly_le_fifth
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player1 eggs ≤ (1 : ℝ) / 5 := by
  rw [lmms41TrueReport_player1_eggOnly eggs heggs]
  have hcard : (eggs.card : ℝ) ≤ 8 := by
    exact_mod_cast lmms41EggOnly_card_le_eight heggs
  linarith

theorem lmms41TrueReport_player2_eggOnly_le_fifth
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player2 eggs ≤ (1 : ℝ) / 5 := by
  rw [lmms41TrueReport_player2_eggOnly eggs heggs]
  have hcard : (eggs.card : ℝ) ≤ 8 := by
    exact_mod_cast lmms41EggOnly_card_le_eight heggs
  linarith

theorem lmms41_not_reportEnvyFree_true_of_player2_has_a_b
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods)
    (ha : LMMS41Item.a ∈ A LMMS41Agent.player2)
    (hb : LMMS41Item.b ∈ A LMMS41Agent.player2) :
    ¬ ReportEnvyFree lmms41TrueReport A := by
  intro hef
  have hnot_a : LMMS41Item.a ∉ A LMMS41Agent.player1 :=
    lmms41_not_mem_player1_of_mem_player2_of_alloc halloc ha
  have hnot_b : LMMS41Item.b ∉ A LMMS41Agent.player1 :=
    lmms41_not_mem_player1_of_mem_player2_of_alloc halloc hb
  have hp1_eggs : lmms41EggOnlyBundle (A LMMS41Agent.player1) :=
    ⟨hnot_a, hnot_b⟩
  have hown :
      lmms41TrueReport LMMS41Agent.player1 (A LMMS41Agent.player1) ≤
        (1 : ℝ) / 5 :=
    lmms41TrueReport_player1_eggOnly_le_fifth _ hp1_eggs
  have hother :
      (4 : ℝ) / 5 ≤
        lmms41TrueReport LMMS41Agent.player1 (A LMMS41Agent.player2) :=
    lmms41TrueReport_player1_pair_ab_le_of_mem ha hb
  have hnoenvy :=
    hef LMMS41Agent.player1 LMMS41Agent.player2
  linarith

theorem lmms41_not_reportEnvyFree_true_of_player1_has_a_b
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods)
    (ha : LMMS41Item.a ∈ A LMMS41Agent.player1)
    (hb : LMMS41Item.b ∈ A LMMS41Agent.player1) :
    ¬ ReportEnvyFree lmms41TrueReport A := by
  intro hef
  have hnot_a : LMMS41Item.a ∉ A LMMS41Agent.player2 :=
    lmms41_not_mem_player2_of_mem_player1_of_alloc halloc ha
  have hnot_b : LMMS41Item.b ∉ A LMMS41Agent.player2 :=
    lmms41_not_mem_player2_of_mem_player1_of_alloc halloc hb
  have hp2_eggs : lmms41EggOnlyBundle (A LMMS41Agent.player2) :=
    ⟨hnot_a, hnot_b⟩
  have hown :
      lmms41TrueReport LMMS41Agent.player2 (A LMMS41Agent.player2) ≤
        (1 : ℝ) / 5 :=
    lmms41TrueReport_player2_eggOnly_le_fifth _ hp2_eggs
  have hother :
      (4 : ℝ) / 5 ≤
        lmms41TrueReport LMMS41Agent.player2 (A LMMS41Agent.player1) :=
    lmms41TrueReport_player2_pair_ab_le_of_mem ha hb
  have hnoenvy :=
    hef LMMS41Agent.player2 LMMS41Agent.player1
  linarith

theorem lmms41TrueReport_player1_insert_a_eggOnly
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player1 (insert LMMS41Item.a eggs) =
      (9 : ℝ) / 20 + (eggs.card : ℝ) / 40 := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.1]
  change
    lmms41TrueWeight LMMS41Agent.player1 LMMS41Item.a +
        lmms41TrueReport LMMS41Agent.player1 eggs =
      (9 : ℝ) / 20 + (eggs.card : ℝ) / 40
  rw [lmms41TrueReport_player1_eggOnly eggs heggs]
  simp

theorem lmms41TrueReport_player1_insert_b_eggOnly
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player1 (insert LMMS41Item.b eggs) =
      (7 : ℝ) / 20 + (eggs.card : ℝ) / 40 := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.2]
  change
    lmms41TrueWeight LMMS41Agent.player1 LMMS41Item.b +
        lmms41TrueReport LMMS41Agent.player1 eggs =
      (7 : ℝ) / 20 + (eggs.card : ℝ) / 40
  rw [lmms41TrueReport_player1_eggOnly eggs heggs]
  simp

theorem lmms41TrueReport_player2_insert_a_eggOnly
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player2 (insert LMMS41Item.a eggs) =
      (7 : ℝ) / 20 + (eggs.card : ℝ) / 40 := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.1]
  change
    lmms41TrueWeight LMMS41Agent.player2 LMMS41Item.a +
        lmms41TrueReport LMMS41Agent.player2 eggs =
      (7 : ℝ) / 20 + (eggs.card : ℝ) / 40
  rw [lmms41TrueReport_player2_eggOnly eggs heggs]
  simp

theorem lmms41TrueReport_player2_insert_b_eggOnly
    (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41TrueReport LMMS41Agent.player2 (insert LMMS41Item.b eggs) =
      (9 : ℝ) / 20 + (eggs.card : ℝ) / 40 := by
  rw [lmms41TrueReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.2]
  change
    lmms41TrueWeight LMMS41Agent.player2 LMMS41Item.b +
        lmms41TrueReport LMMS41Agent.player2 eggs =
      (9 : ℝ) / 20 + (eggs.card : ℝ) / 40
  rw [lmms41TrueReport_player2_eggOnly eggs heggs]
  simp

theorem lmms41_not_reportEnvyFree_true_of_swapped_named_goods
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods)
    (ha2 : LMMS41Item.a ∈ A LMMS41Agent.player2)
    (hb1 : LMMS41Item.b ∈ A LMMS41Agent.player1) :
    ¬ ReportEnvyFree lmms41TrueReport A := by
  intro hef
  let eggs1 := lmms41EggRemainder A LMMS41Agent.player1
  let eggs2 := lmms41EggRemainder A LMMS41Agent.player2
  have hnot_a1 : LMMS41Item.a ∉ A LMMS41Agent.player1 :=
    lmms41_not_mem_player1_of_mem_player2_of_alloc halloc ha2
  have hnot_b2 : LMMS41Item.b ∉ A LMMS41Agent.player2 :=
    lmms41_not_mem_player2_of_mem_player1_of_alloc halloc hb1
  have heggs1 : lmms41EggOnlyBundle eggs1 :=
    lmms41EggOnlyBundle_eggRemainder A LMMS41Agent.player1
  have heggs2 : lmms41EggOnlyBundle eggs2 :=
    lmms41EggOnlyBundle_eggRemainder A LMMS41Agent.player2
  have hA1 :
      insert LMMS41Item.b eggs1 = A LMMS41Agent.player1 :=
    lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb1 hnot_a1
  have hA2 :
      insert LMMS41Item.a eggs2 = A LMMS41Agent.player2 :=
    lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b ha2 hnot_b2
  have hp1_noenvy := hef LMMS41Agent.player1 LMMS41Agent.player2
  rw [← hA2, ← hA1,
    lmms41TrueReport_player1_insert_a_eggOnly eggs2 heggs2,
    lmms41TrueReport_player1_insert_b_eggOnly eggs1 heggs1] at hp1_noenvy
  have hp2_noenvy := hef LMMS41Agent.player2 LMMS41Agent.player1
  rw [← hA1, ← hA2,
    lmms41TrueReport_player2_insert_b_eggOnly eggs1 heggs1,
    lmms41TrueReport_player2_insert_a_eggOnly eggs2 heggs2] at hp2_noenvy
  linarith

theorem lmms41_trueReport_envyFree_namedGoods
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods)
    (hef : ReportEnvyFree lmms41TrueReport A) :
    LMMS41Item.a ∈ A LMMS41Agent.player1 ∧
      LMMS41Item.b ∈ A LMMS41Agent.player2 ∧
      LMMS41Item.b ∉ A LMMS41Agent.player1 ∧
      LMMS41Item.a ∉ A LMMS41Agent.player2 := by
  by_cases ha1 : LMMS41Item.a ∈ A LMMS41Agent.player1
  · have hnot_a2 : LMMS41Item.a ∉ A LMMS41Agent.player2 :=
      lmms41_not_mem_player2_of_mem_player1_of_alloc halloc ha1
    by_cases hb1 : LMMS41Item.b ∈ A LMMS41Agent.player1
    · exact False.elim <|
        lmms41_not_reportEnvyFree_true_of_player1_has_a_b
          halloc ha1 hb1 hef
    · have hb2 : LMMS41Item.b ∈ A LMMS41Agent.player2 :=
        lmms41_mem_player2_of_not_mem_player1_of_alloc halloc hb1
      exact ⟨ha1, hb2, hb1, hnot_a2⟩
  · have ha2 : LMMS41Item.a ∈ A LMMS41Agent.player2 :=
      lmms41_mem_player2_of_not_mem_player1_of_alloc halloc ha1
    by_cases hb1 : LMMS41Item.b ∈ A LMMS41Agent.player1
    · exact False.elim <|
        lmms41_not_reportEnvyFree_true_of_swapped_named_goods
          halloc ha2 hb1 hef
    · have hb2 : LMMS41Item.b ∈ A LMMS41Agent.player2 :=
        lmms41_mem_player2_of_not_mem_player1_of_alloc halloc hb1
      exact False.elim <|
        lmms41_not_reportEnvyFree_true_of_player2_has_a_b
          halloc ha2 hb2 hef

theorem lmms41_trueReport_envyFree_player1_egg_card_bounds
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods)
    (hef : ReportEnvyFree lmms41TrueReport A) :
    2 ≤ (lmms41EggRemainder A LMMS41Agent.player1).card ∧
      (lmms41EggRemainder A LMMS41Agent.player1).card ≤ 6 := by
  let eggs1 := lmms41EggRemainder A LMMS41Agent.player1
  let eggs2 := lmms41EggRemainder A LMMS41Agent.player2
  obtain ⟨ha1, hb2, hnot_b1, hnot_a2⟩ :=
    lmms41_trueReport_envyFree_namedGoods halloc hef
  have heggs1 : lmms41EggOnlyBundle eggs1 :=
    lmms41EggOnlyBundle_eggRemainder A LMMS41Agent.player1
  have heggs2 : lmms41EggOnlyBundle eggs2 :=
    lmms41EggOnlyBundle_eggRemainder A LMMS41Agent.player2
  have hA1 :
      insert LMMS41Item.a eggs1 = A LMMS41Agent.player1 :=
    lmms41_insert_a_eggRemainder_eq_of_mem_a_not_mem_b ha1 hnot_b1
  have hA2 :
      insert LMMS41Item.b eggs2 = A LMMS41Agent.player2 :=
    lmms41_insert_b_eggRemainder_eq_of_mem_b_not_mem_a hb2 hnot_a2
  have hp1_noenvy := hef LMMS41Agent.player1 LMMS41Agent.player2
  rw [← hA2, ← hA1,
    lmms41TrueReport_player1_insert_b_eggOnly eggs2 heggs2,
    lmms41TrueReport_player1_insert_a_eggOnly eggs1 heggs1] at hp1_noenvy
  have hp2_noenvy := hef LMMS41Agent.player2 LMMS41Agent.player1
  rw [← hA1, ← hA2,
    lmms41TrueReport_player2_insert_a_eggOnly eggs1 heggs1,
    lmms41TrueReport_player2_insert_b_eggOnly eggs2 heggs2] at hp2_noenvy
  have hsumNat :
      eggs1.card + eggs2.card = 8 :=
    lmms41_eggRemainder_card_sum halloc
  have hsumReal :
      (eggs1.card : ℝ) + (eggs2.card : ℝ) = 8 := by
    exact_mod_cast hsumNat
  constructor
  · have hlowerReal : (2 : ℝ) ≤ eggs1.card := by
      linarith
    exact_mod_cast hlowerReal
  · have hupperReal : (eggs1.card : ℝ) ≤ 6 := by
      linarith
    exact_mod_cast hupperReal

theorem lmms41_trueReport_envyFree_player2_egg_card_le_three_of_not_player1_le_four
    {A : Allocation LMMS41Agent LMMS41Item}
    (halloc : IsAllocationOf A lmms41Goods)
    (hnot_low :
      ¬ (lmms41EggRemainder A LMMS41Agent.player1).card ≤ 4) :
    (lmms41EggRemainder A LMMS41Agent.player2).card ≤ 3 := by
  have hsum :
      (lmms41EggRemainder A LMMS41Agent.player1).card +
          (lmms41EggRemainder A LMMS41Agent.player2).card =
        8 :=
    lmms41_eggRemainder_card_sum halloc
  omega

@[simp] theorem lmms41Player1ShiftedWeight_player1_a (delta : ℝ) :
    lmms41Player1ShiftedWeight delta LMMS41Agent.player1 LMMS41Item.a =
      (9 : ℝ) / 20 - delta := by
  simp [lmms41Player1ShiftedWeight]

@[simp] theorem lmms41Player1ShiftedWeight_player1_b (delta : ℝ) :
    lmms41Player1ShiftedWeight delta LMMS41Agent.player1 LMMS41Item.b =
      (7 : ℝ) / 20 + delta := by
  simp [lmms41Player1ShiftedWeight]

theorem lmms41Player1ShiftedWeight_player1_of_not_a_not_b
    (delta : ℝ) {item : LMMS41Item}
    (ha : item ≠ LMMS41Item.a) (hb : item ≠ LMMS41Item.b) :
    lmms41Player1ShiftedWeight delta LMMS41Agent.player1 item =
      (1 : ℝ) / 40 := by
  simp [lmms41Player1ShiftedWeight, ha, hb]

theorem lmms41Player1ShiftedReport_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player1ShiftedReport delta eggs = (eggs.card : ℝ) / 40 := by
  rw [lmms41Player1ShiftedReport, lmms41AdditiveReport]
  have hsum :
      eggs.sum
          (fun item =>
            lmms41Player1ShiftedWeight delta LMMS41Agent.player1 item) =
        eggs.sum (fun _item => (1 : ℝ) / 40) := by
    apply Finset.sum_congr rfl
    intro item hitem
    have ha : item ≠ LMMS41Item.a := by
      intro h
      exact heggs.1 (by simpa [h] using hitem)
    have hb : item ≠ LMMS41Item.b := by
      intro h
      exact heggs.2 (by simpa [h] using hitem)
    exact lmms41Player1ShiftedWeight_player1_of_not_a_not_b delta ha hb
  rw [hsum]
  simp
  ring

theorem lmms41Player1ShiftedReport_insert_a_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player1ShiftedReport delta (insert LMMS41Item.a eggs) =
      (9 : ℝ) / 20 - delta + (eggs.card : ℝ) / 40 := by
  rw [lmms41Player1ShiftedReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.1]
  change
    lmms41Player1ShiftedWeight delta LMMS41Agent.player1 LMMS41Item.a +
        lmms41Player1ShiftedReport delta eggs =
      (9 : ℝ) / 20 - delta + (eggs.card : ℝ) / 40
  rw [lmms41Player1ShiftedReport_eggOnly delta eggs heggs]
  simp

theorem lmms41Player1ShiftedReport_insert_b_eggOnly
    (delta : ℝ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs) :
    lmms41Player1ShiftedReport delta (insert LMMS41Item.b eggs) =
      (7 : ℝ) / 20 + delta + (eggs.card : ℝ) / 40 := by
  rw [lmms41Player1ShiftedReport, lmms41AdditiveReport]
  rw [Finset.sum_insert heggs.2]
  change
    lmms41Player1ShiftedWeight delta LMMS41Agent.player1 LMMS41Item.b +
        lmms41Player1ShiftedReport delta eggs =
      (7 : ℝ) / 20 + delta + (eggs.card : ℝ) / 40
  rw [lmms41Player1ShiftedReport_eggOnly delta eggs heggs]
  simp

/--
If player 1 keeps good `a`, one additional egg gives strictly higher true
utility.  This is the reusable arithmetic core of the first LMMS Theorem 4.1
case split.
-/
theorem lmms41TrueReport_player1_insert_a_strict_mono_egg_card
    {oldEggs newEggs : Bundle LMMS41Item}
    (hold : lmms41EggOnlyBundle oldEggs)
    (hnew : lmms41EggOnlyBundle newEggs)
    (hcard : oldEggs.card < newEggs.card) :
    lmms41TrueReport LMMS41Agent.player1 (insert LMMS41Item.a oldEggs) <
      lmms41TrueReport LMMS41Agent.player1 (insert LMMS41Item.a newEggs) := by
  rw [lmms41TrueReport_player1_insert_a_eggOnly oldEggs hold,
    lmms41TrueReport_player1_insert_a_eggOnly newEggs hnew]
  have hcardReal : (oldEggs.card : ℝ) < newEggs.card := by
    exact_mod_cast hcard
  linarith

/--
With the paper's first-case shift `delta = (T - 1) / 40`, player 1's declared
value for `a` plus `T + 1` eggs is exactly one half.
-/
theorem lmms41Player1ShiftedReport_insert_a_eq_half_of_card_eq_succ
    (T : ℕ) (eggs : Bundle LMMS41Item)
    (heggs : lmms41EggOnlyBundle eggs)
    (hcard : eggs.card = T + 1) :
    lmms41Player1ShiftedReport (((T : ℝ) - 1) / 40)
        (insert LMMS41Item.a eggs) =
      (1 : ℝ) / 2 := by
  rw [lmms41Player1ShiftedReport_insert_a_eggOnly
    (((T : ℝ) - 1) / 40) eggs heggs]
  have hcardReal : (eggs.card : ℝ) = (T : ℝ) + 1 := by
    exact_mod_cast hcard
  rw [hcardReal]
  ring

/--
Source-shaped certificate for the LMMS Theorem 4.1 counterexample.

The finite arithmetic proof builds this certificate from a mechanism that
returns an envy-free allocation whenever one exists, using the paper's case
split on the number of eggs assigned with good `a`.
-/
structure LMMS41SourceCounterexampleCertificate
    (M : LMMS41Mechanism) where
  agent : LMMS41Agent
  deviationReport : Bundle LMMS41Item → ℝ
  improves :
    M.utility lmms41TrueReport
        (Function.update lmms41TrueReport agent deviationReport) agent >
      M.utility lmms41TrueReport lmms41TrueReport agent

/-- Convert the LMMS source certificate to the reusable mechanism API witness. -/
def LMMS41SourceCounterexampleCertificate.toProfitableDeviation
    {M : LMMS41Mechanism}
    (C : LMMS41SourceCounterexampleCertificate M) :
    M.ProfitableDeviation where
  values := lmms41TrueReport
  agent := C.agent
  report := C.deviationReport
  improves := C.improves

/--
LMMS Theorem 4.1 support: any mechanism with the source-shaped finite
counterexample certificate is not truthful.
-/
theorem lmms41_not_truthful_of_sourceCounterexampleCertificate
    (M : LMMS41Mechanism)
    (C : LMMS41SourceCounterexampleCertificate M) :
    ¬ M.Truthful := by
  exact
    DirectFairDivisionMechanism.not_truthful_of_profitableDeviation M
      C.toProfitableDeviation

/--
LMMS Theorem 4.1 support specialized directly to the new reusable
`ProfitableDeviation` witness.
-/
theorem lmms41_not_truthful_of_profitableDeviation
    (M : LMMS41Mechanism)
    (w : M.ProfitableDeviation) :
    ¬ M.Truthful := by
  exact DirectFairDivisionMechanism.not_truthful_of_profitableDeviation M w

end

end Theorem41
end LMMS04FairDivision
