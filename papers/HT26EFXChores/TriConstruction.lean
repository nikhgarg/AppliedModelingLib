import AppliedModelingLib.SocialChoice.FairDivision.Chores
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The four-agent tri-valued construction

This module formalizes the explicit four-agent obstruction used in the proof
of Theorem 1.  Its count identities keep the later EFX contradiction separate
from the concrete table of individual chore costs.

Source: `EFXadditivechores.tex`, lines 315--404.
-/

namespace HT26EFXChores

open scoped BigOperators
open AppliedModelingLib.FairDivision

/-- The three item classes in the four-agent tri-valued example. -/
def triA : Finset (Fin 13) := Finset.univ.filter fun item => item.val < 3
def triB : Finset (Fin 13) := Finset.univ.filter fun item => 3 ≤ item.val ∧ item.val < 8
def triC : Finset (Fin 13) := Finset.univ.filter fun item => 8 ≤ item.val

/-- The cost table in the paper's four-agent tri-valued example. -/
def triFourCost (agent : Fin 4) (item : Fin 13) : ℝ :=
  if item.val < 3 then 20 else
    if agent.val < 2 then if item.val < 8 then 1 else 7 else
      if item.val < 8 then 7 else 1

theorem triA_card : triA.card = 3 := by decide
theorem triB_card : triB.card = 5 := by decide
theorem triC_card : triC.card = 5 := by decide

theorem triA_union_triB_union_triC : triA ∪ triB ∪ triC = Finset.univ := by decide

theorem triA_triB_disjoint : Disjoint triA triB := by decide
theorem triA_triC_disjoint : Disjoint triA triC := by decide
theorem triB_triC_disjoint : Disjoint triB triC := by decide

private theorem triA_mem_iff (item : Fin 13) : item ∈ triA ↔ item.val < 3 := by
  simp [triA]

private theorem triB_mem_iff (item : Fin 13) : item ∈ triB ↔ 3 ≤ item.val ∧ item.val < 8 := by
  simp [triB]

private theorem triC_mem_iff (item : Fin 13) : item ∈ triC ↔ 8 ≤ item.val := by
  simp [triC]

theorem triFourCost_on_A (agent : Fin 4) (item : Fin 13) (hitem : item ∈ triA) :
    triFourCost agent item = 20 := by
  simp [triFourCost, triA_mem_iff item |>.mp hitem]

theorem triFourCost_on_B_low (agent : Fin 4) (hagent : agent.val < 2)
    (item : Fin 13) (hitem : item ∈ triB) : triFourCost agent item = 1 := by
  have h := triB_mem_iff item |>.mp hitem
  have hnotA : ¬ item.val < 3 := by omega
  simp [triFourCost, hnotA, h.2, hagent]

theorem triFourCost_on_B_high (agent : Fin 4) (hagent : 2 ≤ agent.val)
    (item : Fin 13) (hitem : item ∈ triB) : triFourCost agent item = 7 := by
  have h := triB_mem_iff item |>.mp hitem
  have hnotA : ¬ item.val < 3 := by omega
  have hnotLow : ¬ agent.val < 2 := by omega
  simp [triFourCost, hnotA, h.2, hnotLow]

theorem triFourCost_on_C_low (agent : Fin 4) (hagent : agent.val < 2)
    (item : Fin 13) (hitem : item ∈ triC) : triFourCost agent item = 7 := by
  have h := triC_mem_iff item |>.mp hitem
  have hnotA : ¬ item.val < 3 := by omega
  have hnotB : ¬ item.val < 8 := by omega
  simp [triFourCost, hnotA, hnotB, hagent]

theorem triFourCost_on_C_high (agent : Fin 4) (hagent : 2 ≤ agent.val)
    (item : Fin 13) (hitem : item ∈ triC) : triFourCost agent item = 1 := by
  have h := triC_mem_iff item |>.mp hitem
  have hnotA : ¬ item.val < 3 := by omega
  have hnotLow : ¬ agent.val < 2 := by omega
  have hnotB : ¬ item.val < 8 := by omega
  simp [triFourCost, hnotA, hnotB, hnotLow]

private theorem tri_partition (bundle : Finset (Fin 13)) :
    bundle = (bundle ∩ triA ∪ bundle ∩ triB) ∪ bundle ∩ triC := by
  ext item
  constructor
  · intro hitem
    have hclass : item ∈ triA ∪ triB ∪ triC := by
      rw [triA_union_triB_union_triC]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hclass with hA | hC
    · rcases Finset.mem_union.mp hA with hA | hB
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hitem, hA⟩))))
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hitem, hB⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hitem, hC⟩))
  · intro hitem
    rcases Finset.mem_union.mp hitem with hAB | hC
    · rcases Finset.mem_union.mp hAB with hA | hB
      · exact (Finset.mem_inter.mp hA).1
      · exact (Finset.mem_inter.mp hB).1
    · exact (Finset.mem_inter.mp hC).1

private theorem tri_partition_disjoint_AB (bundle : Finset (Fin 13)) :
    Disjoint (bundle ∩ triA) (bundle ∩ triB) :=
  Disjoint.mono (Finset.inter_subset_right) (Finset.inter_subset_right) triA_triB_disjoint

private theorem tri_partition_disjoint_ABC (bundle : Finset (Fin 13)) :
    Disjoint (bundle ∩ triA ∪ bundle ∩ triB) (bundle ∩ triC) := by
  rw [Finset.disjoint_union_left]
  constructor
  · exact Disjoint.mono (Finset.inter_subset_right) (Finset.inter_subset_right)
      triA_triC_disjoint
  · exact Disjoint.mono (Finset.inter_subset_right) (Finset.inter_subset_right)
      triB_triC_disjoint

private theorem tri_partition_card (bundle : Finset (Fin 13)) :
    bundle.card = (bundle ∩ triA).card + (bundle ∩ triB).card + (bundle ∩ triC).card := by
  conv_lhs => rw [tri_partition bundle]
  rw [Finset.card_union_of_disjoint (tri_partition_disjoint_ABC bundle),
    Finset.card_union_of_disjoint (tri_partition_disjoint_AB bundle)]

private theorem inter_erase_eq_of_not_mem (bundle group : Finset (Fin 13)) (item : Fin 13)
    (hitem : item ∉ group) :
    (bundle \ {item}) ∩ group = bundle ∩ group := by
  ext other
  constructor
  · intro hother
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hother).1).1,
        (Finset.mem_inter.mp hother).2⟩
  · intro hother
    refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hother).2⟩
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hother).1, ?_⟩
    simp only [Finset.mem_singleton]
    intro hEq
    subst other
    exact hitem (Finset.mem_inter.mp hother).2

theorem triFourCost_low_bundle (agent : Fin 4) (hagent : agent.val < 2)
    (bundle : Finset (Fin 13)) :
    additiveChoreCost triFourCost agent bundle =
      (bundle ∩ triA).card • (20 : ℝ) + (bundle ∩ triB).card • (1 : ℝ) +
        (bundle ∩ triC).card • (7 : ℝ) := by
  conv_lhs => rw [tri_partition bundle]
  rw [additiveChoreCost_union triFourCost agent
    (bundle ∩ triA ∪ bundle ∩ triB) (bundle ∩ triC) (tri_partition_disjoint_ABC bundle),
    additiveChoreCost_union triFourCost agent (bundle ∩ triA) (bundle ∩ triB)
      (tri_partition_disjoint_AB bundle)]
  have hA : ∀ item ∈ bundle ∩ triA, triFourCost agent item = 20 := by
    intro item hitem
    exact triFourCost_on_A agent item (Finset.mem_inter.mp hitem).2
  have hB : ∀ item ∈ bundle ∩ triB, triFourCost agent item = 1 := by
    intro item hitem
    exact triFourCost_on_B_low agent hagent item (Finset.mem_inter.mp hitem).2
  have hC : ∀ item ∈ bundle ∩ triC, triFourCost agent item = 7 := by
    intro item hitem
    exact triFourCost_on_C_low agent hagent item (Finset.mem_inter.mp hitem).2
  rw [additiveChoreCost_eq_card_nsmul_of_constant triFourCost agent (bundle ∩ triA) 20 hA,
    additiveChoreCost_eq_card_nsmul_of_constant triFourCost agent (bundle ∩ triB) 1 hB,
    additiveChoreCost_eq_card_nsmul_of_constant triFourCost agent (bundle ∩ triC) 7 hC]

theorem triFourCost_high_bundle (agent : Fin 4) (hagent : 2 ≤ agent.val)
    (bundle : Finset (Fin 13)) :
    additiveChoreCost triFourCost agent bundle =
      (bundle ∩ triA).card • (20 : ℝ) + (bundle ∩ triB).card • (7 : ℝ) +
        (bundle ∩ triC).card • (1 : ℝ) := by
  conv_lhs => rw [tri_partition bundle]
  rw [additiveChoreCost_union triFourCost agent
    (bundle ∩ triA ∪ bundle ∩ triB) (bundle ∩ triC) (tri_partition_disjoint_ABC bundle),
    additiveChoreCost_union triFourCost agent (bundle ∩ triA) (bundle ∩ triB)
      (tri_partition_disjoint_AB bundle)]
  have hA : ∀ item ∈ bundle ∩ triA, triFourCost agent item = 20 := by
    intro item hitem
    exact triFourCost_on_A agent item (Finset.mem_inter.mp hitem).2
  have hB : ∀ item ∈ bundle ∩ triB, triFourCost agent item = 7 := by
    intro item hitem
    exact triFourCost_on_B_high agent hagent item (Finset.mem_inter.mp hitem).2
  have hC : ∀ item ∈ bundle ∩ triC, triFourCost agent item = 1 := by
    intro item hitem
    exact triFourCost_on_C_high agent hagent item (Finset.mem_inter.mp hitem).2
  rw [additiveChoreCost_eq_card_nsmul_of_constant triFourCost agent (bundle ∩ triA) 20 hA,
    additiveChoreCost_eq_card_nsmul_of_constant triFourCost agent (bundle ∩ triB) 7 hB,
    additiveChoreCost_eq_card_nsmul_of_constant triFourCost agent (bundle ∩ triC) 1 hC]

theorem triFourCost_total (agent : Fin 4) :
    additiveChoreCost triFourCost agent Finset.univ = 100 := by
  by_cases hlow : agent.val < 2
  · rw [triFourCost_low_bundle agent hlow]
    norm_num [triA_card, triB_card, triC_card]
  · have hhigh : 2 ≤ agent.val := by omega
    rw [triFourCost_high_bundle agent hhigh]
    norm_num [triA_card, triB_card, triC_card]

theorem triFourCost_allocation_total (agent : Fin 4)
    (allocation : Allocation (Fin 4) (Fin 13))
    (halloc : IsAllocationOf allocation Finset.univ) :
    Finset.univ.sum (fun owner => additiveChoreCost triFourCost agent (allocation owner)) = 100 := by
  rw [sum_additiveChoreCost_allocation_eq_additiveChoreCost triFourCost agent allocation
    Finset.univ halloc, triFourCost_total]

private theorem exists_tri_bundle_cost_le_25 (agent : Fin 4)
    (allocation : Allocation (Fin 4) (Fin 13))
    (halloc : IsAllocationOf allocation Finset.univ) :
    ∃ owner, additiveChoreCost triFourCost agent (allocation owner) ≤ 25 := by
  by_contra hnone
  push Not at hnone
  have hsum := triFourCost_allocation_total agent allocation halloc
  simp [Fin.sum_univ_succ] at hsum
  have hzero := hnone 0
  have hone := hnone 1
  have htwo := hnone 2
  have hthree := hnone 3
  norm_num at hzero hone htwo hthree
  linarith

theorem triA_filter_eq_inter (bundle : Finset (Fin 13)) :
    bundle.filter (fun item => item.val < 3) = bundle ∩ triA := by
  ext item
  simp [triA]

private theorem tri_cost_erase_A_ge_40 (agent : Fin 4)
    (allocation : Allocation (Fin 4) (Fin 13)) (item : Fin 13)
    (hitem : item ∈ allocation agent) (hAitem : item ∈ triA)
    (hAcard : 3 ≤ (allocation agent ∩ triA).card) :
    40 ≤ additiveChoreCost triFourCost agent (allocation agent \ {item}) := by
  have heraseA : (allocation agent \ {item}) ∩ triA =
      (allocation agent ∩ triA).erase item := by
    ext other
    simp [and_left_comm, and_comm]
  have hAitem' : item ∈ allocation agent ∩ triA :=
    Finset.mem_inter.mpr ⟨hitem, hAitem⟩
  have hAcardErased : 2 ≤ ((allocation agent \ {item}) ∩ triA).card := by
    rw [heraseA, Finset.card_erase_of_mem hAitem']
    omega
  by_cases hlow : agent.val < 2
  · rw [triFourCost_low_bundle agent hlow]
    have hAterm : (40 : ℝ) ≤ ((allocation agent \ {item} ∩ triA).card : ℝ) * 20 := by
      exact_mod_cast (Nat.mul_le_mul_right 20 hAcardErased)
    have hBnonneg : 0 ≤ ((allocation agent \ {item} ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((allocation agent \ {item} ∩ triC).card : ℝ) := Nat.cast_nonneg _
    norm_num [nsmul_eq_mul]
    linarith
  · have hhigh : 2 ≤ agent.val := by omega
    rw [triFourCost_high_bundle agent hhigh]
    have hAterm : (40 : ℝ) ≤ ((allocation agent \ {item} ∩ triA).card : ℝ) * 20 := by
      exact_mod_cast (Nat.mul_le_mul_right 20 hAcardErased)
    have hBnonneg : 0 ≤ ((allocation agent \ {item} ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((allocation agent \ {item} ∩ triC).card : ℝ) := Nat.cast_nonneg _
    norm_num [nsmul_eq_mul]
    linarith

private theorem tri_no_three_A_items (allocation : Allocation (Fin 4) (Fin 13))
    (halloc : IsAllocationOf allocation Finset.univ)
    (hefx : EFXForChores (additiveChoreCost triFourCost) allocation) (agent : Fin 4) :
    (allocation agent ∩ triA).card ≤ 2 := by
  by_contra hnot
  have hAcard : 3 ≤ (allocation agent ∩ triA).card := by omega
  have hApositive : 0 < (allocation agent ∩ triA).card := by omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp hApositive
  have hitem : item ∈ allocation agent := (Finset.mem_inter.mp hitemInter).1
  have hAitem : item ∈ triA := (Finset.mem_inter.mp hitemInter).2
  obtain ⟨other, hother⟩ := exists_tri_bundle_cost_le_25 agent allocation halloc
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitem
    simp at hitem
  have hefxItem := (hefx agent other).resolve_left hnonempty item hitem
  have hremaining := tri_cost_erase_A_ge_40 agent allocation item hitem hAitem hAcard
  linarith

private theorem tri_cost_erase_A_ge_20 (agent : Fin 4)
    (allocation : Allocation (Fin 4) (Fin 13)) (item : Fin 13)
    (hitem : item ∈ allocation agent) (hAitem : item ∈ triA)
    (hAcard : 2 ≤ (allocation agent ∩ triA).card) :
    20 ≤ additiveChoreCost triFourCost agent (allocation agent \ {item}) := by
  have heraseA : (allocation agent \ {item}) ∩ triA =
      (allocation agent ∩ triA).erase item := by
    ext other
    simp [and_left_comm, and_comm]
  have hAitem' : item ∈ allocation agent ∩ triA :=
    Finset.mem_inter.mpr ⟨hitem, hAitem⟩
  have hAcardErased : 1 ≤ ((allocation agent \ {item}) ∩ triA).card := by
    rw [heraseA, Finset.card_erase_of_mem hAitem']
    omega
  by_cases hlow : agent.val < 2
  · rw [triFourCost_low_bundle agent hlow]
    have hAterm : (20 : ℝ) ≤ ((allocation agent \ {item} ∩ triA).card : ℝ) * 20 := by
      exact_mod_cast (Nat.mul_le_mul_right 20 hAcardErased)
    have hBnonneg : 0 ≤ ((allocation agent \ {item} ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((allocation agent \ {item} ∩ triC).card : ℝ) := Nat.cast_nonneg _
    norm_num [nsmul_eq_mul]
    linarith
  · have hhigh : 2 ≤ agent.val := by omega
    rw [triFourCost_high_bundle agent hhigh]
    have hAterm : (20 : ℝ) ≤ ((allocation agent \ {item} ∩ triA).card : ℝ) * 20 := by
      exact_mod_cast (Nat.mul_le_mul_right 20 hAcardErased)
    have hBnonneg : 0 ≤ ((allocation agent \ {item} ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((allocation agent \ {item} ∩ triC).card : ℝ) := Nat.cast_nonneg _
    norm_num [nsmul_eq_mul]
    linarith

private theorem four_sum_forces_40_20 (f : Fin 4 → ℝ) (agent : Fin 4)
    (hsum : Finset.univ.sum f = 100) (hself : 40 ≤ f agent)
    (hother : ∀ other, other ≠ agent → 20 ≤ f other) :
    f agent = 40 ∧ ∀ other, other ≠ agent → f other = 20 := by
  rw [Fin.sum_univ_four] at hsum
  fin_cases agent
  · have hself0 : 40 ≤ f 0 := by simpa using hself
    have h1 := hother 1 (by decide)
    have h2 := hother 2 (by decide)
    have h3 := hother 3 (by decide)
    constructor
    · change f 0 = 40
      linarith
    · intro other hne
      fin_cases other
      · simp at hne
      · change f 1 = 20
        linarith
      · change f 2 = 20
        linarith
      · change f 3 = 20
        linarith
  · have hself1 : 40 ≤ f 1 := by simpa using hself
    have h0 := hother 0 (by decide)
    have h2 := hother 2 (by decide)
    have h3 := hother 3 (by decide)
    constructor
    · change f 1 = 40
      linarith
    · intro other hne
      fin_cases other
      · change f 0 = 20
        linarith
      · simp at hne
      · change f 2 = 20
        linarith
      · change f 3 = 20
        linarith
  · have hself2 : 40 ≤ f 2 := by simpa using hself
    have h0 := hother 0 (by decide)
    have h1 := hother 1 (by decide)
    have h3 := hother 3 (by decide)
    constructor
    · change f 2 = 40
      linarith
    · intro other hne
      fin_cases other
      · change f 0 = 20
        linarith
      · change f 1 = 20
        linarith
      · simp at hne
      · change f 3 = 20
        linarith
  · have hself3 : 40 ≤ f 3 := by simpa using hself
    have h0 := hother 0 (by decide)
    have h1 := hother 1 (by decide)
    have h2 := hother 2 (by decide)
    constructor
    · change f 3 = 40
      linarith
    · intro other hne
      fin_cases other
      · change f 0 = 20
        linarith
      · change f 1 = 20
        linarith
      · change f 2 = 20
        linarith
      · simp at hne

private theorem four_card_sum_impossible (counts : Fin 4 → ℕ)
    (first second : Fin 4) (hsum : Finset.univ.sum counts = 5)
    (hfirst : counts first = 0) (hsecond : counts second = 0)
    (hne : second ≠ first)
    (hbound : ∀ owner, owner ≠ first → owner ≠ second → counts owner ≤ 2) : False := by
  let others : Finset (Fin 4) := (Finset.univ.erase first).erase second
  have hsecondMem : second ∈ Finset.univ.erase first := by simp [hne]
  have hsumFirst : (Finset.univ.erase first).sum counts = 5 := by
    have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin 4)) counts
      (Finset.mem_univ first)
    linarith
  have hsumOthers : others.sum counts = 5 := by
    have herase := Finset.sum_erase_add (Finset.univ.erase first) counts hsecondMem
    change ((Finset.univ.erase first).erase second).sum counts = 5
    linarith
  have hcardOthers : others.card = 2 := by
    simp [others, hne]
  have hupper : others.sum counts ≤ others.card • 2 := by
    apply Finset.sum_le_card_nsmul
    intro owner howner
    apply hbound owner
    · intro hEq
      change owner ∈ (Finset.univ.erase first).erase second at howner
      have hownerInner : owner ∈ Finset.univ.erase first := (Finset.mem_erase.mp howner).2
      exact (Finset.mem_erase.mp hownerInner).1 hEq
    · change owner ∈ (Finset.univ.erase first).erase second at howner
      exact (Finset.mem_erase.mp howner).1
  rw [hsumOthers, hcardOthers] at hupper
  norm_num at hupper

private theorem tri_cost_ge_20_of_A_nonempty (agent : Fin 4) (bundle : Finset (Fin 13))
    (hApositive : 1 ≤ (bundle ∩ triA).card) :
    20 ≤ additiveChoreCost triFourCost agent bundle := by
  by_cases hlow : agent.val < 2
  · rw [triFourCost_low_bundle agent hlow]
    have hApositive' : 1 ≤ ((bundle ∩ triA).card : ℝ) := by
      exact_mod_cast hApositive
    have hBnonneg : 0 ≤ ((bundle ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ triC).card : ℝ) := Nat.cast_nonneg _
    norm_num [nsmul_eq_mul]
    linarith
  · have hhigh : 2 ≤ agent.val := by omega
    rw [triFourCost_high_bundle agent hhigh]
    have hApositive' : 1 ≤ ((bundle ∩ triA).card : ℝ) := by
      exact_mod_cast hApositive
    have hBnonneg : 0 ≤ ((bundle ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ triC).card : ℝ) := Nat.cast_nonneg _
    norm_num [nsmul_eq_mul]
    linarith

private theorem tri_cost_ge_21_of_A_one_and_two_items (agent : Fin 4)
    (bundle : Finset (Fin 13)) (hAcard : (bundle ∩ triA).card = 1)
    (hcard : 2 ≤ bundle.card) :
    21 ≤ additiveChoreCost triFourCost agent bundle := by
  have hpartition := tri_partition_card bundle
  have hBCpositive : 1 ≤ (bundle ∩ triB).card + (bundle ∩ triC).card := by
    rw [hAcard] at hpartition
    omega
  by_cases hlow : agent.val < 2
  · rw [triFourCost_low_bundle agent hlow, hAcard]
    have hBnonneg : 0 ≤ ((bundle ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ triC).card : ℝ) := Nat.cast_nonneg _
    have hBCpositive' : 1 ≤ ((bundle ∩ triB).card : ℝ) +
        ((bundle ∩ triC).card : ℝ) := by exact_mod_cast hBCpositive
    norm_num [nsmul_eq_mul]
    linarith
  · have hhigh : 2 ≤ agent.val := by omega
    rw [triFourCost_high_bundle agent hhigh, hAcard]
    have hBnonneg : 0 ≤ ((bundle ∩ triB).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ triC).card : ℝ) := Nat.cast_nonneg _
    have hBCpositive' : 1 ≤ ((bundle ∩ triB).card : ℝ) +
        ((bundle ∩ triC).card : ℝ) := by exact_mod_cast hBCpositive
    norm_num [nsmul_eq_mul]
    linarith

private theorem four_card_zero_ge_eight (counts : Fin 4 → ℕ) (special : Fin 4)
    (hspecial : special ≠ 0) (hsum : Finset.univ.sum counts = 13)
    (hspecialCard : counts special = 1)
    (hbound : ∀ owner, owner ≠ 0 → owner ≠ special → counts owner ≤ 2) :
    8 ≤ counts 0 := by
  let others : Finset (Fin 4) := (Finset.univ.erase 0).erase special
  have hspecialMem : special ∈ Finset.univ.erase 0 := by simp [hspecial]
  have hsumZero : (Finset.univ.erase 0).sum counts + counts 0 = 13 := by
    have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin 4)) counts
      (Finset.mem_univ 0)
    linarith
  have hsumOthers : others.sum counts + counts special =
      (Finset.univ.erase 0).sum counts := by
    change ((Finset.univ.erase 0).erase special).sum counts + counts special =
      (Finset.univ.erase 0).sum counts
    exact Finset.sum_erase_add (Finset.univ.erase 0) counts hspecialMem
  have hcardOthers : others.card = 2 := by simp [others, hspecial]
  have hupper : others.sum counts ≤ others.card • 2 := by
    apply Finset.sum_le_card_nsmul
    intro owner howner
    apply hbound owner
    · change owner ∈ (Finset.univ.erase 0).erase special at howner
      have hownerInner : owner ∈ Finset.univ.erase 0 := (Finset.mem_erase.mp howner).2
      exact (Finset.mem_erase.mp hownerInner).1
    · change owner ∈ (Finset.univ.erase 0).erase special at howner
      exact (Finset.mem_erase.mp howner).1
  rw [hcardOthers] at hupper
  norm_num at hupper
  omega

theorem tri_four_no_two_large_proof (allocation : Allocation (Fin 4) (Fin 13))
    (halloc : IsAllocationOf allocation Finset.univ)
    (hefx : EFXForChores (additiveChoreCost triFourCost) allocation) :
    ∀ agent, (allocation agent ∩ triA).card ≤ 1 := by
  intro agent
  by_contra hnot
  have hAtLeastTwo : 2 ≤ (allocation agent ∩ triA).card := by omega
  have hAtMostTwo := tri_no_three_A_items allocation halloc hefx agent
  have hAcard : (allocation agent ∩ triA).card = 2 := by omega
  have hApositive : 0 < (allocation agent ∩ triA).card := by omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp hApositive
  have hitem : item ∈ allocation agent := (Finset.mem_inter.mp hitemInter).1
  have hitemA : item ∈ triA := (Finset.mem_inter.mp hitemInter).2
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitem
    simp at hitem
  have hremainingCost := tri_cost_erase_A_ge_20 agent allocation item hitem hitemA hAtLeastTwo
  have hselfLower : 40 ≤ additiveChoreCost triFourCost agent (allocation agent) := by
    rw [additiveChoreCost_erase triFourCost agent (allocation agent) item hitem,
      triFourCost_on_A agent item hitemA] at hremainingCost
    linarith
  have hotherLower : ∀ other, other ≠ agent →
      20 ≤ additiveChoreCost triFourCost agent (allocation other) := by
    intro other hne
    have hefxItem := (hefx agent other).resolve_left hnonempty item hitem
    linarith
  obtain ⟨hself, hothers⟩ := four_sum_forces_40_20
    (fun owner => additiveChoreCost triFourCost agent (allocation owner)) agent
    (triFourCost_allocation_total agent allocation halloc) hselfLower hotherLower
  have htargetA_lt : (allocation agent ∩ triA).card < triA.card := by
    rw [hAcard, triA_card]
    norm_num
  obtain ⟨remaining, hremainingA, hremainingNotTarget⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := allocation agent ∩ triA) (t := triA)
      htargetA_lt
  have hremainingNotInTarget : remaining ∉ allocation agent := by
    intro hremainingTarget
    exact hremainingNotTarget (Finset.mem_inter.mpr ⟨hremainingTarget, hremainingA⟩)
  obtain ⟨special, hspecialMem⟩ := isAllocationOf_exists_owner halloc
    (Finset.mem_univ remaining)
  have hspecialNe : special ≠ agent := by
    intro hEq
    subst special
    exact hremainingNotInTarget hspecialMem
  have hspecialCost : additiveChoreCost triFourCost agent (allocation special) = 20 :=
    hothers special hspecialNe
  by_cases hlow : agent.val < 2
  · have htargetCzero : (allocation agent ∩ triC).card = 0 := by
      have hformula := triFourCost_low_bundle agent hlow (allocation agent)
      rw [hself, hAcard] at hformula
      by_contra hCnot
      have hCpositive : 1 ≤ (allocation agent ∩ triC).card := by omega
      have hBnonneg : 0 ≤ ((allocation agent ∩ triB).card : ℝ) := Nat.cast_nonneg _
      have hCpositive' : 1 ≤ ((allocation agent ∩ triC).card : ℝ) := by
        exact_mod_cast hCpositive
      norm_num [nsmul_eq_mul] at hformula
      linarith
    have hspecialCzero : (allocation special ∩ triC).card = 0 := by
      have hApositiveSpecial : 1 ≤ (allocation special ∩ triA).card := by
        have hpositive : 0 < (allocation special ∩ triA).card := Finset.card_pos.mpr
          ⟨remaining, Finset.mem_inter.mpr ⟨hspecialMem, hremainingA⟩⟩
        omega
      have hformula := triFourCost_low_bundle agent hlow (allocation special)
      rw [hspecialCost] at hformula
      by_contra hCnot
      have hCpositive : 1 ≤ (allocation special ∩ triC).card := by omega
      have hApositive' : 1 ≤ ((allocation special ∩ triA).card : ℝ) := by
        exact_mod_cast hApositiveSpecial
      have hBnonneg : 0 ≤ ((allocation special ∩ triB).card : ℝ) := Nat.cast_nonneg _
      have hCpositive' : 1 ≤ ((allocation special ∩ triC).card : ℝ) := by
        exact_mod_cast hCpositive
      norm_num [nsmul_eq_mul] at hformula
      linarith
    have hbound : ∀ owner, owner ≠ agent → owner ≠ special →
        (allocation owner ∩ triC).card ≤ 2 := by
      intro owner hneAgent _
      have hcost := hothers owner hneAgent
      have hformula := triFourCost_low_bundle agent hlow (allocation owner)
      rw [hcost] at hformula
      by_contra hCnot
      have hCge : 3 ≤ (allocation owner ∩ triC).card := by omega
      have hAnonneg : 0 ≤ ((allocation owner ∩ triA).card : ℝ) := Nat.cast_nonneg _
      have hBnonneg : 0 ≤ ((allocation owner ∩ triB).card : ℝ) := Nat.cast_nonneg _
      have hCge' : 3 ≤ ((allocation owner ∩ triC).card : ℝ) := by
        exact_mod_cast hCge
      norm_num [nsmul_eq_mul] at hformula
      linarith
    apply four_card_sum_impossible (fun owner => (allocation owner ∩ triC).card) agent special
      (by
        simpa [triC_card] using
          (sum_card_inter_allocation_eq_card_inter allocation Finset.univ triC halloc))
      htargetCzero hspecialCzero hspecialNe hbound
  · have hhigh : 2 ≤ agent.val := by omega
    have htargetBzero : (allocation agent ∩ triB).card = 0 := by
      have hformula := triFourCost_high_bundle agent hhigh (allocation agent)
      rw [hself, hAcard] at hformula
      by_contra hBnot
      have hBpositive : 1 ≤ (allocation agent ∩ triB).card := by omega
      have hCnonneg : 0 ≤ ((allocation agent ∩ triC).card : ℝ) := Nat.cast_nonneg _
      have hBpositive' : 1 ≤ ((allocation agent ∩ triB).card : ℝ) := by
        exact_mod_cast hBpositive
      norm_num [nsmul_eq_mul] at hformula
      linarith
    have hspecialBzero : (allocation special ∩ triB).card = 0 := by
      have hApositiveSpecial : 1 ≤ (allocation special ∩ triA).card := by
        have hpositive : 0 < (allocation special ∩ triA).card := Finset.card_pos.mpr
          ⟨remaining, Finset.mem_inter.mpr ⟨hspecialMem, hremainingA⟩⟩
        omega
      have hformula := triFourCost_high_bundle agent hhigh (allocation special)
      rw [hspecialCost] at hformula
      by_contra hBnot
      have hBpositive : 1 ≤ (allocation special ∩ triB).card := by omega
      have hApositive' : 1 ≤ ((allocation special ∩ triA).card : ℝ) := by
        exact_mod_cast hApositiveSpecial
      have hBpositive' : 1 ≤ ((allocation special ∩ triB).card : ℝ) := by
        exact_mod_cast hBpositive
      have hCnonneg : 0 ≤ ((allocation special ∩ triC).card : ℝ) := Nat.cast_nonneg _
      norm_num [nsmul_eq_mul] at hformula
      linarith
    have hbound : ∀ owner, owner ≠ agent → owner ≠ special →
        (allocation owner ∩ triB).card ≤ 2 := by
      intro owner hneAgent _
      have hcost := hothers owner hneAgent
      have hformula := triFourCost_high_bundle agent hhigh (allocation owner)
      rw [hcost] at hformula
      by_contra hBnot
      have hBge : 3 ≤ (allocation owner ∩ triB).card := by omega
      have hAnonneg : 0 ≤ ((allocation owner ∩ triA).card : ℝ) := Nat.cast_nonneg _
      have hCnonneg : 0 ≤ ((allocation owner ∩ triC).card : ℝ) := Nat.cast_nonneg _
      have hBge' : 3 ≤ ((allocation owner ∩ triB).card : ℝ) := by
        exact_mod_cast hBge
      norm_num [nsmul_eq_mul] at hformula
      linarith
    apply four_card_sum_impossible (fun owner => (allocation owner ∩ triB).card) agent special
      (by
        simpa [triB_card] using
          (sum_card_inter_allocation_eq_card_inter allocation Finset.univ triB halloc))
      htargetBzero hspecialBzero hspecialNe hbound

private theorem tri_no_A_bundle_cost_ge_20_for_nonzero
    (allocation : Allocation (Fin 4) (Fin 13))
    (halloc : IsAllocationOf allocation Finset.univ)
    (hefx : EFXForChores (additiveChoreCost triFourCost) allocation)
    (hzero : (allocation 0 ∩ triA).card = 0)
    (hone : ∀ agent, agent ≠ 0 → (allocation agent ∩ triA).card = 1)
    (special : Fin 4) (hspecial : special ≠ 0) :
    20 ≤ additiveChoreCost triFourCost special (allocation 0) := by
  by_contra hlow
  have hlow' : additiveChoreCost triFourCost special (allocation 0) < 20 := lt_of_not_ge hlow
  have hAcardSpecial := hone special hspecial
  have hsubsetA : allocation special ⊆ triA := by
    intro item hitem
    by_contra hitemA
    have heraseA : (allocation special \ {item}) ∩ triA = allocation special ∩ triA :=
      inter_erase_eq_of_not_mem (allocation special) triA item hitemA
    have hApositive : 1 ≤ ((allocation special \ {item}) ∩ triA).card := by
      rw [heraseA, hAcardSpecial]
    have hremaining := tri_cost_ge_20_of_A_nonempty special (allocation special \ {item})
      hApositive
    have hnonempty : allocation special ≠ ∅ := by
      intro hempty
      rw [hempty] at hitem
      simp at hitem
    have hefxItem := (hefx special 0).resolve_left hnonempty item hitem
    exact hlow (hremaining.trans hefxItem)
  have hspecialInter : allocation special ∩ triA = allocation special :=
    Finset.inter_eq_left.mpr hsubsetA
  have hspecialCard : (allocation special).card = 1 := by
    rw [← hspecialInter]
    exact hAcardSpecial
  obtain ⟨a, hspecialEq⟩ := Finset.card_eq_one.mp hspecialCard
  have haMem : a ∈ allocation special := by rw [hspecialEq]; simp
  have haA : a ∈ triA := hsubsetA haMem
  have hbound : ∀ agent, agent ≠ 0 → agent ≠ special → (allocation agent).card ≤ 2 := by
    intro agent hagentZero hagentSpecial
    by_contra hcardNot
    have hcard : 3 ≤ (allocation agent).card := by omega
    have hAcardAgent := hone agent hagentZero
    have hextra : ∃ item ∈ allocation agent, item ∉ triA := by
      by_contra hnoExtra
      push Not at hnoExtra
      have hsubset : allocation agent ⊆ triA := by
        intro item hitem
        exact hnoExtra item hitem
      have hinter : allocation agent ∩ triA = allocation agent :=
        Finset.inter_eq_left.mpr hsubset
      rw [hinter] at hAcardAgent
      omega
    obtain ⟨item, hitem, hitemA⟩ := hextra
    have heraseA : (allocation agent \ {item}) ∩ triA = allocation agent ∩ triA :=
      inter_erase_eq_of_not_mem (allocation agent) triA item hitemA
    have hAcardErase : ((allocation agent \ {item}) ∩ triA).card = 1 := by
      rw [heraseA, hAcardAgent]
    have hcardErase : 2 ≤ (allocation agent \ {item}).card := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitem]
      omega
    have hremaining := tri_cost_ge_21_of_A_one_and_two_items agent
      (allocation agent \ {item}) hAcardErase hcardErase
    have hcomparison : additiveChoreCost triFourCost agent (allocation special) = 20 := by
      rw [hspecialEq]
      simp only [additiveChoreCost, Finset.sum_singleton]
      exact triFourCost_on_A agent a haA
    have hnonempty : allocation agent ≠ ∅ := by
      intro hempty
      rw [hempty] at hitem
      simp at hitem
    have hefxItem := (hefx agent special).resolve_left hnonempty item hitem
    linarith
  have hsum : Finset.univ.sum (fun agent => (allocation agent).card) = 13 := by
    simpa using (sum_card_allocation_eq_card_of_isAllocation allocation Finset.univ halloc)
  have hzeroCard : 8 ≤ (allocation 0).card :=
    four_card_zero_ge_eight (fun agent => (allocation agent).card) special hspecial hsum
      hspecialCard hbound
  have hpartition := tri_partition_card (allocation 0)
  have hBupper : (allocation 0 ∩ triB).card ≤ 5 := by
    calc
      (allocation 0 ∩ triB).card ≤ triB.card := Finset.card_le_card Finset.inter_subset_right
      _ = 5 := triB_card
  have hCupper : (allocation 0 ∩ triC).card ≤ 5 := by
    calc
      (allocation 0 ∩ triC).card ≤ triC.card := Finset.card_le_card Finset.inter_subset_right
      _ = 5 := triC_card
  have hBcard : 3 ≤ (allocation 0 ∩ triB).card := by
    rw [hzero] at hpartition
    omega
  have hCcard : 3 ≤ (allocation 0 ∩ triC).card := by
    rw [hzero] at hpartition
    omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp (by omega : 0 < (allocation 0 ∩ triB).card)
  have hitem : item ∈ allocation 0 := (Finset.mem_inter.mp hitemInter).1
  have hitemB : item ∈ triB := (Finset.mem_inter.mp hitemInter).2
  have hitemNotA : item ∉ triA := by
    intro hitemA
    exact Finset.disjoint_left.mp triA_triB_disjoint hitemA hitemB
  have hitemNotC : item ∉ triC := by
    intro hitemC
    exact Finset.disjoint_left.mp triB_triC_disjoint hitemB hitemC
  have heraseA : (allocation 0 \ {item}) ∩ triA = allocation 0 ∩ triA :=
    inter_erase_eq_of_not_mem (allocation 0) triA item hitemNotA
  have heraseB : (allocation 0 \ {item}) ∩ triB = (allocation 0 ∩ triB).erase item := by
    ext other
    simp [and_left_comm, and_comm]
  have heraseC : (allocation 0 \ {item}) ∩ triC = allocation 0 ∩ triC :=
    inter_erase_eq_of_not_mem (allocation 0) triC item hitemNotC
  have hBremain : 2 ≤ ((allocation 0 \ {item}) ∩ triB).card := by
    have hitemB' : item ∈ allocation 0 ∩ triB := Finset.mem_inter.mpr ⟨hitem, hitemB⟩
    rw [heraseB, Finset.card_erase_of_mem hitemB']
    omega
  have hCremain : 3 ≤ ((allocation 0 \ {item}) ∩ triC).card := by
    rw [heraseC]
    exact hCcard
  have hremainingCost : 23 ≤ additiveChoreCost triFourCost 0 (allocation 0 \ {item}) := by
    have hformula := triFourCost_low_bundle 0 (by decide) (allocation 0 \ {item})
    rw [heraseA, hzero] at hformula
    have hBremain' : 2 ≤ (((allocation 0 \ {item}) ∩ triB).card : ℝ) := by
      exact_mod_cast hBremain
    have hCremain' : 3 ≤ (((allocation 0 \ {item}) ∩ triC).card : ℝ) := by
      exact_mod_cast hCremain
    norm_num [nsmul_eq_mul] at hformula
    linarith
  have hcomparison : additiveChoreCost triFourCost 0 (allocation special) = 20 := by
    rw [hspecialEq]
    simp only [additiveChoreCost, Finset.sum_singleton]
    exact triFourCost_on_A 0 a haA
  have hzeroNonempty : allocation 0 ≠ ∅ := by
    intro hempty
    rw [hempty] at hitem
    simp at hitem
  have hefxItem := (hefx 0 special).resolve_left hzeroNonempty item hitem
  linarith

theorem tri_four_no_A_bundle_expensive_proof (allocation : Allocation (Fin 4) (Fin 13))
    (halloc : IsAllocationOf allocation Finset.univ)
    (hefx : EFXForChores (additiveChoreCost triFourCost) allocation)
    (hzero : (allocation 0 ∩ triA).card = 0)
    (hone : ∀ agent, agent ≠ 0 → (allocation agent ∩ triA).card = 1) :
    ∀ agent, 20 ≤ additiveChoreCost triFourCost agent (allocation 0) := by
  intro agent
  by_cases hagentZero : agent = 0
  · subst agent
    have hagentOne := tri_no_A_bundle_cost_ge_20_for_nonzero allocation halloc hefx hzero hone 1
      (by decide)
    have hcostEq : additiveChoreCost triFourCost 0 (allocation 0) =
        additiveChoreCost triFourCost 1 (allocation 0) := by
      unfold additiveChoreCost
      apply Finset.sum_congr rfl
      intro item _
      simp [triFourCost]
    linarith
  · exact tri_no_A_bundle_cost_ge_20_for_nonzero allocation halloc hefx hzero hone agent hagentZero

end HT26EFXChores
