import HT26EFXChores.AppendixTriArithmetic

/-!
# Bundle accounting for the general tri-valued obstruction

These lemmas expose the two source bundle functions `P₁` and `P₂` directly as
additive chore costs.  They deliberately work for arbitrary finite item labels
and a stated A/B/C partition, which is the source-to-Lean bridge used by the
Appendix propositions.

Source: `EFXadditivechores.tex`, Appendix A, lines 2036--2067.
-/

namespace HT26EFXChores

open scoped BigOperators
open AppliedModelingLib.FairDivision

private theorem appendix_partition_bundle {Item : Type} [DecidableEq Item]
    (A B C chores bundle : Finset Item)
    (hpartition : A ∪ B ∪ C = chores) (hsubset : bundle ⊆ chores) :
    bundle = (bundle ∩ A ∪ bundle ∩ B) ∪ bundle ∩ C := by
  ext item
  constructor
  · intro hitem
    have hclass : item ∈ A ∪ B ∪ C := by
      rw [hpartition]
      exact hsubset hitem
    rcases Finset.mem_union.mp hclass with hABitem | hCitem
    · rcases Finset.mem_union.mp hABitem with hAitem | hBitem
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hitem, hAitem⟩))))
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hitem, hBitem⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hitem, hCitem⟩))
  · intro hitem
    rcases Finset.mem_union.mp hitem with hABitem | hCitem
    · rcases Finset.mem_union.mp hABitem with hAitem | hBitem
      · exact (Finset.mem_inter.mp hAitem).1
      · exact (Finset.mem_inter.mp hBitem).1
    · exact (Finset.mem_inter.mp hCitem).1

private theorem appendix_inter_disjoint {Item : Type} [DecidableEq Item]
    (A B : Finset Item) (bundle : Finset Item) (hdisjoint : Disjoint A B) :
    Disjoint (bundle ∩ A) (bundle ∩ B) :=
  Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisjoint

private theorem appendix_inter_union_disjoint {Item : Type} [DecidableEq Item]
    (A B C : Finset Item) (bundle : Finset Item)
    (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Disjoint (bundle ∩ A ∪ bundle ∩ B) (bundle ∩ C) := by
  rw [Finset.disjoint_union_left]
  constructor
  · exact appendix_inter_disjoint A C bundle hAC
  · exact appendix_inter_disjoint B C bundle hBC

/-- Removing an item outside a class does not change the corresponding class
intersection.  Kept private because it is only accounting infrastructure for
the final Appendix-A EFX contradiction. -/
private theorem appendix_inter_erase_eq_of_not_mem {Item : Type} [DecidableEq Item]
    (bundle group : Finset Item) (item : Item) (hitem : item ∉ group) :
    (bundle \ {item}) ∩ group = bundle ∩ group := by
  ext candidate
  constructor
  · intro hcandidate
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hcandidate).1).1,
        (Finset.mem_inter.mp hcandidate).2⟩
  · intro hcandidate
    refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hcandidate).2⟩
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hcandidate).1, ?_⟩
    intro heq
    have hEq : candidate = item := Finset.mem_singleton.mp heq
    subst candidate
    exact hitem (Finset.mem_inter.mp hcandidate).2

/-- The A/B/C partition gives a cardinal accounting identity for every
subbundle of the Appendix-A chore pool. -/
theorem appendix_partition_card {Item : Type} [DecidableEq Item]
    (A B C chores bundle : Finset Item)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores) (hsubset : bundle ⊆ chores) :
    bundle.card = (bundle ∩ A).card + (bundle ∩ B).card + (bundle ∩ C).card := by
  conv_lhs => rw [appendix_partition_bundle A B C chores bundle hpartition hsubset]
  rw [Finset.card_union_of_disjoint (appendix_inter_union_disjoint A B C bundle hAC hBC),
    Finset.card_union_of_disjoint (appendix_inter_disjoint A B bundle hAB)]

/-- An Appendix-A `T₁` agent evaluates a subbundle by the source's `P₁`
formula. -/
theorem appendix_cost_low_bundle
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C bundle : Finset Item)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hsubset : bundle ⊆ chores) (agent : Fin n) (hlow : agent.val < n / 2) :
    additiveChoreCost cost agent bundle =
      r * (bundle ∩ A).card + (bundle ∩ B).card + q * (bundle ∩ C).card := by
  conv_lhs => rw [appendix_partition_bundle A B C chores bundle hpartition hsubset]
  rw [additiveChoreCost_union cost agent (bundle ∩ A ∪ bundle ∩ B) (bundle ∩ C)
    (appendix_inter_union_disjoint A B C bundle hAC hBC)]
  rw [additiveChoreCost_union cost agent (bundle ∩ A) (bundle ∩ B)
    (appendix_inter_disjoint A B bundle hAB)]
  have hA : ∀ item ∈ bundle ∩ A, cost agent item = r := by
    intro item hitem
    exact (hcost agent item).1 (Finset.mem_inter.mp hitem).2
  have hB : ∀ item ∈ bundle ∩ B, cost agent item = 1 := by
    intro item hitem
    rw [(hcost agent item).2.1 (Finset.mem_inter.mp hitem).2]
    simp [hlow]
  have hC : ∀ item ∈ bundle ∩ C, cost agent item = q := by
    intro item hitem
    rw [(hcost agent item).2.2 (Finset.mem_inter.mp hitem).2]
    simp [hlow]
  rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle ∩ A) r hA,
    additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle ∩ B) 1 hB,
    additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle ∩ C) q hC]
  simp only [nsmul_eq_mul]
  ring

/-- An Appendix-A `T₂` agent evaluates a subbundle by the source's `P₂`
formula. -/
theorem appendix_cost_high_bundle
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C bundle : Finset Item)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hsubset : bundle ⊆ chores) (agent : Fin n) (hhigh : n / 2 ≤ agent.val) :
    additiveChoreCost cost agent bundle =
      r * (bundle ∩ A).card + q * (bundle ∩ B).card + (bundle ∩ C).card := by
  conv_lhs => rw [appendix_partition_bundle A B C chores bundle hpartition hsubset]
  rw [additiveChoreCost_union cost agent (bundle ∩ A ∪ bundle ∩ B) (bundle ∩ C)
    (appendix_inter_union_disjoint A B C bundle hAC hBC)]
  rw [additiveChoreCost_union cost agent (bundle ∩ A) (bundle ∩ B)
    (appendix_inter_disjoint A B bundle hAB)]
  have hA : ∀ item ∈ bundle ∩ A, cost agent item = r := by
    intro item hitem
    exact (hcost agent item).1 (Finset.mem_inter.mp hitem).2
  have hB : ∀ item ∈ bundle ∩ B, cost agent item = q := by
    intro item hitem
    rw [(hcost agent item).2.1 (Finset.mem_inter.mp hitem).2]
    simp [show ¬ agent.val < n / 2 by omega]
  have hC : ∀ item ∈ bundle ∩ C, cost agent item = 1 := by
    intro item hitem
    rw [(hcost agent item).2.2 (Finset.mem_inter.mp hitem).2]
    simp [show ¬ agent.val < n / 2 by omega]
  rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle ∩ A) r hA,
    additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle ∩ B) q hB,
    additiveChoreCost_eq_card_nsmul_of_constant cost agent (bundle ∩ C) 1 hC]
  simp only [nsmul_eq_mul]
  ring

/-- Every agent assigns total cost `(n + 1) r` to the entire Appendix-A
chore pool.  This is the averaging identity used before the first EFX
contradiction. -/
theorem appendix_total_cost
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2) (agent : Fin n) :
    additiveChoreCost cost agent chores = (n + 1 : ℕ) * r := by
  have hAsub : A ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hitem)))
  have hBsub : B ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hitem)))
  have hCsub : C ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inr hitem)
  have hAinter : chores ∩ A = A := Finset.inter_eq_right.mpr hAsub
  have hBinter : chores ∩ B = B := Finset.inter_eq_right.mpr hBsub
  have hCinter : chores ∩ C = C := Finset.inter_eq_right.mpr hCsub
  have hn : 1 ≤ n := by
    have := agent.isLt
    omega
  by_cases hlow : agent.val < n / 2
  · rw [appendix_cost_low_bundle n Item r q cost chores A B C chores hAB hAC hBC
      hpartition hcost (by rfl) agent hlow, hAinter, hBinter, hCinter,
      hAcard, hBcard, hCcard, hr]
    push_cast
    rw [Nat.cast_sub hn]
    ring
  · have hhigh : n / 2 ≤ agent.val := by omega
    rw [appendix_cost_high_bundle n Item r q cost chores A B C chores hAB hAC hBC
      hpartition hcost (by rfl) agent hhigh, hAinter, hBinter, hCinter,
      hAcard, hBcard, hCcard, hr]
    push_cast
    rw [Nat.cast_sub hn]
    ring

/-- Under the Appendix-A parameters, every observer has a bundle of cost
strictly below `2r` in any complete allocation.  This is the paper's
averaging bound `p₁,p₂ < 2r`, phrased in the allocation form used by EFX. -/
theorem appendix_exists_bundle_cost_lt_two_r
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item)
    (hn : 4 ≤ n) (hq : q = appendixQ n)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (halloc : IsAllocationOf allocation chores) (agent : Fin n) :
    ∃ owner, additiveChoreCost cost agent (allocation owner) < 2 * r := by
  have hspos : (0 : ℝ) < appendixS n := by
    simp only [appendixS]
    positivity
  have hqplus : 0 < q + 1 := by
    rw [hq]
    simp only [appendixQ]
    linarith
  have hrpos : 0 < r := by
    rw [hr]
    positivity
  by_contra hno
  push Not at hno
  have hsum := sum_additiveChoreCost_allocation_eq_additiveChoreCost cost agent allocation
    chores halloc
  rw [appendix_total_cost n Item r q cost chores A B C hAcard hBcard hCcard hAB hAC hBC
    hpartition hcost hr agent] at hsum
  have hlower : (Finset.univ : Finset (Fin n)).sum (fun _ => 2 * r) ≤
      Finset.univ.sum (fun owner => additiveChoreCost cost agent (allocation owner)) := by
    exact Finset.sum_le_sum fun owner _ => hno owner
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at hlower
  norm_num at hlower
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- A bundle's cost is at least `r` times the number of A-items it contains.
All terms retained in this inequality are explicit source table entries. -/
theorem appendix_cost_ge_r_mul_A_card
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C bundle : Finset Item)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hqnonneg : 0 ≤ q)
    (hsubset : bundle ⊆ chores) (agent : Fin n) :
    r * (bundle ∩ A).card ≤ additiveChoreCost cost agent bundle := by
  by_cases hlow : agent.val < n / 2
  · rw [appendix_cost_low_bundle n Item r q cost chores A B C bundle hAB hAC hBC
      hpartition hcost hsubset agent hlow]
    have hBnonneg : 0 ≤ ((bundle ∩ B).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ C).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hhigh : n / 2 ≤ agent.val := by omega
    rw [appendix_cost_high_bundle n Item r q cost chores A B C bundle hAB hAC hBC
      hpartition hcost hsubset agent hhigh]
    have hBnonneg : 0 ≤ ((bundle ∩ B).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ C).card : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- A bundle with one A-item and at least one further item costs at least
`r + 1` to every Appendix-A agent. -/
theorem appendix_cost_ge_r_add_one_of_one_A_and_card_ge_two
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C bundle : Finset Item)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hqone : 1 ≤ q) (hsubset : bundle ⊆ chores) (agent : Fin n)
    (hAone : (bundle ∩ A).card = 1) (hcard : 2 ≤ bundle.card) :
    r + 1 ≤ additiveChoreCost cost agent bundle := by
  have hpartitionCard := appendix_partition_card A B C chores bundle hAB hAC hBC hpartition hsubset
  have hBCpositive : 1 ≤ (bundle ∩ B).card + (bundle ∩ C).card := by
    rw [hAone] at hpartitionCard
    omega
  by_cases hlow : agent.val < n / 2
  · rw [appendix_cost_low_bundle n Item r q cost chores A B C bundle hAB hAC hBC
      hpartition hcost hsubset agent hlow, hAone]
    norm_num
    have hBnonneg : 0 ≤ ((bundle ∩ B).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ C).card : ℝ) := Nat.cast_nonneg _
    have hBCpositiveReal : 1 ≤ ((bundle ∩ B).card : ℝ) + ((bundle ∩ C).card : ℝ) := by
      exact_mod_cast hBCpositive
    have hCsmall : ((bundle ∩ C).card : ℝ) ≤ q * (bundle ∩ C).card :=
      by simpa using mul_le_mul_of_nonneg_right hqone hCnonneg
    nlinarith
  · have hhigh : n / 2 ≤ agent.val := by omega
    rw [appendix_cost_high_bundle n Item r q cost chores A B C bundle hAB hAC hBC
      hpartition hcost hsubset agent hhigh, hAone]
    norm_num
    have hBnonneg : 0 ≤ ((bundle ∩ B).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle ∩ C).card : ℝ) := Nat.cast_nonneg _
    have hBCpositiveReal : 1 ≤ ((bundle ∩ B).card : ℝ) + ((bundle ∩ C).card : ℝ) := by
      exact_mod_cast hBCpositive
    have hBsmall : ((bundle ∩ B).card : ℝ) ≤ q * (bundle ∩ B).card :=
      by simpa using mul_le_mul_of_nonneg_right hqone hBnonneg
    nlinarith

/-- The first branch of the Appendix-A argument: an EFX bundle cannot contain
three A-items, because deleting one still leaves cost at least `2r` while
the averaging lemma supplies a comparison bundle of cost below `2r`. -/
theorem appendix_no_three_A_items
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item)
    (hn : 4 ≤ n) (hq : q = appendixQ n)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (agent : Fin n) :
    (allocation agent ∩ A).card ≤ 2 := by
  have hqpos : 0 < q := by
    rw [hq]
    simp only [appendixQ]
    positivity
  have hrpos : 0 < r := by
    have hspos : (0 : ℝ) < appendixS n := by
      simp only [appendixS]
      positivity
    have hqone : 0 < q + 1 := by linarith
    rw [hr]
    positivity
  by_contra hnot
  have hthree : 3 ≤ (allocation agent ∩ A).card := by omega
  obtain ⟨item, hitem⟩ := Finset.card_pos.mp (by omega : 0 < (allocation agent ∩ A).card)
  have hitemBundle : item ∈ allocation agent := (Finset.mem_inter.mp hitem).1
  have hitemA : item ∈ A := (Finset.mem_inter.mp hitem).2
  obtain ⟨other, hother⟩ := appendix_exists_bundle_cost_lt_two_r n Item r q cost chores A B C
    allocation hn hq hAcard hBcard hCcard hAB hAC hBC hpartition hcost hr halloc agent
  have heraseA : (allocation agent \ {item}) ∩ A = (allocation agent ∩ A).erase item := by
    ext candidate
    simp [and_left_comm, and_comm]
  have htwo : 2 ≤ ((allocation agent \ {item}) ∩ A).card := by
    rw [heraseA, Finset.card_erase_of_mem hitem]
    omega
  have heraseSubset : allocation agent \ {item} ⊆ chores := by
    intro candidate hcandidate
    exact halloc.1 agent candidate (Finset.sdiff_subset hcandidate)
  have hremaining : 2 * r ≤ additiveChoreCost cost agent (allocation agent \ {item}) := by
    have hlower := appendix_cost_ge_r_mul_A_card n Item r q cost chores A B C
      (allocation agent \ {item}) hAB hAC hBC hpartition hcost hqpos.le
      heraseSubset agent
    have htwoReal : (2 : ℝ) ≤ ((allocation agent \ {item} ∩ A).card : ℝ) :=
      Nat.cast_le.mpr htwo
    nlinarith
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  have hefxItem := (hefx agent other).resolve_left hnonempty item hitemBundle
  linarith

/-- The second easy branch of the Appendix-A argument: if a bundle has
exactly two A-items, it cannot contain any further item.  Deleting that
further item would still leave two A-items and violate the same averaging
comparison as in `appendix_no_three_A_items`. -/
theorem appendix_two_A_bundle_subset_A
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item)
    (hn : 4 ≤ n) (hq : q = appendixQ n)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (agent : Fin n) (hAtwo : (allocation agent ∩ A).card = 2) :
    allocation agent ⊆ A := by
  have hqpos : 0 < q := by
    rw [hq]
    simp only [appendixQ]
    positivity
  have hrpos : 0 < r := by
    have hspos : (0 : ℝ) < appendixS n := by
      simp only [appendixS]
      positivity
    have hqone : 0 < q + 1 := by linarith
    rw [hr]
    positivity
  intro item hitemBundle
  by_contra hitemA
  obtain ⟨other, hother⟩ := appendix_exists_bundle_cost_lt_two_r n Item r q cost chores A B C
    allocation hn hq hAcard hBcard hCcard hAB hAC hBC hpartition hcost hr halloc agent
  have heraseA : (allocation agent \ {item}) ∩ A = allocation agent ∩ A := by
    ext candidate
    constructor
    · intro hcandidate
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hcandidate).1).1,
          (Finset.mem_inter.mp hcandidate).2⟩
    · intro hcandidate
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hcandidate).2⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hcandidate).1, ?_⟩
      intro heq
      have hEq : candidate = item := Finset.mem_singleton.mp heq
      subst candidate
      exact hitemA (Finset.mem_inter.mp hcandidate).2
  have heraseSubset : allocation agent \ {item} ⊆ chores := by
    intro candidate hcandidate
    exact halloc.1 agent candidate (Finset.sdiff_subset hcandidate)
  have hremaining : 2 * r ≤ additiveChoreCost cost agent (allocation agent \ {item}) := by
    have hlower := appendix_cost_ge_r_mul_A_card n Item r q cost chores A B C
      (allocation agent \ {item}) hAB hAC hBC hpartition hcost hqpos.le heraseSubset agent
    rw [heraseA, hAtwo] at hlower
    norm_num at hlower
    nlinarith
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  have hefxItem := (hefx agent other).resolve_left hnonempty item hitemBundle
  linarith

/-- Once the easy branches have forced a two-A bundle to contain no other
items, its owner assigns it exact cost `2r`. -/
theorem appendix_two_A_bundle_cost
    (n : ℕ) (Item : Type) [DecidableEq Item] (r : ℝ)
    (cost : ChoreCost (Fin n) Item) (A : Finset Item)
    (allocation : Allocation (Fin n) Item) (agent : Fin n)
    (hcostA : ∀ item ∈ A, cost agent item = r)
    (hsubsetA : allocation agent ⊆ A) (hAtwo : (allocation agent ∩ A).card = 2) :
    additiveChoreCost cost agent (allocation agent) = 2 * r := by
  have hinter : allocation agent ∩ A = allocation agent := Finset.inter_eq_left.mpr hsubsetA
  have hcard : (allocation agent).card = 2 := by
    rw [← hinter]
    exact hAtwo
  rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation agent) r]
  · rw [hcard]
    norm_num [nsmul_eq_mul]
  · intro item hitem
    exact hcostA item (hsubsetA hitem)

/-- EFX from a pure two-A bundle forces every comparison bundle to have cost
at least `r` for that owner. -/
theorem appendix_two_A_efx_lower_bound
    (n : ℕ) (Item : Type) [DecidableEq Item] (r : ℝ)
    (cost : ChoreCost (Fin n) Item) (A : Finset Item)
    (allocation : Allocation (Fin n) Item) (agent : Fin n)
    (hcostA : ∀ item ∈ A, cost agent item = r)
    (hsubsetA : allocation agent ⊆ A) (hAtwo : (allocation agent ∩ A).card = 2)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∀ other, r ≤ additiveChoreCost cost agent (allocation other) := by
  have hown := appendix_two_A_bundle_cost n Item r cost A allocation agent hcostA hsubsetA hAtwo
  have hpositive : 0 < (allocation agent ∩ A).card := by omega
  obtain ⟨item, hitem⟩ := Finset.card_pos.mp hpositive
  have hitemBundle : item ∈ allocation agent := (Finset.mem_inter.mp hitem).1
  have hitemA : item ∈ A := (Finset.mem_inter.mp hitem).2
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  intro other
  have hefxItem := (hefx agent other).resolve_left hnonempty item hitemBundle
  rw [additiveChoreCost_erase cost agent (allocation agent) item hitemBundle, hown,
    hcostA item hitemA] at hefxItem
  linarith

/-- Equality in the Appendix-A total-cost averaging bound is rigid: after one
bundle has cost `2r`, if every bundle is at least `r`, then every other bundle
has cost exactly `r`. -/
theorem appendix_other_cost_eq_r_of_two_r_bundle
    (n : ℕ) (f : Fin n → ℝ) (r : ℝ) (agent : Fin n)
    (hn : 2 ≤ n) (hsum : Finset.univ.sum f = (n + 1 : ℕ) * r)
    (hself : f agent = 2 * r) (hlower : ∀ owner, r ≤ f owner) :
    ∀ owner, owner ≠ agent → f owner = r := by
  intro owner howner
  have hownerMem : owner ∈ (Finset.univ.erase agent : Finset (Fin n)) := by
    simp [howner]
  have hsumErase : (Finset.univ.erase agent : Finset (Fin n)).sum f + f agent =
      Finset.univ.sum f :=
    Finset.sum_erase_add Finset.univ f (Finset.mem_univ agent)
  have hsumRest : ((Finset.univ.erase agent).erase owner : Finset (Fin n)).sum f + f owner =
      (Finset.univ.erase agent : Finset (Fin n)).sum f :=
    Finset.sum_erase_add (Finset.univ.erase agent) f hownerMem
  have hrestLower : ((Finset.univ.erase agent).erase owner : Finset (Fin n)).sum
      (fun _ => r) ≤ ((Finset.univ.erase agent).erase owner).sum f := by
    exact Finset.sum_le_sum fun remaining _ => hlower remaining
  have hcard : ((Finset.univ.erase agent).erase owner : Finset (Fin n)).card = n - 2 := by
    simp [howner]
    omega
  rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub hn] at hrestLower
  have hupper : f owner ≤ r := by
    rw [hsum, hself] at hsumErase
    push_cast at hsumErase
    have hsumErase' : (Finset.univ.erase agent : Finset (Fin n)).sum f =
        ((n : ℝ) - 1) * r := by
      calc
        (Finset.univ.erase agent : Finset (Fin n)).sum f = (n : ℝ) * r + r - 2 * r := by
          linarith
        _ = ((n : ℝ) - 1) * r := by ring
    have hsumIdentity : ((Finset.univ.erase agent).erase owner : Finset (Fin n)).sum f +
        f owner = ((n : ℝ) - 2) * r + r := by
      calc
        ((Finset.univ.erase agent).erase owner : Finset (Fin n)).sum f + f owner =
            (Finset.univ.erase agent : Finset (Fin n)).sum f := hsumRest
        _ = ((n : ℝ) - 1) * r := hsumErase'
        _ = ((n : ℝ) - 2) * r + r := by ring
    by_contra hnot
    have hstrict : ((n : ℝ) - 2) * r + r <
        ((Finset.univ.erase agent).erase owner : Finset (Fin n)).sum f + f owner :=
      add_lt_add_of_le_of_lt hrestLower (lt_of_not_ge hnot)
    rw [hsumIdentity] at hstrict
    exact (lt_irrefl _ hstrict)
  exact le_antisymm hupper (hlower owner)

/-- If one bundle contains two A-items, the `n - 1` A-items cannot meet all
of the other `n - 1` bundles.  This is the allocation-counting step that
produces an A-free comparison bundle in the final Appendix-A branch. -/
theorem appendix_exists_a_free_other_bundle
    (n : ℕ) (Item : Type) [DecidableEq Item]
    (chores A : Finset Item) (allocation : Allocation (Fin n) Item)
    (hAcard : A.card = n - 1) (hAsub : A ⊆ chores)
    (halloc : IsAllocationOf allocation chores)
    (agent : Fin n) (hAtwo : (allocation agent ∩ A).card = 2) :
    ∃ owner, owner ≠ agent ∧ allocation owner ∩ A = ∅ := by
  by_contra hno
  have hsum := sum_card_inter_allocation_eq_card_inter allocation chores A halloc
  rw [Finset.inter_eq_right.mpr hAsub, hAcard] at hsum
  have hsumErase : (Finset.univ.erase agent : Finset (Fin n)).sum
      (fun owner => (allocation owner ∩ A).card) + (allocation agent ∩ A).card =
      Finset.univ.sum (fun owner => (allocation owner ∩ A).card) :=
    Finset.sum_erase_add Finset.univ (fun owner => (allocation owner ∩ A).card)
      (Finset.mem_univ agent)
  rw [hAtwo, hsum] at hsumErase
  have hpositive : ∀ owner ∈ (Finset.univ.erase agent : Finset (Fin n)),
      1 ≤ (allocation owner ∩ A).card := by
    intro owner howner
    have hne : owner ≠ agent := Finset.mem_erase.mp howner |>.1
    have hnonempty : (allocation owner ∩ A).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      apply hno
      exact ⟨owner, hne, hempty⟩
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr hnonempty)
  have hlower : (Finset.univ.erase agent : Finset (Fin n)).sum (fun _ => 1) ≤
      (Finset.univ.erase agent).sum (fun owner => (allocation owner ∩ A).card) := by
    exact Finset.sum_le_sum hpositive
  have hcard : (Finset.univ.erase agent : Finset (Fin n)).card = n - 1 := by simp
  rw [Finset.sum_const, hcard] at hlower
  norm_num at hlower
  omega

/-- Source-faithful proof of the first Appendix-A proposition.  The proof
follows the source split exactly: three A-items contradict the `2r` average,
two A-items plus another chore do the same, and a pure two-A bundle forces an
A-free bundle of exact cost `r`, which the modular lemma rules out. -/
theorem appendix_no_two_A_items_proof :
    ∀ (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
      (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
      (allocation : Allocation (Fin n) Item),
      4 ≤ n → q = appendixQ n → r = (appendixS n : ℝ) * (q + 1) / 2 →
      A.card = n - 1 → B.card = appendixS n → C.card = appendixS n →
      Disjoint A B → Disjoint A C → Disjoint B C → A ∪ B ∪ C = chores →
      (∀ (agent : Fin n) item,
        (item ∈ A → cost agent item = r) ∧
        (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
        (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1)) →
      IsAllocationOf allocation chores →
      EFXForChores (additiveChoreCost cost) allocation →
      ∀ agent, (allocation agent ∩ A).card ≤ 1 := by
  intro n Item _ r q cost chores A B C allocation hn hq hr hAcard hBcard hCcard hAB hAC hBC
    hpartition hcost halloc hefx agent
  by_contra hnot
  have hAtLeastTwo : 2 ≤ (allocation agent ∩ A).card := by omega
  have hAtMostTwo := appendix_no_three_A_items n Item r q cost chores A B C allocation hn hq
    hAcard hBcard hCcard hAB hAC hBC hpartition hcost hr halloc hefx agent
  have hAtwo : (allocation agent ∩ A).card = 2 := by omega
  have hsubsetA := appendix_two_A_bundle_subset_A n Item r q cost chores A B C allocation hn hq
    hAcard hBcard hCcard hAB hAC hBC hpartition hcost hr halloc hefx agent hAtwo
  have hcostA : ∀ item ∈ A, cost agent item = r := by
    intro item hitem
    exact (hcost agent item).1 hitem
  have hself := appendix_two_A_bundle_cost n Item r cost A allocation agent hcostA hsubsetA hAtwo
  have hlower := appendix_two_A_efx_lower_bound n Item r cost A allocation agent hcostA hsubsetA
    hAtwo hefx
  have hsum : Finset.univ.sum (fun owner => additiveChoreCost cost agent (allocation owner)) =
      (n + 1 : ℕ) * r := by
    calc
      Finset.univ.sum (fun owner => additiveChoreCost cost agent (allocation owner)) =
          additiveChoreCost cost agent chores :=
        sum_additiveChoreCost_allocation_eq_additiveChoreCost cost agent allocation chores halloc
      _ = (n + 1 : ℕ) * r := appendix_total_cost n Item r q cost chores A B C hAcard hBcard
        hCcard hAB hAC hBC hpartition hcost hr agent
  have hnTwo : 2 ≤ n := by omega
  have hotherCost := appendix_other_cost_eq_r_of_two_r_bundle n
    (fun owner => additiveChoreCost cost agent (allocation owner)) r agent hnTwo hsum hself hlower
  have hAsub : A ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hitem)))
  obtain ⟨other, hotherNe, hfree⟩ := appendix_exists_a_free_other_bundle n Item chores A allocation
    hAcard hAsub halloc agent hAtwo
  have hotherExact : additiveChoreCost cost agent (allocation other) = r :=
    hotherCost other hotherNe
  have hrNat : r = (appendixRNat n : ℝ) := by
    calc
      r = (appendixS n : ℝ) * (q + 1) / 2 := hr
      _ = (appendixS n : ℝ) * ((appendixQ n : ℝ) + 1) / 2 := by rw [hq]
      _ = appendixRNat n := appendix_r_formula n
  have hbundleSubset : allocation other ⊆ chores := by
    intro item hitem
    exact halloc.1 other item hitem
  have hBbound : (allocation other ∩ B).card ≤ appendixS n := by
    calc
      (allocation other ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      _ = appendixS n := hBcard
  have hCbound : (allocation other ∩ C).card ≤ appendixS n := by
    calc
      (allocation other ∩ C).card ≤ C.card := Finset.card_le_card Finset.inter_subset_right
      _ = appendixS n := hCcard
  by_cases hlow : agent.val < n / 2
  · have hformula := appendix_cost_low_bundle n Item r q cost chores A B C (allocation other)
      hAB hAC hBC hpartition hcost hbundleSubset agent hlow
    rw [hfree, hotherExact] at hformula
    norm_num at hformula
    exact (appendix_no_exact_a_free_cost_real n (allocation other ∩ B).card
      (allocation other ∩ C).card hBbound) (by
        calc
          ((allocation other ∩ B).card : ℝ) + (appendixQ n : ℝ) *
              (allocation other ∩ C).card =
              ((allocation other ∩ B).card : ℝ) + q * (allocation other ∩ C).card := by
                rw [hq]
          _ = r := hformula.symm
          _ = appendixRNat n := hrNat)
  · have hhigh : n / 2 ≤ agent.val := by omega
    have hformula := appendix_cost_high_bundle n Item r q cost chores A B C (allocation other)
      hAB hAC hBC hpartition hcost hbundleSubset agent hhigh
    rw [hfree, hotherExact] at hformula
    norm_num at hformula
    exact (appendix_no_exact_a_free_cost_real n (allocation other ∩ C).card
      (allocation other ∩ B).card hCbound) (by
        calc
          ((allocation other ∩ C).card : ℝ) + (appendixQ n : ℝ) *
              (allocation other ∩ B).card =
              q * (allocation other ∩ B).card + (allocation other ∩ C).card := by
                rw [hq]
                ring
          _ = r := hformula.symm
          _ = appendixRNat n := hrNat)

/-- After the no-two-A proposition, the `n - 1` A-items occupy exactly one
item in every bundle except for a unique A-free bundle. -/
theorem appendix_a_item_distribution
    (n : ℕ) (Item : Type) [DecidableEq Item]
    (chores A : Finset Item) (allocation : Allocation (Fin n) Item)
    (hn : 4 ≤ n) (hAcard : A.card = n - 1) (hAsub : A ⊆ chores)
    (halloc : IsAllocationOf allocation chores)
    (hatMostOne : ∀ agent, (allocation agent ∩ A).card ≤ 1) :
    ∃ zero, (allocation zero ∩ A).card = 0 ∧
      ∀ other, other ≠ zero → (allocation other ∩ A).card = 1 := by
  let counts : Fin n → ℕ := fun agent => (allocation agent ∩ A).card
  have hsum : Finset.univ.sum counts = n - 1 := by
    dsimp [counts]
    rw [sum_card_inter_allocation_eq_card_inter allocation chores A halloc,
      Finset.inter_eq_right.mpr hAsub, hAcard]
  have hexists : ∃ zero, counts zero = 0 := by
    by_contra hno
    have hpositive : ∀ owner, 1 ≤ counts owner := by
      intro owner
      apply Nat.one_le_iff_ne_zero.mpr
      intro hzero
      apply hno
      exact ⟨owner, hzero⟩
    have hlower : (Finset.univ : Finset (Fin n)).sum (fun _ => 1) ≤
        Finset.univ.sum counts := Finset.sum_le_sum fun owner _ => hpositive owner
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum] at hlower
    norm_num at hlower
    omega
  obtain ⟨zero, hzero⟩ := hexists
  refine ⟨zero, hzero, ?_⟩
  intro other hother
  have hnonzero : counts other ≠ 0 := by
    intro hotherzero
    have hzeroNe : zero ≠ other := Ne.symm hother
    have hzeroMem : zero ∈ (Finset.univ.erase other : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨hzeroNe, Finset.mem_univ _⟩
    have hsumEraseOther : (Finset.univ.erase other : Finset (Fin n)).sum counts + counts other =
        Finset.univ.sum counts :=
      Finset.sum_erase_add Finset.univ counts (Finset.mem_univ other)
    have hsumEraseZero : ((Finset.univ.erase other).erase zero : Finset (Fin n)).sum counts +
        counts zero = (Finset.univ.erase other : Finset (Fin n)).sum counts :=
      Finset.sum_erase_add (Finset.univ.erase other) counts hzeroMem
    rw [hotherzero, hsum] at hsumEraseOther
    rw [hzero] at hsumEraseZero
    have hupper : ((Finset.univ.erase other).erase zero : Finset (Fin n)).sum counts ≤
        ((Finset.univ.erase other).erase zero).sum (fun _ => 1) := by
      exact Finset.sum_le_sum fun owner _ => hatMostOne owner
    have hcard : ((Finset.univ.erase other).erase zero : Finset (Fin n)).card = n - 2 := by
      simp [hzeroNe]
      omega
    rw [Finset.sum_const, hcard] at hupper
    norm_num at hupper
    omega
  have hpositive : 1 ≤ counts other := Nat.one_le_iff_ne_zero.mpr hnonzero
  exact Nat.le_antisymm (hatMostOne other) hpositive

/-- If the group-one minimum `p₁` is below `r`, then a group-one agent whose
bundle contains an A-item must receive that A-item alone.  Removing any other
item would leave an A-cost of at least `r` and violate EFX against a
`p₁`-minimizing bundle. -/
theorem appendix_low_A_bundle_subset_A_of_p1_lt
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P1 : Bundle Item → ℝ) (p1 : ℝ)
    (hq : q = appendixQ n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hcostP1 : ∀ (agent : Fin n), agent.val < n / 2 → additiveChoreCost cost agent = P1)
    (hmin : ∃ owner, P1 (allocation owner) = p1)
    (hp1lt : p1 < r) (agent : Fin n) (hlow : agent.val < n / 2)
    (hAone : (allocation agent ∩ A).card = 1) :
    allocation agent ⊆ A := by
  have hqpos : 0 < q := by
    rw [hq]
    simp only [appendixQ]
    positivity
  obtain ⟨minimum, hminimum⟩ := hmin
  intro item hitemBundle
  by_contra hitemA
  have heraseA : (allocation agent \ {item}) ∩ A = allocation agent ∩ A := by
    ext candidate
    constructor
    · intro hcandidate
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hcandidate).1).1,
          (Finset.mem_inter.mp hcandidate).2⟩
    · intro hcandidate
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hcandidate).2⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hcandidate).1, ?_⟩
      intro heq
      have hEq : candidate = item := Finset.mem_singleton.mp heq
      subst candidate
      exact hitemA (Finset.mem_inter.mp hcandidate).2
  have heraseSubset : allocation agent \ {item} ⊆ chores := by
    intro candidate hcandidate
    exact halloc.1 agent candidate (Finset.sdiff_subset hcandidate)
  have hremaining : r ≤ additiveChoreCost cost agent (allocation agent \ {item}) := by
    have hlower := appendix_cost_ge_r_mul_A_card n Item r q cost chores A B C
      (allocation agent \ {item}) hAB hAC hBC hpartition hcost hqpos.le heraseSubset agent
    rw [heraseA, hAone] at hlower
    norm_num at hlower
    exact hlower
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  have hefxItem := (hefx agent minimum).resolve_left hnonempty item hitemBundle
  rw [hcostP1 agent hlow] at hremaining
  rw [hcostP1 agent hlow, hminimum] at hefxItem
  linarith

/-- The low group contains an agent distinct from any prescribed owner when
`n ≥ 4`; the explicit `0/1` choice avoids a hidden cardinality argument in
the lower-bound proof. -/
theorem appendix_exists_low_agent_ne (n : ℕ) (hn : 4 ≤ n) (owner : Fin n) :
    ∃ agent : Fin n, agent ≠ owner ∧ agent.val < n / 2 := by
  let first : Fin n := ⟨0, by omega⟩
  let second : Fin n := ⟨1, by omega⟩
  by_cases howner : owner = first
  · subst owner
    refine ⟨second, ?_, ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      dsimp [first, second] at hval
      omega
    · dsimp [second]
      omega
  · refine ⟨first, ?_, ?_⟩
    · intro heq
      exact howner heq.symm
    · dsimp [first]
      omega

/-- Either group evaluates a singleton A-bundle at exactly `r`. -/
theorem appendix_group_formula_on_A_singleton
    (Item : Type) [DecidableEq Item] (r q : ℝ) (A B C bundle : Finset Item)
    (P : Bundle Item → ℝ)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hformula : ∀ bundle, P bundle = r * (bundle ∩ A).card +
      q * (bundle ∩ B).card + (bundle ∩ C).card)
  (hsubsetA : bundle ⊆ A) (hAone : (bundle ∩ A).card = 1) :
    P bundle = r := by
  have hBempty : bundle ∩ B = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp hAB (hsubsetA (Finset.mem_inter.mp hitem).1)
      (Finset.mem_inter.mp hitem).2
  have hCempty : bundle ∩ C = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp hAC (hsubsetA (Finset.mem_inter.mp hitem).1)
      (Finset.mem_inter.mp hitem).2
  rw [hformula, hAone, hBempty, hCempty]
  norm_num

/-- Once `p₂ ≤ r`, a high-group bundle containing its unique A-item can have
at most one further chore.  Otherwise deleting one non-A chore leaves cost at
least `r + 1`, contradicting EFX against a `p₂`-minimum bundle. -/
theorem appendix_high_A_bundle_card_le_two_of_p2_le
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P2 : Bundle Item → ℝ) (p2 : ℝ)
    (hq : q = appendixQ n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hcostP2 : ∀ (agent : Fin n), n / 2 ≤ agent.val → additiveChoreCost cost agent = P2)
    (hmin : ∃ owner, P2 (allocation owner) = p2)
    (hp2le : p2 ≤ r) (agent : Fin n) (hhigh : n / 2 ≤ agent.val)
    (hAone : (allocation agent ∩ A).card = 1) :
    (allocation agent).card ≤ 2 := by
  have hqone : 1 ≤ q := by
    rw [hq]
    simp only [appendixQ, appendixS, appendixT, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have ht : (0 : ℝ) ≤ ((n + 1) / 2 : ℕ) := Nat.cast_nonneg _
    linarith
  by_contra hnot
  have hthree : 3 ≤ (allocation agent).card := by omega
  have hnotSubset : ¬ allocation agent ⊆ A := by
    intro hsubsetA
    have hinter : allocation agent ∩ A = allocation agent := Finset.inter_eq_left.mpr hsubsetA
    rw [hinter] at hAone
    omega
  obtain ⟨item, hitemBundle, hitemA⟩ := Finset.not_subset.mp hnotSubset
  obtain ⟨minimum, hminimum⟩ := hmin
  have heraseA : (allocation agent \ {item}) ∩ A = allocation agent ∩ A := by
    ext candidate
    constructor
    · intro hcandidate
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hcandidate).1).1,
          (Finset.mem_inter.mp hcandidate).2⟩
    · intro hcandidate
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hcandidate).2⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hcandidate).1, ?_⟩
      intro heq
      have hEq : candidate = item := Finset.mem_singleton.mp heq
      subst candidate
      exact hitemA (Finset.mem_inter.mp hcandidate).2
  have heraseCard : 2 ≤ (allocation agent \ {item}).card := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitemBundle]
    omega
  have heraseSubset : allocation agent \ {item} ⊆ chores := by
    intro candidate hcandidate
    exact halloc.1 agent candidate (Finset.sdiff_subset hcandidate)
  have hremaining : r + 1 ≤ additiveChoreCost cost agent (allocation agent \ {item}) := by
    apply appendix_cost_ge_r_add_one_of_one_A_and_card_ge_two n Item r q cost chores A B C
      (allocation agent \ {item}) hAB hAC hBC hpartition hcost hqone heraseSubset agent
    · rwa [heraseA]
    · exact heraseCard
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  have hefxItem := (hefx agent minimum).resolve_left hnonempty item hitemBundle
  rw [hcostP2 agent hhigh] at hremaining
  rw [hcostP2 agent hhigh, hminimum] at hefxItem
  linarith

/-- The high group in the Appendix-A partition has the source cardinality
`ceil(n / 2) = (n + 1) / 2`. -/
theorem appendix_high_group_card (n : ℕ) :
    (Finset.univ.filter fun agent : Fin n => n / 2 ≤ agent.val).card = appendixT n := by
  let low : Finset (Fin n) := Finset.univ.filter fun agent => agent.val < n / 2
  have hlow : low.card = n / 2 := by
    dsimp [low]
    simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
      (Fin.card_filter_val_lt (n := n) (m := n / 2))
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun agent : Fin n => agent.val < n / 2)
  have hpartition' : low.card +
      (Finset.univ.filter fun agent : Fin n => n / 2 ≤ agent.val).card = n := by
    simpa only [low, Finset.card_univ, Fintype.card_fin, Nat.not_lt] using hpartition
  rw [hlow] at hpartition'
  simp only [appendixT]
  omega

/-- Across a feasible Appendix-A allocation, the B/C cardinalities in all
bundles sum to the `2s` non-A chores. -/
theorem appendix_sum_nonA_cards
    (n : ℕ) (Item : Type) [DecidableEq Item]
    (chores B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (hBcard : B.card = appendixS n) (hCcard : C.card = appendixS n)
    (hBsub : B ⊆ chores) (hCsub : C ⊆ chores)
    (halloc : IsAllocationOf allocation chores) :
    Finset.univ.sum (fun agent => (allocation agent ∩ B).card + (allocation agent ∩ C).card) =
      2 * appendixS n := by
  have hsumB := sum_card_inter_allocation_eq_card_inter allocation chores B halloc
  have hsumC := sum_card_inter_allocation_eq_card_inter allocation chores C halloc
  rw [Finset.inter_eq_right.mpr hBsub, hBcard] at hsumB
  rw [Finset.inter_eq_right.mpr hCsub, hCcard] at hsumC
  rw [Finset.sum_add_distrib, hsumB, hsumC]
  omega

/-- In the `p₁ < r` branch, all non-A chores outside the unique A-free bundle
fit into at most one slot per high agent.  Hence the A-free bundle contains at
least `2s - ceil(n/2)` non-A chores. -/
theorem appendix_a_free_nonA_card_lower_bound
    (n : ℕ) (Item : Type) [DecidableEq Item]
    (chores A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (zero : Fin n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hBcard : B.card = appendixS n) (hCcard : C.card = appendixS n)
    (halloc : IsAllocationOf allocation chores)
    (hAone : ∀ owner, owner ≠ zero → (allocation owner ∩ A).card = 1)
    (hlowSubset : ∀ owner, owner ≠ zero → owner.val < n / 2 → allocation owner ⊆ A)
    (hhighCard : ∀ owner, owner ≠ zero → n / 2 ≤ owner.val → (allocation owner).card ≤ 2) :
    2 * appendixS n - appendixT n ≤
      (allocation zero ∩ B).card + (allocation zero ∩ C).card := by
  let nonA : Fin n → ℕ := fun owner =>
    (allocation owner ∩ B).card + (allocation owner ∩ C).card
  have hBsub : B ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hitem)))
  have hCsub : C ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inr hitem)
  have htotal : Finset.univ.sum nonA = 2 * appendixS n := by
    exact appendix_sum_nonA_cards n Item chores B C allocation hBcard hCcard hBsub hCsub halloc
  let rest : Finset (Fin n) := Finset.univ.erase zero
  have hrestBound : rest.sum nonA ≤ rest.sum
      (fun owner => if n / 2 ≤ owner.val then 1 else 0) := by
    apply Finset.sum_le_sum
    intro owner howner
    have hne : owner ≠ zero := Finset.mem_erase.mp howner |>.1
    by_cases hhigh : n / 2 ≤ owner.val
    · have hsubset : allocation owner ⊆ chores := by
        intro item hitem
        exact halloc.1 owner item hitem
      have hpart := appendix_partition_card A B C chores (allocation owner) hAB hAC hBC
        hpartition hsubset
      have hA := hAone owner hne
      have hcard := hhighCard owner hne hhigh
      change nonA owner ≤ if n / 2 ≤ owner.val then 1 else 0
      rw [if_pos hhigh]
      dsimp [nonA]
      omega
    · have hlow : owner.val < n / 2 := by omega
      have hsubsetA := hlowSubset owner hne hlow
      have hBempty : allocation owner ∩ B = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro item hitem
        exact Finset.disjoint_left.mp hAB (hsubsetA (Finset.mem_inter.mp hitem).1)
          (Finset.mem_inter.mp hitem).2
      have hCempty : allocation owner ∩ C = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro item hitem
        exact Finset.disjoint_left.mp hAC (hsubsetA (Finset.mem_inter.mp hitem).1)
          (Finset.mem_inter.mp hitem).2
      change nonA owner ≤ if n / 2 ≤ owner.val then 1 else 0
      rw [if_neg hhigh]
      dsimp [nonA]
      rw [hBempty, hCempty]
      norm_num
  have hrestFilter : rest.sum (fun owner => if n / 2 ≤ owner.val then 1 else 0) =
      (rest.filter fun owner => n / 2 ≤ owner.val).card := by
    exact Finset.sum_boole (fun owner : Fin n => n / 2 ≤ owner.val) rest
  have hfilterSub : rest.filter (fun owner => n / 2 ≤ owner.val) ⊆
      Finset.univ.filter (fun owner => n / 2 ≤ owner.val) := by
    intro owner howner
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp howner).2⟩
  have hhighCount : (rest.filter fun owner => n / 2 ≤ owner.val).card ≤ appendixT n := by
    calc
      (rest.filter fun owner => n / 2 ≤ owner.val).card ≤
          (Finset.univ.filter fun owner : Fin n => n / 2 ≤ owner.val).card :=
        Finset.card_le_card hfilterSub
      _ = appendixT n := appendix_high_group_card n
  have hrestLe : rest.sum nonA ≤ appendixT n := by
    rw [hrestFilter] at hrestBound
    exact hrestBound.trans hhighCount
  have hsumErase : rest.sum nonA + nonA zero = Finset.univ.sum nonA := by
    dsimp [rest]
    exact Finset.sum_erase_add Finset.univ nonA (Finset.mem_univ zero)
  rw [htotal] at hsumErase
  change 2 * appendixS n - appendixT n ≤ nonA zero
  omega

/-- The source's B/C count lower bound makes the A-free bundle expensive for
the first group: it has `P₁` cost at least `s + (t + 1)q`. -/
theorem appendix_p1_a_free_bundle_lower_bound
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (P1 : Bundle Item → ℝ) (zero : Fin n)
    (hq : q = appendixQ n) (hBcard : B.card = appendixS n)
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card)
    (hzeroA : (allocation zero ∩ A).card = 0)
    (hnonA : 2 * appendixS n - appendixT n ≤
      (allocation zero ∩ B).card + (allocation zero ∩ C).card) :
    (appendixS n : ℝ) + (appendixT n + 1 : ℕ) * q ≤ P1 (allocation zero) := by
  have hqone : 1 ≤ q := by
    rw [hq]
    simp only [appendixQ, appendixS, appendixT, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have ht : (0 : ℝ) ≤ ((n + 1) / 2 : ℕ) := Nat.cast_nonneg _
    linarith
  have hBbound : (allocation zero ∩ B).card ≤ appendixS n := by
    calc
      (allocation zero ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      _ = appendixS n := hBcard
  have hnonA' : appendixS n + appendixT n + 1 ≤
      (allocation zero ∩ B).card + (allocation zero ∩ C).card := by
    have hs : appendixS n = 2 * appendixT n + 1 := rfl
    omega
  have hCbound : appendixT n + 1 ≤ (allocation zero ∩ C).card := by omega
  have hnonAreal : (appendixS n : ℝ) + (appendixT n : ℝ) + 1 ≤
      ((allocation zero ∩ B).card : ℝ) + ((allocation zero ∩ C).card : ℝ) := by
    exact_mod_cast hnonA'
  have hCboundReal : (appendixT n : ℝ) + 1 ≤ ((allocation zero ∩ C).card : ℝ) := by
    exact_mod_cast hCbound
  have hqminus : 0 ≤ q - 1 := by linarith
  have hproduct : (q - 1) * ((appendixT n : ℝ) + 1) ≤
      (q - 1) * ((allocation zero ∩ C).card : ℝ) :=
    mul_le_mul_of_nonneg_left hCboundReal hqminus
  rw [hP1, hzeroA]
  norm_num
  nlinarith

/-- The previous lower bound is strictly greater than `r` under the exact
Appendix-A parameter identities. -/
theorem appendix_p1_a_free_bundle_strictly_expensive
    (n : ℕ) (r q : ℝ) (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2) :
    r < (appendixS n : ℝ) + (appendixT n + 1 : ℕ) * q := by
  rw [hr, hq]
  simp only [appendixQ, appendixS, appendixT, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have ht : (0 : ℝ) ≤ ((n + 1) / 2 : ℕ) := Nat.cast_nonneg _
  ring_nf
  linarith

/-- Source-faithful first half of the second Appendix-A proposition. -/
theorem appendix_p1_lower_bound_proof
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P1 P2 : Bundle Item → ℝ) (p1 p2 : ℝ)
    (hn : 4 ≤ n) (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card)
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card)
    (hcostP1 : ∀ (agent : Fin n), agent.val < n / 2 → additiveChoreCost cost agent = P1)
    (hcostP2 : ∀ (agent : Fin n), n / 2 ≤ agent.val → additiveChoreCost cost agent = P2)
    (hmin1 : ∃ agent, P1 (allocation agent) = p1)
    (hmin2 : ∃ agent, P2 (allocation agent) = p2)
    (hmin2Lower : ∀ agent, p2 ≤ P2 (allocation agent)) :
    r ≤ p1 := by
  by_contra hnot
  have hp1lt : p1 < r := lt_of_not_ge hnot
  have hAtMost : ∀ agent, (allocation agent ∩ A).card ≤ 1 :=
    appendix_no_two_A_items_proof n Item r q cost chores A B C allocation hn hq hr hAcard hBcard
      hCcard hAB hAC hBC hpartition hcost halloc hefx
  have hAsub : A ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hitem)))
  obtain ⟨zero, hzeroA, hAone⟩ := appendix_a_item_distribution n Item chores A allocation hn
    hAcard hAsub halloc hAtMost
  obtain ⟨lowAgent, hlowNe, hlow⟩ := appendix_exists_low_agent_ne n hn zero
  have hlowSubset : ∀ owner, owner ≠ zero → owner.val < n / 2 → allocation owner ⊆ A := by
    intro owner howner hownerLow
    exact appendix_low_A_bundle_subset_A_of_p1_lt n Item r q cost chores A B C allocation P1 p1
      hq hAB hAC hBC hpartition hcost halloc hefx hcostP1 hmin1 hp1lt owner hownerLow
      (hAone owner howner)
  have hlowASubset : allocation lowAgent ⊆ A := hlowSubset lowAgent hlowNe hlow
  have hlowP2 : P2 (allocation lowAgent) = r :=
    appendix_group_formula_on_A_singleton Item r q A B C (allocation lowAgent) P2 hAB hAC hP2
      hlowASubset (hAone lowAgent hlowNe)
  have hp2le : p2 ≤ r := hmin2Lower lowAgent |>.trans_eq hlowP2
  have hhighCard : ∀ owner, owner ≠ zero → n / 2 ≤ owner.val → (allocation owner).card ≤ 2 := by
    intro owner howner hownerHigh
    exact appendix_high_A_bundle_card_le_two_of_p2_le n Item r q cost chores A B C allocation P2 p2
      hq hAB hAC hBC hpartition hcost halloc hefx hcostP2 hmin2 hp2le owner hownerHigh
      (hAone owner howner)
  have hnonA := appendix_a_free_nonA_card_lower_bound n Item chores A B C allocation zero hAB hAC hBC
    hpartition hBcard hCcard halloc hAone hlowSubset hhighCard
  have hzeroLower := appendix_p1_a_free_bundle_lower_bound n Item r q A B C allocation P1 zero hq
    hBcard hP1 hzeroA hnonA
  have hzeroStrict := appendix_p1_a_free_bundle_strictly_expensive n r q hq hr
  obtain ⟨minimum, hminimum⟩ := hmin1
  by_cases hminimumZero : minimum = zero
  · subst minimum
    rw [hminimum] at hzeroLower
    linarith
  · have hminimumA := hAone minimum hminimumZero
    have hqnonneg : 0 ≤ q := by
      rw [hq]
      exact Nat.cast_nonneg _
    have hminimumLower : r ≤ P1 (allocation minimum) := by
      rw [hP1, hminimumA]
      norm_num
      have hBnonneg : 0 ≤ ((allocation minimum ∩ B).card : ℝ) := Nat.cast_nonneg _
      have hCnonneg : 0 ≤ ((allocation minimum ∩ C).card : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [hminimum] at hminimumLower
    linarith

/-- Symmetric singleton step for the `p₂ < r` branch. -/
theorem appendix_high_A_bundle_subset_A_of_p2_lt
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P2 : Bundle Item → ℝ) (p2 : ℝ)
    (hq : q = appendixQ n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hcostP2 : ∀ (agent : Fin n), n / 2 ≤ agent.val → additiveChoreCost cost agent = P2)
    (hmin : ∃ owner, P2 (allocation owner) = p2)
    (hp2lt : p2 < r) (agent : Fin n) (hhigh : n / 2 ≤ agent.val)
    (hAone : (allocation agent ∩ A).card = 1) :
    allocation agent ⊆ A := by
  have hqpos : 0 < q := by
    rw [hq]
    simp only [appendixQ]
    positivity
  obtain ⟨minimum, hminimum⟩ := hmin
  intro item hitemBundle
  by_contra hitemA
  have heraseA : (allocation agent \ {item}) ∩ A = allocation agent ∩ A := by
    ext candidate
    constructor
    · intro hcandidate
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hcandidate).1).1,
          (Finset.mem_inter.mp hcandidate).2⟩
    · intro hcandidate
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hcandidate).2⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hcandidate).1, ?_⟩
      intro heq
      have hEq : candidate = item := Finset.mem_singleton.mp heq
      subst candidate
      exact hitemA (Finset.mem_inter.mp hcandidate).2
  have heraseSubset : allocation agent \ {item} ⊆ chores := by
    intro candidate hcandidate
    exact halloc.1 agent candidate (Finset.sdiff_subset hcandidate)
  have hremaining : r ≤ additiveChoreCost cost agent (allocation agent \ {item}) := by
    have hlower := appendix_cost_ge_r_mul_A_card n Item r q cost chores A B C
      (allocation agent \ {item}) hAB hAC hBC hpartition hcost hqpos.le heraseSubset agent
    rw [heraseA, hAone] at hlower
    norm_num at hlower
    exact hlower
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  have hefxItem := (hefx agent minimum).resolve_left hnonempty item hitemBundle
  rw [hcostP2 agent hhigh] at hremaining
  rw [hcostP2 agent hhigh, hminimum] at hefxItem
  linarith

/-- The high group contains an agent distinct from any prescribed owner when
`n ≥ 4`; use the last two indices explicitly. -/
theorem appendix_exists_high_agent_ne (n : ℕ) (hn : 4 ≤ n) (owner : Fin n) :
    ∃ agent : Fin n, agent ≠ owner ∧ n / 2 ≤ agent.val := by
  let last : Fin n := ⟨n - 1, by omega⟩
  let penultimate : Fin n := ⟨n - 2, by omega⟩
  by_cases howner : owner = last
  · subst owner
    refine ⟨penultimate, ?_, ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      dsimp [last, penultimate] at hval
      omega
    · dsimp [penultimate]
      omega
  · refine ⟨last, ?_, ?_⟩
    · intro heq
      exact howner heq.symm
    · dsimp [last]
      omega

/-- The first-group formula also evaluates a singleton A-bundle at `r`. -/
theorem appendix_group_one_formula_on_A_singleton
    (Item : Type) [DecidableEq Item] (r q : ℝ) (A B C bundle : Finset Item)
    (P : Bundle Item → ℝ)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hformula : ∀ bundle, P bundle = r * (bundle ∩ A).card +
      (bundle ∩ B).card + q * (bundle ∩ C).card)
    (hsubsetA : bundle ⊆ A) (hAone : (bundle ∩ A).card = 1) :
    P bundle = r := by
  have hBempty : bundle ∩ B = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp hAB (hsubsetA (Finset.mem_inter.mp hitem).1)
      (Finset.mem_inter.mp hitem).2
  have hCempty : bundle ∩ C = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp hAC (hsubsetA (Finset.mem_inter.mp hitem).1)
      (Finset.mem_inter.mp hitem).2
  rw [hformula, hAone, hBempty, hCempty]
  norm_num

/-- Symmetric capacity step: once `p₁ ≤ r`, a low-group bundle with its
unique A-item has size at most two. -/
theorem appendix_low_A_bundle_card_le_two_of_p1_le
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P1 : Bundle Item → ℝ) (p1 : ℝ)
    (hq : q = appendixQ n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hcostP1 : ∀ (agent : Fin n), agent.val < n / 2 → additiveChoreCost cost agent = P1)
    (hmin : ∃ owner, P1 (allocation owner) = p1)
    (hp1le : p1 ≤ r) (agent : Fin n) (hlow : agent.val < n / 2)
    (hAone : (allocation agent ∩ A).card = 1) :
    (allocation agent).card ≤ 2 := by
  have hqone : 1 ≤ q := by
    rw [hq]
    simp only [appendixQ, appendixS, appendixT, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have ht : (0 : ℝ) ≤ ((n + 1) / 2 : ℕ) := Nat.cast_nonneg _
    linarith
  by_contra hnot
  have hthree : 3 ≤ (allocation agent).card := by omega
  have hnotSubset : ¬ allocation agent ⊆ A := by
    intro hsubsetA
    have hinter : allocation agent ∩ A = allocation agent := Finset.inter_eq_left.mpr hsubsetA
    rw [hinter] at hAone
    omega
  obtain ⟨item, hitemBundle, hitemA⟩ := Finset.not_subset.mp hnotSubset
  obtain ⟨minimum, hminimum⟩ := hmin
  have heraseA : (allocation agent \ {item}) ∩ A = allocation agent ∩ A := by
    ext candidate
    constructor
    · intro hcandidate
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hcandidate).1).1,
          (Finset.mem_inter.mp hcandidate).2⟩
    · intro hcandidate
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hcandidate).2⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hcandidate).1, ?_⟩
      intro heq
      have hEq : candidate = item := Finset.mem_singleton.mp heq
      subst candidate
      exact hitemA (Finset.mem_inter.mp hcandidate).2
  have heraseCard : 2 ≤ (allocation agent \ {item}).card := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitemBundle]
    omega
  have heraseSubset : allocation agent \ {item} ⊆ chores := by
    intro candidate hcandidate
    exact halloc.1 agent candidate (Finset.sdiff_subset hcandidate)
  have hremaining : r + 1 ≤ additiveChoreCost cost agent (allocation agent \ {item}) := by
    apply appendix_cost_ge_r_add_one_of_one_A_and_card_ge_two n Item r q cost chores A B C
      (allocation agent \ {item}) hAB hAC hBC hpartition hcost hqone heraseSubset agent
    · rwa [heraseA]
    · exact heraseCard
  have hnonempty : allocation agent ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemBundle
    simp at hitemBundle
  have hefxItem := (hefx agent minimum).resolve_left hnonempty item hitemBundle
  rw [hcostP1 agent hlow] at hremaining
  rw [hcostP1 agent hlow, hminimum] at hefxItem
  linarith

/-- The low group has `floor(n / 2) = n / 2` agents. -/
theorem appendix_low_group_card (n : ℕ) :
    (Finset.univ.filter fun agent : Fin n => agent.val < n / 2).card = n / 2 := by
  simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
    (Fin.card_filter_val_lt (n := n) (m := n / 2))

/-- Symmetric aggregate count for the `p₂ < r` branch.  It uses the fact that
the low group has no more agents than the high group. -/
theorem appendix_a_free_nonA_card_lower_bound_symmetric
    (n : ℕ) (Item : Type) [DecidableEq Item]
    (chores A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (zero : Fin n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hBcard : B.card = appendixS n) (hCcard : C.card = appendixS n)
    (halloc : IsAllocationOf allocation chores)
    (hAone : ∀ owner, owner ≠ zero → (allocation owner ∩ A).card = 1)
    (hhighSubset : ∀ owner, owner ≠ zero → n / 2 ≤ owner.val → allocation owner ⊆ A)
    (hlowCard : ∀ owner, owner ≠ zero → owner.val < n / 2 → (allocation owner).card ≤ 2) :
    2 * appendixS n - appendixT n ≤
      (allocation zero ∩ B).card + (allocation zero ∩ C).card := by
  let nonA : Fin n → ℕ := fun owner =>
    (allocation owner ∩ B).card + (allocation owner ∩ C).card
  have hBsub : B ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hitem)))
  have hCsub : C ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inr hitem)
  have htotal : Finset.univ.sum nonA = 2 * appendixS n := by
    exact appendix_sum_nonA_cards n Item chores B C allocation hBcard hCcard hBsub hCsub halloc
  let rest : Finset (Fin n) := Finset.univ.erase zero
  have hrestBound : rest.sum nonA ≤ rest.sum
      (fun owner => if owner.val < n / 2 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro owner howner
    have hne : owner ≠ zero := Finset.mem_erase.mp howner |>.1
    by_cases hlow : owner.val < n / 2
    · have hsubset : allocation owner ⊆ chores := by
        intro item hitem
        exact halloc.1 owner item hitem
      have hpart := appendix_partition_card A B C chores (allocation owner) hAB hAC hBC
        hpartition hsubset
      have hA := hAone owner hne
      have hcard := hlowCard owner hne hlow
      change nonA owner ≤ if owner.val < n / 2 then 1 else 0
      rw [if_pos hlow]
      dsimp [nonA]
      omega
    · have hhigh : n / 2 ≤ owner.val := by omega
      have hsubsetA := hhighSubset owner hne hhigh
      have hBempty : allocation owner ∩ B = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro item hitem
        exact Finset.disjoint_left.mp hAB (hsubsetA (Finset.mem_inter.mp hitem).1)
          (Finset.mem_inter.mp hitem).2
      have hCempty : allocation owner ∩ C = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro item hitem
        exact Finset.disjoint_left.mp hAC (hsubsetA (Finset.mem_inter.mp hitem).1)
          (Finset.mem_inter.mp hitem).2
      change nonA owner ≤ if owner.val < n / 2 then 1 else 0
      rw [if_neg hlow]
      dsimp [nonA]
      rw [hBempty, hCempty]
      norm_num
  have hrestFilter : rest.sum (fun owner => if owner.val < n / 2 then 1 else 0) =
      (rest.filter fun owner => owner.val < n / 2).card := by
    exact Finset.sum_boole (fun owner : Fin n => owner.val < n / 2) rest
  have hfilterSub : rest.filter (fun owner => owner.val < n / 2) ⊆
      Finset.univ.filter (fun owner => owner.val < n / 2) := by
    intro owner howner
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp howner).2⟩
  have hlowCount : (rest.filter fun owner => owner.val < n / 2).card ≤ appendixT n := by
    calc
      (rest.filter fun owner => owner.val < n / 2).card ≤
          (Finset.univ.filter fun owner : Fin n => owner.val < n / 2).card :=
        Finset.card_le_card hfilterSub
      _ = n / 2 := appendix_low_group_card n
      _ ≤ appendixT n := by
        simp only [appendixT]
        omega
  have hrestLe : rest.sum nonA ≤ appendixT n := by
    rw [hrestFilter] at hrestBound
    exact hrestBound.trans hlowCount
  have hsumErase : rest.sum nonA + nonA zero = Finset.univ.sum nonA := by
    dsimp [rest]
    exact Finset.sum_erase_add Finset.univ nonA (Finset.mem_univ zero)
  rw [htotal] at hsumErase
  change 2 * appendixS n - appendixT n ≤ nonA zero
  omega

/-- The symmetric B/C count lower bound makes the A-free bundle expensive for
the second group: it has `P₂` cost at least `s + (t + 1)q`. -/
theorem appendix_p2_a_free_bundle_lower_bound
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (P2 : Bundle Item → ℝ) (zero : Fin n)
    (hq : q = appendixQ n) (hCcard : C.card = appendixS n)
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card)
    (hzeroA : (allocation zero ∩ A).card = 0)
    (hnonA : 2 * appendixS n - appendixT n ≤
      (allocation zero ∩ B).card + (allocation zero ∩ C).card) :
    (appendixS n : ℝ) + (appendixT n + 1 : ℕ) * q ≤ P2 (allocation zero) := by
  have hqone : 1 ≤ q := by
    rw [hq]
    simp only [appendixQ, appendixS, appendixT, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have ht : (0 : ℝ) ≤ ((n + 1) / 2 : ℕ) := Nat.cast_nonneg _
    linarith
  have hCbound : (allocation zero ∩ C).card ≤ appendixS n := by
    calc
      (allocation zero ∩ C).card ≤ C.card := Finset.card_le_card Finset.inter_subset_right
      _ = appendixS n := hCcard
  have hnonA' : appendixS n + appendixT n + 1 ≤
      (allocation zero ∩ B).card + (allocation zero ∩ C).card := by
    have hs : appendixS n = 2 * appendixT n + 1 := rfl
    omega
  have hBbound : appendixT n + 1 ≤ (allocation zero ∩ B).card := by omega
  have hnonAreal : (appendixS n : ℝ) + (appendixT n : ℝ) + 1 ≤
      ((allocation zero ∩ B).card : ℝ) + ((allocation zero ∩ C).card : ℝ) := by
    exact_mod_cast hnonA'
  have hBboundReal : (appendixT n : ℝ) + 1 ≤ ((allocation zero ∩ B).card : ℝ) := by
    exact_mod_cast hBbound
  have hqminus : 0 ≤ q - 1 := by linarith
  have hproduct : (q - 1) * ((appendixT n : ℝ) + 1) ≤
      (q - 1) * ((allocation zero ∩ B).card : ℝ) :=
    mul_le_mul_of_nonneg_left hBboundReal hqminus
  rw [hP2, hzeroA]
  norm_num
  nlinarith

/-- Source-faithful symmetric half of the second Appendix-A proposition.
The source interchanges the two agent groups and the B/C item types. -/
theorem appendix_p2_lower_bound_proof
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P1 P2 : Bundle Item → ℝ) (p1 p2 : ℝ)
    (hn : 4 ≤ n) (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card)
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card)
    (hcostP1 : ∀ (agent : Fin n), agent.val < n / 2 → additiveChoreCost cost agent = P1)
    (hcostP2 : ∀ (agent : Fin n), n / 2 ≤ agent.val → additiveChoreCost cost agent = P2)
    (hmin1 : ∃ agent, P1 (allocation agent) = p1)
    (hmin1Lower : ∀ agent, p1 ≤ P1 (allocation agent))
    (hmin2 : ∃ agent, P2 (allocation agent) = p2) :
    r ≤ p2 := by
  by_contra hnot
  have hp2lt : p2 < r := lt_of_not_ge hnot
  have hAtMost : ∀ agent, (allocation agent ∩ A).card ≤ 1 :=
    appendix_no_two_A_items_proof n Item r q cost chores A B C allocation hn hq hr hAcard hBcard
      hCcard hAB hAC hBC hpartition hcost halloc hefx
  have hAsub : A ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hitem)))
  obtain ⟨zero, hzeroA, hAone⟩ := appendix_a_item_distribution n Item chores A allocation hn
    hAcard hAsub halloc hAtMost
  obtain ⟨highAgent, hhighNe, hhigh⟩ := appendix_exists_high_agent_ne n hn zero
  have hhighSubset : ∀ owner, owner ≠ zero → n / 2 ≤ owner.val → allocation owner ⊆ A := by
    intro owner howner hownerHigh
    exact appendix_high_A_bundle_subset_A_of_p2_lt n Item r q cost chores A B C allocation P2 p2
      hq hAB hAC hBC hpartition hcost halloc hefx hcostP2 hmin2 hp2lt owner hownerHigh
      (hAone owner howner)
  have hhighASubset : allocation highAgent ⊆ A := hhighSubset highAgent hhighNe hhigh
  have hhighP1 : P1 (allocation highAgent) = r :=
    appendix_group_one_formula_on_A_singleton Item r q A B C (allocation highAgent) P1 hAB hAC hP1
      hhighASubset (hAone highAgent hhighNe)
  have hp1le : p1 ≤ r := hmin1Lower highAgent |>.trans_eq hhighP1
  have hlowCard : ∀ owner, owner ≠ zero → owner.val < n / 2 → (allocation owner).card ≤ 2 := by
    intro owner howner hownerLow
    exact appendix_low_A_bundle_card_le_two_of_p1_le n Item r q cost chores A B C allocation P1 p1
      hq hAB hAC hBC hpartition hcost halloc hefx hcostP1 hmin1 hp1le owner hownerLow
      (hAone owner howner)
  have hnonA := appendix_a_free_nonA_card_lower_bound_symmetric n Item chores A B C allocation zero
    hAB hAC hBC hpartition hBcard hCcard halloc hAone hhighSubset hlowCard
  have hzeroLower := appendix_p2_a_free_bundle_lower_bound n Item r q A B C allocation P2 zero hq
    hCcard hP2 hzeroA hnonA
  have hzeroStrict := appendix_p1_a_free_bundle_strictly_expensive n r q hq hr
  obtain ⟨minimum, hminimum⟩ := hmin2
  by_cases hminimumZero : minimum = zero
  · subst minimum
    rw [hminimum] at hzeroLower
    linarith
  · have hminimumA := hAone minimum hminimumZero
    have hqnonneg : 0 ≤ q := by
      rw [hq]
      exact Nat.cast_nonneg _
    have hminimumLower : r ≤ P2 (allocation minimum) := by
      rw [hP2, hminimumA]
      norm_num
      have hBnonneg : 0 ≤ ((allocation minimum ∩ B).card : ℝ) := Nat.cast_nonneg _
      have hCnonneg : 0 ≤ ((allocation minimum ∩ C).card : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [hminimum] at hminimumLower
    linarith

/-- Once the two groupwise minima are at least `r`, the unique A-free bundle
contains at least `t + 1` chores of each of B and C.  This is the first count
step in the source's final Appendix-A contradiction. -/
theorem appendix_a_free_cross_counts
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (P1 P2 : Bundle Item → ℝ) (zero : Fin n)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hBcard : B.card = appendixS n) (hCcard : C.card = appendixS n)
    (hzeroA : (allocation zero ∩ A).card = 0)
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card)
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card)
    (hP1ge : r ≤ P1 (allocation zero))
    (hP2ge : r ≤ P2 (allocation zero)) :
    appendixT n + 1 ≤ (allocation zero ∩ B).card ∧
      appendixT n + 1 ≤ (allocation zero ∩ C).card := by
  have hBbound : (allocation zero ∩ B).card ≤ appendixS n := by
    calc
      (allocation zero ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      _ = appendixS n := hBcard
  have hCbound : (allocation zero ∩ C).card ≤ appendixS n := by
    calc
      (allocation zero ∩ C).card ≤ C.card := Finset.card_le_card Finset.inter_subset_right
      _ = appendixS n := hCcard
  have hcost1 : r ≤ ((allocation zero ∩ B).card : ℝ) +
      q * (allocation zero ∩ C).card := by
    rw [hP1, hzeroA] at hP1ge
    norm_num at hP1ge
    exact hP1ge
  have hcost2 : r ≤ q * ((allocation zero ∩ B).card : ℝ) +
      (allocation zero ∩ C).card := by
    rw [hP2, hzeroA] at hP2ge
    norm_num at hP2ge
    exact hP2ge
  constructor
  · exact appendix_p2_large_forces_B_card n (allocation zero ∩ B).card
      (allocation zero ∩ C).card r q hq hr hCbound hcost2
  · exact appendix_p1_large_forces_C_card n (allocation zero ∩ B).card
      (allocation zero ∩ C).card r q hq hr hBbound hcost1

/-- If the A-free bundle belongs to the first group, EFX after removing one
of its (now guaranteed) B-items raises the first-group minimum to
`r + t + 1`.  This is the source's final low-group EFX estimate. -/
theorem appendix_low_a_free_min_lower
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P1 : Bundle Item → ℝ) (p1 : ℝ)
    (zero : Fin n)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hAB : Disjoint A B) (hBC : Disjoint B C)
    (hzeroA : (allocation zero ∩ A).card = 0)
    (hBcount : appendixT n + 1 ≤ (allocation zero ∩ B).card)
    (hCcount : appendixT n + 1 ≤ (allocation zero ∩ C).card)
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card)
    (hcostP1 : additiveChoreCost cost zero = P1)
    (hmin1 : ∃ agent, P1 (allocation agent) = p1)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    r + (appendixT n + 1 : ℕ) ≤ p1 := by
  have hBpositive : 0 < (allocation zero ∩ B).card := by
    have hTnonneg : 0 ≤ appendixT n := Nat.zero_le _
    omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp hBpositive
  have hitemZero : item ∈ allocation zero := (Finset.mem_inter.mp hitemInter).1
  have hitemB : item ∈ B := (Finset.mem_inter.mp hitemInter).2
  have hitemA : item ∉ A := by
    intro hitemA
    exact Finset.disjoint_left.mp hAB hitemA hitemB
  have hitemC : item ∉ C := by
    intro hitemC
    exact Finset.disjoint_left.mp hBC hitemB hitemC
  have hAerase : (allocation zero \ {item}) ∩ A = allocation zero ∩ A :=
    appendix_inter_erase_eq_of_not_mem (allocation zero) A item hitemA
  have hCerase : (allocation zero \ {item}) ∩ C = allocation zero ∩ C :=
    appendix_inter_erase_eq_of_not_mem (allocation zero) C item hitemC
  have hBeraseSet : (allocation zero \ {item}) ∩ B = (allocation zero ∩ B).erase item := by
    ext candidate
    simp [and_left_comm, and_comm]
  have hBerase : ((allocation zero \ {item}) ∩ B).card =
      (allocation zero ∩ B).card - 1 := by
    rw [hBeraseSet, Finset.card_erase_of_mem hitemInter]
  have hremovedLower : r + (appendixT n + 1 : ℕ) ≤
      P1 (allocation zero \ {item}) := by
    rw [hP1, hAerase, hzeroA, hBerase, hCerase]
    norm_num
    simpa only [Nat.cast_add, Nat.cast_one] using
      (appendix_p1_after_B_removal_lower n (allocation zero ∩ B).card
        (allocation zero ∩ C).card r q hq hr hBcount hCcount)
  obtain ⟨minimum, hminimum⟩ := hmin1
  have hnonempty : allocation zero ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemZero
    simp at hitemZero
  have hEfxItem := (hefx zero minimum).resolve_left hnonempty item hitemZero
  rw [hcostP1, hminimum] at hEfxItem
  exact hremovedLower.trans hEfxItem

/-- The B/C-swapped high-group version of `appendix_low_a_free_min_lower`. -/
theorem appendix_high_a_free_min_lower
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P2 : Bundle Item → ℝ) (p2 : ℝ)
    (zero : Fin n)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hzeroA : (allocation zero ∩ A).card = 0)
    (hBcount : appendixT n + 1 ≤ (allocation zero ∩ B).card)
    (hCcount : appendixT n + 1 ≤ (allocation zero ∩ C).card)
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card)
    (hcostP2 : additiveChoreCost cost zero = P2)
    (hmin2 : ∃ agent, P2 (allocation agent) = p2)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    r + (appendixT n + 1 : ℕ) ≤ p2 := by
  have hCpositive : 0 < (allocation zero ∩ C).card := by
    have hTnonneg : 0 ≤ appendixT n := Nat.zero_le _
    omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp hCpositive
  have hitemZero : item ∈ allocation zero := (Finset.mem_inter.mp hitemInter).1
  have hitemC : item ∈ C := (Finset.mem_inter.mp hitemInter).2
  have hitemA : item ∉ A := by
    intro hitemA
    exact Finset.disjoint_left.mp hAC hitemA hitemC
  have hitemB : item ∉ B := by
    intro hitemB
    exact Finset.disjoint_left.mp hBC hitemB hitemC
  have hAerase : (allocation zero \ {item}) ∩ A = allocation zero ∩ A :=
    appendix_inter_erase_eq_of_not_mem (allocation zero) A item hitemA
  have hBerase : (allocation zero \ {item}) ∩ B = allocation zero ∩ B :=
    appendix_inter_erase_eq_of_not_mem (allocation zero) B item hitemB
  have hCeraseSet : (allocation zero \ {item}) ∩ C = (allocation zero ∩ C).erase item := by
    ext candidate
    simp [and_left_comm, and_comm]
  have hCerase : ((allocation zero \ {item}) ∩ C).card =
      (allocation zero ∩ C).card - 1 := by
    rw [hCeraseSet, Finset.card_erase_of_mem hitemInter]
  have hremovedLower : r + (appendixT n + 1 : ℕ) ≤
      P2 (allocation zero \ {item}) := by
    rw [hP2, hAerase, hzeroA, hBerase, hCerase]
    norm_num
    simpa only [Nat.cast_add, Nat.cast_one] using
      (appendix_p2_after_C_removal_lower n (allocation zero ∩ B).card
        (allocation zero ∩ C).card r q hq hr hBcount hCcount)
  obtain ⟨minimum, hminimum⟩ := hmin2
  have hnonempty : allocation zero ≠ ∅ := by
    intro hempty
    rw [hempty] at hitemZero
    simp at hitemZero
  have hEfxItem := (hefx zero minimum).resolve_left hnonempty item hitemZero
  rw [hcostP2, hminimum] at hEfxItem
  exact hremovedLower.trans hEfxItem

/-- In the low-group final branch, every A-holding bundle must contain a
C-item.  Otherwise its B-items fit into the `t` B-items left outside the
A-free bundle, contradicting the strengthened `p₁` lower bound. -/
theorem appendix_low_A_holders_contain_C
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (chores A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (P1 : Bundle Item → ℝ) (p1 : ℝ) (zero : Fin n)
    (hBcard : B.card = appendixS n)
    (halloc : IsAllocationOf allocation chores)
    (hAone : ∀ owner, owner ≠ zero → (allocation owner ∩ A).card = 1)
    (hBzero : appendixT n + 1 ≤ (allocation zero ∩ B).card)
    (hminLower : r + (appendixT n + 1 : ℕ) ≤ p1)
    (hmin1Lower : ∀ owner, p1 ≤ P1 (allocation owner))
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card) :
    ∀ owner, owner ≠ zero → (allocation owner ∩ C).Nonempty := by
  intro owner howner
  by_contra hnot
  have hCempty : allocation owner ∩ C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
  have hdisjoint : Disjoint (allocation owner ∩ B) (allocation zero ∩ B) :=
    Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (IsAllocationOf.disjoint_of_ne allocation chores halloc howner)
  have hunionSub : (allocation owner ∩ B) ∪ (allocation zero ∩ B) ⊆ B := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hownerItem | hzeroItem
    · exact (Finset.mem_inter.mp hownerItem).2
    · exact (Finset.mem_inter.mp hzeroItem).2
  have hsum : (allocation owner ∩ B).card + (allocation zero ∩ B).card ≤ appendixS n := by
    calc
      (allocation owner ∩ B).card + (allocation zero ∩ B).card =
          ((allocation owner ∩ B) ∪ (allocation zero ∩ B)).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ B.card := Finset.card_le_card hunionSub
      _ = appendixS n := hBcard
  have hBowner : (allocation owner ∩ B).card ≤ appendixT n := by
    have hs : appendixS n = 2 * appendixT n + 1 := rfl
    omega
  have hownerUpper : P1 (allocation owner) ≤ r + appendixT n := by
    rw [hP1, hAone owner howner, hCempty]
    norm_num
    have hBownerReal : ((allocation owner ∩ B).card : ℝ) ≤ appendixT n := by
      exact_mod_cast hBowner
    linarith
  have hmin := hmin1Lower owner
  have hminLower' : r + ((appendixT n : ℝ) + 1) ≤ p1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hminLower
  linarith

/-- The B/C-swapped high-group branch: every A-holding bundle contains a
B-item once the strengthened `p₂` lower bound has been derived. -/
theorem appendix_high_A_holders_contain_B
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (chores A B C : Finset Item) (allocation : Allocation (Fin n) Item)
    (P2 : Bundle Item → ℝ) (p2 : ℝ) (zero : Fin n)
    (hCcard : C.card = appendixS n)
    (halloc : IsAllocationOf allocation chores)
    (hAone : ∀ owner, owner ≠ zero → (allocation owner ∩ A).card = 1)
    (hCzero : appendixT n + 1 ≤ (allocation zero ∩ C).card)
    (hminLower : r + (appendixT n + 1 : ℕ) ≤ p2)
    (hmin2Lower : ∀ owner, p2 ≤ P2 (allocation owner))
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card) :
    ∀ owner, owner ≠ zero → (allocation owner ∩ B).Nonempty := by
  intro owner howner
  by_contra hnot
  have hBempty : allocation owner ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
  have hdisjoint : Disjoint (allocation owner ∩ C) (allocation zero ∩ C) :=
    Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (IsAllocationOf.disjoint_of_ne allocation chores halloc howner)
  have hunionSub : (allocation owner ∩ C) ∪ (allocation zero ∩ C) ⊆ C := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hownerItem | hzeroItem
    · exact (Finset.mem_inter.mp hownerItem).2
    · exact (Finset.mem_inter.mp hzeroItem).2
  have hsum : (allocation owner ∩ C).card + (allocation zero ∩ C).card ≤ appendixS n := by
    calc
      (allocation owner ∩ C).card + (allocation zero ∩ C).card =
          ((allocation owner ∩ C) ∪ (allocation zero ∩ C)).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ C.card := Finset.card_le_card hunionSub
      _ = appendixS n := hCcard
  have hCowner : (allocation owner ∩ C).card ≤ appendixT n := by
    have hs : appendixS n = 2 * appendixT n + 1 := rfl
    omega
  have hownerUpper : P2 (allocation owner) ≤ r + appendixT n := by
    rw [hP2, hAone owner howner, hBempty]
    norm_num
    have hCownerReal : ((allocation owner ∩ C).card : ℝ) ≤ appendixT n := by
      exact_mod_cast hCowner
    linarith
  have hmin := hmin2Lower owner
  have hminLower' : r + ((appendixT n : ℝ) + 1) ≤ p2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hminLower
  linarith

/-- There are too few chores of a class outside a bundle holding at least
`t + 1` of its `2t + 1` items to give every one of the other `n - 1` bundles
an item of that class.  This is the final pigeonhole contradiction in both
Appendix-A group cases. -/
theorem appendix_too_many_nonempty_outside
    (n : ℕ) (Item : Type) [DecidableEq Item]
    (chores D : Finset Item) (allocation : Allocation (Fin n) Item) (zero : Fin n)
    (hn : 4 ≤ n) (hDcard : D.card = appendixS n) (hDsub : D ⊆ chores)
    (halloc : IsAllocationOf allocation chores)
    (hzero : appendixT n + 1 ≤ (allocation zero ∩ D).card)
    (hother : ∀ owner, owner ≠ zero → (allocation owner ∩ D).Nonempty) :
    False := by
  let counts : Fin n → ℕ := fun owner => (allocation owner ∩ D).card
  have htotal : Finset.univ.sum counts = appendixS n := by
    dsimp [counts]
    rw [sum_card_inter_allocation_eq_card_inter allocation chores D halloc,
      Finset.inter_eq_right.mpr hDsub, hDcard]
  let rest : Finset (Fin n) := Finset.univ.erase zero
  have hsumErase : rest.sum counts + counts zero = Finset.univ.sum counts := by
    dsimp [rest]
    exact Finset.sum_erase_add Finset.univ counts (Finset.mem_univ zero)
  rw [htotal] at hsumErase
  have hrestUpper : rest.sum counts ≤ appendixT n := by
    change rest.sum counts + (allocation zero ∩ D).card = appendixS n at hsumErase
    have hs : appendixS n = 2 * appendixT n + 1 := rfl
    omega
  have hrestLower : n - 1 ≤ rest.sum counts := by
    have hpointwise : ∀ owner ∈ rest, 1 ≤ counts owner := by
      intro owner howner
      apply Nat.one_le_iff_ne_zero.mpr
      intro hcountZero
      have hnonempty := hother owner (Finset.mem_erase.mp howner |>.1)
      exact (Finset.nonempty_iff_ne_empty.mp hnonempty) (Finset.card_eq_zero.mp hcountZero)
    have hsumOne : rest.sum (fun _ => 1) ≤ rest.sum counts :=
      Finset.sum_le_sum fun owner howner => hpointwise owner howner
    have hrestCard : rest.card = n - 1 := by
      dsimp [rest]
      simp
    rw [Finset.sum_const, hrestCard] at hsumOne
    norm_num at hsumOne
    omega
  have hstrict : appendixT n < n - 1 := by
    simp only [appendixT]
    omega
  omega

/-- Complete source-faithful nonexistence argument for the general Appendix-A
construction.  The P1/P2 minimum witnesses are stated explicitly so this
theorem is reusable for any concrete labelling of the construction's chores. -/
theorem appendix_no_efx_proof
    (n : ℕ) (Item : Type) [DecidableEq Item] (r q : ℝ)
    (cost : ChoreCost (Fin n) Item) (chores A B C : Finset Item)
    (allocation : Allocation (Fin n) Item) (P1 P2 : Bundle Item → ℝ) (p1 p2 : ℝ)
    (hn : 4 ≤ n) (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hAcard : A.card = n - 1) (hBcard : B.card = appendixS n)
    (hCcard : C.card = appendixS n)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hpartition : A ∪ B ∪ C = chores)
    (hcost : ∀ (agent : Fin n) item,
      (item ∈ A → cost agent item = r) ∧
      (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧
      (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1))
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card)
    (hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card)
    (hcostP1 : ∀ (agent : Fin n), agent.val < n / 2 → additiveChoreCost cost agent = P1)
    (hcostP2 : ∀ (agent : Fin n), n / 2 ≤ agent.val → additiveChoreCost cost agent = P2)
    (hmin1 : ∃ agent, P1 (allocation agent) = p1)
    (hmin1Lower : ∀ agent, p1 ≤ P1 (allocation agent))
    (hmin2 : ∃ agent, P2 (allocation agent) = p2)
    (hmin2Lower : ∀ agent, p2 ≤ P2 (allocation agent)) :
    False := by
  have hAtMost : ∀ agent, (allocation agent ∩ A).card ≤ 1 :=
    appendix_no_two_A_items_proof n Item r q cost chores A B C allocation hn hq hr hAcard hBcard
      hCcard hAB hAC hBC hpartition hcost halloc hefx
  have hAsub : A ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hitem)))
  have hBsub : B ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hitem)))
  have hCsub : C ⊆ chores := by
    rw [← hpartition]
    intro item hitem
    exact Finset.mem_union.mpr (Or.inr hitem)
  obtain ⟨zero, hzeroA, hAone⟩ := appendix_a_item_distribution n Item chores A allocation hn
    hAcard hAsub halloc hAtMost
  have hp1 : r ≤ p1 := appendix_p1_lower_bound_proof n Item r q cost chores A B C allocation P1
    P2 p1 p2 hn hq hr hAcard hBcard hCcard hAB hAC hBC hpartition hcost halloc hefx hP1 hP2
    hcostP1 hcostP2 hmin1 hmin2 hmin2Lower
  have hp2 : r ≤ p2 := appendix_p2_lower_bound_proof n Item r q cost chores A B C allocation P1
    P2 p1 p2 hn hq hr hAcard hBcard hCcard hAB hAC hBC hpartition hcost halloc hefx hP1 hP2
    hcostP1 hcostP2 hmin1 hmin1Lower hmin2
  have hzeroP1 : r ≤ P1 (allocation zero) := hp1.trans (hmin1Lower zero)
  have hzeroP2 : r ≤ P2 (allocation zero) := hp2.trans (hmin2Lower zero)
  obtain ⟨hBcount, hCcount⟩ := appendix_a_free_cross_counts n Item r q A B C allocation P1 P2 zero
    hq hr hBcard hCcard hzeroA hP1 hP2 hzeroP1 hzeroP2
  by_cases hlow : zero.val < n / 2
  · have hp1Strong := appendix_low_a_free_min_lower n Item r q cost A B C allocation P1 p1 zero
      hq hr hAB hBC hzeroA hBcount hCcount hP1 (hcostP1 zero hlow) hmin1 hefx
    have hothersC := appendix_low_A_holders_contain_C n Item r q chores A B C allocation P1 p1 zero
      hBcard halloc hAone hBcount hp1Strong hmin1Lower hP1
    exact appendix_too_many_nonempty_outside n Item chores C allocation zero hn hCcard hCsub halloc
      hCcount hothersC
  · have hhigh : n / 2 ≤ zero.val := by omega
    have hp2Strong := appendix_high_a_free_min_lower n Item r q cost A B C allocation P2 p2 zero
      hq hr hAC hBC hzeroA hBcount hCcount hP2 (hcostP2 zero hhigh) hmin2 hefx
    have hothersB := appendix_high_A_holders_contain_B n Item r q chores A B C allocation P2 p2 zero
      hCcard halloc hAone hCcount hp2Strong hmin2Lower hP2
    exact appendix_too_many_nonempty_outside n Item chores B allocation zero hn hBcard hBsub halloc
      hBcount hothersB

end HT26EFXChores
