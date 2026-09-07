import AppliedModelingLib.SocialChoice.FairDivision.Chores
import Mathlib.Tactic

/-!
# Theorem-2 `(1,r)` construction

He--Tao's EFX--Pareto incompatibility construction has `2n + 1` chores:
`n - 1` universally large A-chores, `floor(n/2) + 1` B-chores, and
`ceil(n/2) + 1` C-chores.  This module is the concrete finite-index bridge
for the theorem and its two intermediate propositions.

Source: `EFXadditivechores.tex`, lines 423--441.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

private theorem po_A_endpoint_lt (n : ℕ) : n - 1 < 2 * n + 1 := by omega

private theorem po_B_endpoint_lt (n : ℕ) : n + n / 2 < 2 * n + 1 := by omega

/-- The universally large A-chores in Theorem 2. -/
def poAItems (n : ℕ) : Finset (Fin (2 * n + 1)) :=
  Finset.Iio ⟨n - 1, po_A_endpoint_lt n⟩

/-- B has `floor(n/2) + 1` chores and is small for the low group. -/
def poBItems (n : ℕ) : Finset (Fin (2 * n + 1)) :=
  Finset.Ico ⟨n - 1, po_A_endpoint_lt n⟩ ⟨n + n / 2, po_B_endpoint_lt n⟩

/-- C has `ceil(n/2) + 1` chores and is small for the high group. -/
def poCItems (n : ℕ) : Finset (Fin (2 * n + 1)) :=
  Finset.Ici ⟨n + n / 2, po_B_endpoint_lt n⟩

/-- The A- and C-chores, namely the chores that are large for a low-group
agent.  This is the counted pool in the asymmetric case of Proposition 2. -/
def poACItems (n : ℕ) : Finset (Fin (2 * n + 1)) := poAItems n ∪ poCItems n

/-- The A- and B-chores, the chore pool large for a high-group agent. -/
def poABItems (n : ℕ) : Finset (Fin (2 * n + 1)) := poAItems n ∪ poBItems n

theorem poAItems_card (n : ℕ) : (poAItems n).card = n - 1 := by
  simp [poAItems]

theorem poBItems_card (n : ℕ) (hn : 1 ≤ n) : (poBItems n).card = n / 2 + 1 := by
  rw [poBItems, Fin.card_Ico]
  change n + n / 2 - (n - 1) = n / 2 + 1
  omega

theorem poCItems_card (n : ℕ) : (poCItems n).card = (n + 1) / 2 + 1 := by
  rw [poCItems, Fin.card_Ici]
  change 2 * n + 1 - (n + n / 2) = (n + 1) / 2 + 1
  omega

theorem poA_B_disjoint (n : ℕ) : Disjoint (poAItems n) (poBItems n) := by
  rw [Finset.disjoint_left]
  intro item hA hB
  have hA' : item < (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) := by
    simpa [poAItems] using hA
  have hBmem : (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item ∧
      item < ⟨n + n / 2, po_B_endpoint_lt n⟩ := by
    simpa [poBItems] using hB
  have hB' : (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item := hBmem.1
  exact (not_lt_of_ge hB') hA'

theorem poA_C_disjoint (n : ℕ) : Disjoint (poAItems n) (poCItems n) := by
  rw [Finset.disjoint_left]
  intro item hA hC
  have hA' : item < (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) := by
    simpa [poAItems] using hA
  have hC' : (⟨n + n / 2, po_B_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item := by
    simpa [poCItems] using hC
  have hAC : (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤
      ⟨n + n / 2, po_B_endpoint_lt n⟩ := by
    apply Fin.le_iff_val_le_val.mpr
    change n - 1 ≤ n + n / 2
    omega
  exact (not_lt_of_ge (hAC.trans hC')) hA'

theorem poACItems_card (n : ℕ) (hn : 1 ≤ n) :
    (poACItems n).card = n + (n + 1) / 2 := by
  rw [poACItems, Finset.card_union_of_disjoint (poA_C_disjoint n), poAItems_card, poCItems_card]
  omega

theorem poB_C_disjoint (n : ℕ) : Disjoint (poBItems n) (poCItems n) := by
  rw [Finset.disjoint_left]
  intro item hB hC
  have hBmem : (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item ∧
      item < ⟨n + n / 2, po_B_endpoint_lt n⟩ := by
    simpa [poBItems] using hB
  have hB' : item < (⟨n + n / 2, po_B_endpoint_lt n⟩ : Fin (2 * n + 1)) := hBmem.2
  have hC' : (⟨n + n / 2, po_B_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item := by
    simpa [poCItems] using hC
  exact (not_lt_of_ge hC') hB'

theorem poABItems_card (n : ℕ) (hn : 1 ≤ n) :
    (poABItems n).card = n + n / 2 := by
  rw [poABItems, Finset.card_union_of_disjoint (poA_B_disjoint n), poAItems_card,
    poBItems_card n hn]
  omega

theorem poC_AB_disjoint (n : ℕ) : Disjoint (poCItems n) (poABItems n) := by
  rw [poABItems, Finset.disjoint_union_right]
  constructor
  · exact (poA_C_disjoint n).symm
  · exact (poB_C_disjoint n).symm

theorem poB_AC_disjoint (n : ℕ) : Disjoint (poBItems n) (poACItems n) := by
  rw [poACItems, Finset.disjoint_union_right]
  constructor
  · exact (poA_B_disjoint n).symm
  · exact poB_C_disjoint n

theorem po_item_partition (n : ℕ) : poAItems n ∪ poBItems n ∪ poCItems n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro item
  by_cases hA : item < (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1))
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl (by simpa [poAItems] using hA))))
  · by_cases hB : item < (⟨n + n / 2, po_B_endpoint_lt n⟩ : Fin (2 * n + 1))
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      simp only [poBItems, Finset.mem_Ico]
      exact ⟨le_of_not_gt hA, hB⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      simpa [poCItems] using le_of_not_gt hB

/-- The exact `(1,r)` cost table used in Theorem 2. -/
def poCost (n : ℕ) (r : ℝ) (agent : Fin n) (item : Fin (2 * n + 1)) : ℝ :=
  if item.val < n - 1 then r else
    if agent.val < n / 2 then
      if item.val < n + n / 2 then 1 else r
    else if item.val < n + n / 2 then r else 1

theorem poCost_is_one_or_r (n : ℕ) (r : ℝ) : IsOneOrRChoreCost (poCost n r) r := by
  intro agent item
  simp only [poCost]
  split <;> rename_i hA
  · exact Or.inr rfl
  · split <;> rename_i hlow
    · split <;> simp
    · split <;> simp

theorem poCost_nonneg (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (agent : Fin n) (item : Fin (2 * n + 1)) : 0 ≤ poCost n r agent item :=
  IsOneOrRChoreCost.nonneg (poCost n r) r (poCost_is_one_or_r n r) hr agent item

/-- The explicit Theorem-2 instance, with all `2n + 1` indexed chores in its
feasible chore pool. -/
def poChoreInstance (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    AdditiveChoreInstance (Fin n) (Fin (2 * n + 1)) where
  chores := Finset.univ
  cost := poCost n r
  nonneg := poCost_nonneg n r hr

/-- The source threshold on `r` implies the strict positivity regime used by
the EFX arguments in Theorem 2. -/
theorem po_r_gt_two (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r) : 2 < r := by
  have ht : (1 : ℝ) ≤ ((n + 1) / 2 : ℕ) := by
    exact_mod_cast (show 1 ≤ (n + 1) / 2 by omega)
  linarith

theorem poCost_on_A (n : ℕ) (r : ℝ) (agent : Fin n) (item : Fin (2 * n + 1))
    (hitem : item ∈ poAItems n) : poCost n r agent item = r := by
  have hval : item.val < n - 1 := by simpa [poAItems] using hitem
  simp [poCost, hval]

theorem poCost_on_B_low (n : ℕ) (r : ℝ) (agent : Fin n)
    (hlow : agent.val < n / 2) (item : Fin (2 * n + 1))
    (hitem : item ∈ poBItems n) : poCost n r agent item = 1 := by
  have hmem : (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item ∧
      item < ⟨n + n / 2, po_B_endpoint_lt n⟩ := by
    simpa [poBItems] using hitem
  have hnotA : ¬ item.val < n - 1 := by
    have hval := Fin.le_iff_val_le_val.mp hmem.1
    have : n - 1 ≤ item.val := by simpa using hval
    omega
  have hB : item.val < n + n / 2 := by simpa using hmem.2
  simp [poCost, hnotA, hlow, hB]

theorem poCost_on_B_high (n : ℕ) (r : ℝ) (agent : Fin n)
    (hhigh : n / 2 ≤ agent.val) (item : Fin (2 * n + 1))
    (hitem : item ∈ poBItems n) : poCost n r agent item = r := by
  have hmem : (⟨n - 1, po_A_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item ∧
      item < ⟨n + n / 2, po_B_endpoint_lt n⟩ := by
    simpa [poBItems] using hitem
  have hnotA : ¬ item.val < n - 1 := by
    have hval := Fin.le_iff_val_le_val.mp hmem.1
    have : n - 1 ≤ item.val := by simpa using hval
    omega
  have hB : item.val < n + n / 2 := by simpa using hmem.2
  have hnotLow : ¬ agent.val < n / 2 := by omega
  simp [poCost, hnotA, hnotLow, hB]

theorem poCost_on_C_low (n : ℕ) (r : ℝ) (agent : Fin n)
    (hlow : agent.val < n / 2) (item : Fin (2 * n + 1))
    (hitem : item ∈ poCItems n) : poCost n r agent item = r := by
  have hmem : (⟨n + n / 2, po_B_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item := by
    simpa [poCItems] using hitem
  have hnotA : ¬ item.val < n - 1 := by
    have : n - 1 ≤ item.val := by
      calc
        n - 1 ≤ n + n / 2 := by omega
        _ ≤ item.val := by simpa using hmem
    omega
  have hnotB : ¬ item.val < n + n / 2 := by
    have : n + n / 2 ≤ item.val := by simpa using hmem
    omega
  simp [poCost, hnotA, hlow, hnotB]

theorem poCost_on_C_high (n : ℕ) (r : ℝ) (agent : Fin n)
    (hhigh : n / 2 ≤ agent.val) (item : Fin (2 * n + 1))
    (hitem : item ∈ poCItems n) : poCost n r agent item = 1 := by
  have hmem : (⟨n + n / 2, po_B_endpoint_lt n⟩ : Fin (2 * n + 1)) ≤ item := by
    simpa [poCItems] using hitem
  have hnotA : ¬ item.val < n - 1 := by
    have : n - 1 ≤ item.val := by
      calc
        n - 1 ≤ n + n / 2 := by omega
        _ ≤ item.val := by simpa using hmem
    omega
  have hnotB : ¬ item.val < n + n / 2 := by
    have : n + n / 2 ≤ item.val := by simpa using hmem
    omega
  have hnotLow : ¬ agent.val < n / 2 := by omega
  simp [poCost, hnotA, hnotLow, hnotB]

private theorem po_partition_bundle (n : ℕ) (bundle : Finset (Fin (2 * n + 1))) :
    bundle = (bundle ∩ poAItems n ∪ bundle ∩ poBItems n) ∪ bundle ∩ poCItems n := by
  ext item
  constructor
  · intro hitem
    have hclass : item ∈ poAItems n ∪ poBItems n ∪ poCItems n := by
      rw [po_item_partition]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hclass with hAB | hC
    · rcases Finset.mem_union.mp hAB with hA | hB
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

private theorem po_inter_disjoint_A_B (n : ℕ) (bundle : Finset (Fin (2 * n + 1))) :
    Disjoint (bundle ∩ poAItems n) (bundle ∩ poBItems n) :=
  Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (poA_B_disjoint n)

private theorem po_inter_disjoint_AB_C (n : ℕ) (bundle : Finset (Fin (2 * n + 1))) :
    Disjoint (bundle ∩ poAItems n ∪ bundle ∩ poBItems n) (bundle ∩ poCItems n) := by
  rw [Finset.disjoint_union_left]
  constructor
  · exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (poA_C_disjoint n)
  · exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (poB_C_disjoint n)

/-- A low-group agent evaluates a Theorem-2 bundle by `r` times its A/C
chores plus one times its B-chores. -/
theorem poCost_low_bundle (n : ℕ) (r : ℝ) (agent : Fin n) (hlow : agent.val < n / 2)
    (bundle : Finset (Fin (2 * n + 1))) :
    additiveChoreCost (poCost n r) agent bundle =
      r * (bundle ∩ poAItems n).card + (bundle ∩ poBItems n).card +
        r * (bundle ∩ poCItems n).card := by
  conv_lhs => rw [po_partition_bundle n bundle]
  rw [additiveChoreCost_union (poCost n r) agent
    (bundle ∩ poAItems n ∪ bundle ∩ poBItems n) (bundle ∩ poCItems n)
    (po_inter_disjoint_AB_C n bundle)]
  rw [additiveChoreCost_union (poCost n r) agent (bundle ∩ poAItems n) (bundle ∩ poBItems n)
    (po_inter_disjoint_A_B n bundle)]
  have hA : ∀ item ∈ bundle ∩ poAItems n, poCost n r agent item = r := by
    intro item hitem
    exact poCost_on_A n r agent item (Finset.mem_inter.mp hitem).2
  have hB : ∀ item ∈ bundle ∩ poBItems n, poCost n r agent item = 1 := by
    intro item hitem
    exact poCost_on_B_low n r agent hlow item (Finset.mem_inter.mp hitem).2
  have hC : ∀ item ∈ bundle ∩ poCItems n, poCost n r agent item = r := by
    intro item hitem
    exact poCost_on_C_low n r agent hlow item (Finset.mem_inter.mp hitem).2
  rw [additiveChoreCost_eq_card_nsmul_of_constant (poCost n r) agent (bundle ∩ poAItems n) r hA,
    additiveChoreCost_eq_card_nsmul_of_constant (poCost n r) agent (bundle ∩ poBItems n) 1 hB,
    additiveChoreCost_eq_card_nsmul_of_constant (poCost n r) agent (bundle ∩ poCItems n) r hC]
  simp only [nsmul_eq_mul]
  ring

/-- The B/C-swapped bundle formula for a high-group agent. -/
theorem poCost_high_bundle (n : ℕ) (r : ℝ) (agent : Fin n) (hhigh : n / 2 ≤ agent.val)
    (bundle : Finset (Fin (2 * n + 1))) :
    additiveChoreCost (poCost n r) agent bundle =
      r * (bundle ∩ poAItems n).card + r * (bundle ∩ poBItems n).card +
        (bundle ∩ poCItems n).card := by
  conv_lhs => rw [po_partition_bundle n bundle]
  rw [additiveChoreCost_union (poCost n r) agent
    (bundle ∩ poAItems n ∪ bundle ∩ poBItems n) (bundle ∩ poCItems n)
    (po_inter_disjoint_AB_C n bundle)]
  rw [additiveChoreCost_union (poCost n r) agent (bundle ∩ poAItems n) (bundle ∩ poBItems n)
    (po_inter_disjoint_A_B n bundle)]
  have hA : ∀ item ∈ bundle ∩ poAItems n, poCost n r agent item = r := by
    intro item hitem
    exact poCost_on_A n r agent item (Finset.mem_inter.mp hitem).2
  have hB : ∀ item ∈ bundle ∩ poBItems n, poCost n r agent item = r := by
    intro item hitem
    exact poCost_on_B_high n r agent hhigh item (Finset.mem_inter.mp hitem).2
  have hC : ∀ item ∈ bundle ∩ poCItems n, poCost n r agent item = 1 := by
    intro item hitem
    exact poCost_on_C_high n r agent hhigh item (Finset.mem_inter.mp hitem).2
  rw [additiveChoreCost_eq_card_nsmul_of_constant (poCost n r) agent (bundle ∩ poAItems n) r hA,
    additiveChoreCost_eq_card_nsmul_of_constant (poCost n r) agent (bundle ∩ poBItems n) r hB,
    additiveChoreCost_eq_card_nsmul_of_constant (poCost n r) agent (bundle ∩ poCItems n) 1 hC]
  simp only [nsmul_eq_mul]
  ring

/-- A low-group bundle consisting only of B-items has cost strictly below
`r` under the Theorem-2 parameter threshold. -/
theorem po_low_B_bundle_cost_lt_r
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (agent : Fin n) (hlow : agent.val < n / 2)
    (bundle : Finset (Fin (2 * n + 1))) (hsubset : bundle ⊆ poBItems n) :
    additiveChoreCost (poCost n r) agent bundle < r := by
  have hAempty : bundle ∩ poAItems n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poA_B_disjoint n)
      (Finset.mem_inter.mp hitem).2 (hsubset (Finset.mem_inter.mp hitem).1)
  have hCempty : bundle ∩ poCItems n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poB_C_disjoint n)
      (hsubset (Finset.mem_inter.mp hitem).1) (Finset.mem_inter.mp hitem).2
  have hBbound : (bundle ∩ poBItems n).card ≤ n / 2 + 1 := by
    calc
      (bundle ∩ poBItems n).card ≤ (poBItems n).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = n / 2 + 1 := poBItems_card n (by omega)
  rw [poCost_low_bundle n r agent hlow bundle, hAempty, hCempty]
  norm_num
  have hBboundReal : ((bundle ∩ poBItems n).card : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hBbound
  have hhalf : ((n / 2 : ℕ) : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n / 2 ≤ (n + 1) / 2 by omega)
  norm_num [Nat.cast_add, Nat.cast_one] at hBboundReal
  linarith

/-- The B/C-swapped strict upper bound for a high-group no-large bundle. -/
theorem po_high_C_bundle_cost_lt_r
    (n : ℕ) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (agent : Fin n) (hhigh : n / 2 ≤ agent.val)
    (bundle : Finset (Fin (2 * n + 1))) (hsubset : bundle ⊆ poCItems n) :
    additiveChoreCost (poCost n r) agent bundle < r := by
  have hAempty : bundle ∩ poAItems n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poA_C_disjoint n)
      (Finset.mem_inter.mp hitem).2 (hsubset (Finset.mem_inter.mp hitem).1)
  have hBempty : bundle ∩ poBItems n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poB_C_disjoint n)
      (Finset.mem_inter.mp hitem).2 (hsubset (Finset.mem_inter.mp hitem).1)
  have hCbound : (bundle ∩ poCItems n).card ≤ (n + 1) / 2 + 1 := by
    calc
      (bundle ∩ poCItems n).card ≤ (poCItems n).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = (n + 1) / 2 + 1 := poCItems_card n
  rw [poCost_high_bundle n r agent hhigh bundle, hAempty, hBempty]
  norm_num
  have hCboundReal : ((bundle ∩ poCItems n).card : ℝ) ≤ (((n + 1) / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hCbound
  norm_num [Nat.cast_add, Nat.cast_one] at hCboundReal
  linarith

/-- Removing one A-chore from a bundle with at least two A-chores leaves
cost at least `r` for either type of Theorem-2 agent. -/
theorem po_cost_erase_A_ge_r
    (n : ℕ) (r : ℝ) (agent : Fin n) (bundle : Finset (Fin (2 * n + 1)))
    (item : Fin (2 * n + 1)) (hitem : item ∈ bundle) (hAitem : item ∈ poAItems n)
    (hAcard : 2 ≤ (bundle ∩ poAItems n).card) (hr : 0 < r) :
    r ≤ additiveChoreCost (poCost n r) agent (bundle \ {item}) := by
  have hAerase : (bundle \ {item}) ∩ poAItems n = (bundle ∩ poAItems n).erase item := by
    ext candidate
    simp [and_assoc, and_comm]
  have hitemInter : item ∈ bundle ∩ poAItems n := Finset.mem_inter.mpr ⟨hitem, hAitem⟩
  have hAremaining : 1 ≤ ((bundle \ {item}) ∩ poAItems n).card := by
    rw [hAerase, Finset.card_erase_of_mem hitemInter]
    omega
  by_cases hlow : agent.val < n / 2
  · rw [poCost_low_bundle n r agent hlow]
    have hAreal : (1 : ℝ) ≤ ((bundle \ {item} ∩ poAItems n).card : ℝ) := by
      exact_mod_cast hAremaining
    have hBnonneg : 0 ≤ ((bundle \ {item} ∩ poBItems n).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle \ {item} ∩ poCItems n).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hhigh : n / 2 ≤ agent.val := by omega
    rw [poCost_high_bundle n r agent hhigh]
    have hAreal : (1 : ℝ) ≤ ((bundle \ {item} ∩ poAItems n).card : ℝ) := by
      exact_mod_cast hAremaining
    have hBnonneg : 0 ≤ ((bundle \ {item} ∩ poBItems n).card : ℝ) := Nat.cast_nonneg _
    have hCnonneg : 0 ≤ ((bundle \ {item} ∩ poCItems n).card : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- Every individual cost in the Theorem-2 construction is at least one once
`r ≥ 1`.  This elementary consequence of the `(1,r)` table is used when an
EFX comparison retains a large chore and one further chore. -/
theorem poCost_ge_one
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) (agent : Fin n) (item : Fin (2 * n + 1)) :
    1 ≤ poCost n r agent item := by
  rcases poCost_is_one_or_r n r agent item with hsmall | hlarge
  · rw [hsmall]
  · rw [hlarge]
    exact hr

/-- Conversely, every individual cost in the Theorem-2 construction is at
most `r` in the positive `r ≥ 1` regime. -/
theorem poCost_le_r
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) (agent : Fin n) (item : Fin (2 * n + 1)) :
    poCost n r agent item ≤ r := by
  rcases poCost_is_one_or_r n r agent item with hsmall | hlarge
  · rw [hsmall]
    exact hr
  · rw [hlarge]

/-- If an owned large chore survives the deletion of a distinct chore, the
remaining additive cost is at least `r`. -/
theorem po_cost_erase_ge_r_of_large
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) (agent : Fin n)
    (bundle : Finset (Fin (2 * n + 1)))
    (large removed : Fin (2 * n + 1))
    (hlarge : large ∈ bundle) (hlargeCost : poCost n r agent large = r)
    (hremovedNe : removed ≠ large) :
    r ≤ additiveChoreCost (poCost n r) agent (bundle \ {removed}) := by
  have hlargeRemaining : large ∈ bundle \ {removed} := by
    simp [hlarge, Ne.symm hremovedNe]
  have hsum := Finset.single_le_sum
    (fun item hitem => poCost_nonneg n r (by linarith) agent item) hlargeRemaining
  unfold additiveChoreCost
  simpa only [Finset.sdiff_singleton_eq_erase, hlargeCost] using hsum

/-- Removing one chore from a bundle that still contains a large chore and a
second distinct chore leaves cost at least `r + 1`.  This is the strict EFX
capacity estimate used in the one-group cases of Proposition 2. -/
theorem po_cost_erase_ge_r_add_one_of_large_and_other
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) (agent : Fin n)
    (bundle : Finset (Fin (2 * n + 1)))
    (large removed other : Fin (2 * n + 1))
    (hlarge : large ∈ bundle) (hlargeCost : poCost n r agent large = r)
    (hremovedNe : removed ≠ large)
    (hother : other ∈ bundle) (hotherNeLarge : other ≠ large)
    (hotherNeRemoved : other ≠ removed) :
    r + 1 ≤ additiveChoreCost (poCost n r) agent (bundle \ {removed}) := by
  have hlargeRemaining : large ∈ bundle \ {removed} := by
    simp [hlarge, Ne.symm hremovedNe]
  have hotherRemaining : other ∈ (bundle \ {removed}).erase large := by
    simp [hother, hotherNeLarge, hotherNeRemoved]
  have hotherCost : 1 ≤ poCost n r agent other := poCost_ge_one n r hr agent other
  have hotherLower : 1 ≤ ∑ item ∈ (bundle \ {removed}).erase large, poCost n r agent item :=
    Finset.single_le_sum (fun item hitem => poCost_nonneg n r (by linarith) agent item)
      hotherRemaining |>.trans' hotherCost
  have hotherLower' : 1 ≤ ∑ item ∈ (bundle.erase removed).erase large,
      poCost n r agent item := by
    simpa only [Finset.sdiff_singleton_eq_erase] using hotherLower
  have hsplit := Finset.sum_erase_add (bundle \ {removed}) (poCost n r agent) hlargeRemaining
  unfold additiveChoreCost
  rw [Finset.sdiff_singleton_eq_erase]
  calc
    r + 1 = 1 + r := by ring
    _ ≤ (∑ item ∈ (bundle.erase removed).erase large, poCost n r agent item) +
        poCost n r agent large := by rw [hlargeCost]; linarith
    _ = ∑ item ∈ bundle.erase removed, poCost n r agent item := by
      simpa only [Finset.sdiff_singleton_eq_erase] using hsplit

/-- A bundle containing a large chore and a distinct additional chore has
total cost at least `r + 1`. -/
theorem po_cost_ge_r_add_one_of_large_and_other
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) (agent : Fin n)
    (bundle : Finset (Fin (2 * n + 1))) (large other : Fin (2 * n + 1))
    (hlarge : large ∈ bundle) (hlargeCost : poCost n r agent large = r)
    (hother : other ∈ bundle) (hotherNeLarge : other ≠ large) :
    r + 1 ≤ additiveChoreCost (poCost n r) agent bundle := by
  have hotherErase : other ∈ bundle.erase large := by
    simp [hother, hotherNeLarge]
  have hotherCost : 1 ≤ poCost n r agent other := poCost_ge_one n r hr agent other
  have hotherLower : 1 ≤ ∑ item ∈ bundle.erase large, poCost n r agent item :=
    Finset.single_le_sum (fun item hitem => poCost_nonneg n r (by linarith) agent item)
      hotherErase |>.trans' hotherCost
  have hsplit := Finset.sum_erase_add bundle (poCost n r agent) hlarge
  unfold additiveChoreCost
  calc
    r + 1 = 1 + r := by ring
    _ ≤ (∑ item ∈ bundle.erase large, poCost n r agent item) + poCost n r agent large := by
      rw [hlargeCost]
      linarith
    _ = ∑ item ∈ bundle, poCost n r agent item := hsplit

/-- A bundle containing a large chore and two further distinct chores has
cost at least `r + 2`. -/
theorem po_cost_ge_r_add_two_of_large_and_others
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) (agent : Fin n)
    (bundle : Finset (Fin (2 * n + 1))) (large first second : Fin (2 * n + 1))
    (hlarge : large ∈ bundle) (hlargeCost : poCost n r agent large = r)
    (hfirst : first ∈ bundle) (hfirstNeLarge : first ≠ large)
    (hsecond : second ∈ bundle) (hsecondNeLarge : second ≠ large)
    (hsecondNeFirst : second ≠ first) :
    r + 2 ≤ additiveChoreCost (poCost n r) agent bundle := by
  have hfirstErase : first ∈ bundle.erase large := by
    simp [hfirst, hfirstNeLarge]
  have hsecondDoubleErase : second ∈ (bundle.erase large).erase first := by
    simp [hsecond, hsecondNeLarge, hsecondNeFirst]
  have hfirstCost : 1 ≤ poCost n r agent first := poCost_ge_one n r hr agent first
  have hsecondCost : 1 ≤ poCost n r agent second := poCost_ge_one n r hr agent second
  have hsecondLower : 1 ≤ ∑ item ∈ (bundle.erase large).erase first, poCost n r agent item :=
    Finset.single_le_sum (fun item hitem => poCost_nonneg n r (by linarith) agent item)
      hsecondDoubleErase |>.trans' hsecondCost
  have hfirstSplit := Finset.sum_erase_add (bundle.erase large) (poCost n r agent) hfirstErase
  have hlargeSplit := Finset.sum_erase_add bundle (poCost n r agent) hlarge
  have hfirstAndMore : 2 ≤ ∑ item ∈ bundle.erase large, poCost n r agent item := by
    calc
      2 = 1 + 1 := by norm_num
      _ ≤ (∑ item ∈ (bundle.erase large).erase first, poCost n r agent item) +
          poCost n r agent first := by linarith
      _ = ∑ item ∈ bundle.erase large, poCost n r agent item := hfirstSplit
  unfold additiveChoreCost
  calc
    r + 2 = 2 + r := by ring
    _ ≤ (∑ item ∈ bundle.erase large, poCost n r agent item) + poCost n r agent large := by
      rw [hlargeCost]
      linarith
    _ = ∑ item ∈ bundle, poCost n r agent item := hlargeSplit

/-- A low-group agent with a large chore cannot receive a second chore when
some low-group agent has a B-only bundle: deleting the second chore leaves
strictly more than the comparison bundle's cost. -/
theorem po_low_bundle_card_le_one_of_large_and_low_no_large
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hlow : owner.val < n / 2)
    (hcomparison : allocation comparison ⊆ poBItems n)
    (large : Fin (2 * n + 1)) (hlarge : large ∈ allocation owner)
    (hlargeCost : poCost n r owner large = r) :
    (allocation owner).card ≤ 1 := by
  by_contra hnot
  have hcard : 1 < (allocation owner).card := by omega
  obtain ⟨removed, hremoved, hremovedNe⟩ := Finset.exists_mem_ne hcard large
  have hremain := po_cost_erase_ge_r_of_large n r
    (by linarith [po_r_gt_two n hn r hr]) owner (allocation owner)
    large removed hlarge hlargeCost hremovedNe
  have hcomparisonCost := po_low_B_bundle_cost_lt_r n hn r hr owner hlow
    (allocation comparison) hcomparison
  have hnonempty : allocation owner ≠ ∅ := by
    intro hempty
    rw [hempty] at hlarge
    simp at hlarge
  have hEfx := (hefx owner comparison).resolve_left hnonempty removed hremoved
  linarith

/-- A comparison bundle of cost at most `r` caps any agent who owns a large
chore at two chores under EFX.  This cost-only form is used when the comparison
B-only bundle may be empty. -/
theorem po_bundle_card_le_two_of_large_vs_cost_le_r
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n)
    (hcomparisonCost : additiveChoreCost (poCost n r) owner (allocation comparison) ≤ r)
    (large : Fin (2 * n + 1)) (hlarge : large ∈ allocation owner)
    (hlargeCost : poCost n r owner large = r) :
    (allocation owner).card ≤ 2 := by
  by_contra hnot
  have hcard : 2 < (allocation owner).card := by omega
  have heraseCard : 1 < ((allocation owner).erase large).card := by
    rw [Finset.card_erase_of_mem hlarge]
    omega
  obtain ⟨removed, hremovedErase, _⟩ := Finset.exists_mem_ne heraseCard large
  obtain ⟨other, hotherErase, hotherNe⟩ := Finset.exists_mem_ne heraseCard removed
  have hremoved : removed ∈ allocation owner := Finset.mem_erase.mp hremovedErase |>.2
  have hremovedNeLarge : removed ≠ large := Finset.mem_erase.mp hremovedErase |>.1
  have hother : other ∈ allocation owner := Finset.mem_erase.mp hotherErase |>.2
  have hotherNeLarge : other ≠ large := Finset.mem_erase.mp hotherErase |>.1
  have hremain := po_cost_erase_ge_r_add_one_of_large_and_other n r hr owner (allocation owner)
    large removed other hlarge hlargeCost hremovedNeLarge hother hotherNeLarge hotherNe
  have hnonempty : allocation owner ≠ ∅ := by
    intro hempty
    rw [hempty] at hlarge
    simp at hlarge
  have hEfx := (hefx owner comparison).resolve_left hnonempty removed hremoved
  linarith

/-- If a high-group agent has a large chore, then comparison to a singleton
low-group large bundle caps her at two chores.  The comparison singleton costs
at most `r` to every observer, while removing one of three owned chores leaves
a large chore and another positive-cost chore. -/
theorem po_high_bundle_card_le_two_of_large_vs_singleton
    (n : ℕ) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (comparisonItem : Fin (2 * n + 1))
    (hcomparison : allocation comparison = {comparisonItem})
    (large : Fin (2 * n + 1)) (hlarge : large ∈ allocation owner)
    (hlargeCost : poCost n r owner large = r) :
    (allocation owner).card ≤ 2 := by
  by_contra hnot
  have hcard : 2 < (allocation owner).card := by omega
  have heraseCard : 1 < ((allocation owner).erase large).card := by
    rw [Finset.card_erase_of_mem hlarge]
    omega
  obtain ⟨removed, hremovedErase, hremovedNe⟩ :=
    Finset.exists_mem_ne heraseCard large
  obtain ⟨other, hotherErase, hotherNe⟩ :=
    Finset.exists_mem_ne heraseCard removed
  have hremoved : removed ∈ allocation owner := Finset.mem_erase.mp hremovedErase |>.2
  have hremovedNeLarge : removed ≠ large := Finset.mem_erase.mp hremovedErase |>.1
  have hother : other ∈ allocation owner := Finset.mem_erase.mp hotherErase |>.2
  have hotherNeLarge : other ≠ large := Finset.mem_erase.mp hotherErase |>.1
  have hremain := po_cost_erase_ge_r_add_one_of_large_and_other n r
    (by linarith) owner (allocation owner)
    large removed other hlarge hlargeCost hremovedNeLarge hother hotherNeLarge hotherNe
  have hcomparisonCost : additiveChoreCost (poCost n r) owner (allocation comparison) ≤ r := by
    rw [hcomparison]
    simp only [additiveChoreCost, Finset.sum_singleton]
    exact poCost_le_r n r (by linarith) owner comparisonItem
  have hnonempty : allocation owner ≠ ∅ := by
    intro hempty
    rw [hempty] at hlarge
    simp at hlarge
  have hEfx := (hefx owner comparison).resolve_left hnonempty removed hremoved
  linarith

/-- A low-group bundle not contained in B contains a chore of cost `r`. -/
theorem po_low_exists_large_of_not_subset_B
    (n : ℕ) (r : ℝ) (agent : Fin n) (hlow : agent.val < n / 2)
    (bundle : Finset (Fin (2 * n + 1))) (hnotB : ¬ bundle ⊆ poBItems n) :
    ∃ item ∈ bundle, poCost n r agent item = r := by
  rcases Finset.not_subset.mp hnotB with ⟨item, hitem, hitemNotB⟩
  have hclass : item ∈ poAItems n ∪ poBItems n ∪ poCItems n := by
    rw [po_item_partition]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hclass with hAB | hC
  · rcases Finset.mem_union.mp hAB with hA | hB
    · exact ⟨item, hitem, poCost_on_A n r agent item hA⟩
    · exact (hitemNotB hB).elim
  · exact ⟨item, hitem, poCost_on_C_low n r agent hlow item hC⟩

/-- A high-group bundle not contained in C contains a chore of cost `r`. -/
theorem po_high_exists_large_of_not_subset_C
    (n : ℕ) (r : ℝ) (agent : Fin n) (hhigh : n / 2 ≤ agent.val)
    (bundle : Finset (Fin (2 * n + 1))) (hnotC : ¬ bundle ⊆ poCItems n) :
    ∃ item ∈ bundle, poCost n r agent item = r := by
  rcases Finset.not_subset.mp hnotC with ⟨item, hitem, hitemNotC⟩
  have hclass : item ∈ poAItems n ∪ poBItems n ∪ poCItems n := by
    rw [po_item_partition]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hclass with hAB | hC
  · rcases Finset.mem_union.mp hAB with hA | hB
    · exact ⟨item, hitem, poCost_on_A n r agent item hA⟩
    · exact ⟨item, hitem, poCost_on_B_high n r agent hhigh item hB⟩
  · exact (hitemNotC hC).elim

/-- A B-only bundle contains no A/C chores. -/
theorem po_AC_card_eq_zero_of_subset_B
    (n : ℕ) (bundle : Finset (Fin (2 * n + 1))) (hsubset : bundle ⊆ poBItems n) :
    (bundle ∩ poACItems n).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro item hitem
  exact Finset.disjoint_left.mp (poB_AC_disjoint n)
    (hsubset (Finset.mem_inter.mp hitem).1) (Finset.mem_inter.mp hitem).2

/-- Relative to a B-only low-group comparison bundle, every low-group agent
receives at most one A/C chore. -/
theorem po_low_AC_card_le_one_of_low_no_large
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hlow : owner.val < n / 2)
    (hcomparison : allocation comparison ⊆ poBItems n) :
    (allocation owner ∩ poACItems n).card ≤ 1 := by
  by_cases hownerB : allocation owner ⊆ poBItems n
  · rw [po_AC_card_eq_zero_of_subset_B n (allocation owner) hownerB]
    omega
  · obtain ⟨large, hlarge, hlargeCost⟩ :=
      po_low_exists_large_of_not_subset_B n r owner hlow (allocation owner) hownerB
    have hcard := po_low_bundle_card_le_one_of_large_and_low_no_large n hn r hr allocation
      hefx owner comparison hlow hcomparison large hlarge hlargeCost
    exact (Finset.card_le_card Finset.inter_subset_left).trans hcard

/-- If a low-group agent is not B-only, its comparison to a B-only bundle is
a singleton large bundle.  This supplies the singleton used for the high-group
capacity bound in the asymmetric Proposition-2 case. -/
theorem po_low_bundle_eq_singleton_of_not_subset_B
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hlow : owner.val < n / 2)
    (hcomparison : allocation comparison ⊆ poBItems n)
    (hnotB : ¬ allocation owner ⊆ poBItems n) :
    ∃ large : Fin (2 * n + 1), allocation owner = {large} ∧ poCost n r owner large = r := by
  obtain ⟨large, hlarge, hlargeCost⟩ :=
    po_low_exists_large_of_not_subset_B n r owner hlow (allocation owner) hnotB
  have hcard := po_low_bundle_card_le_one_of_large_and_low_no_large n hn r hr allocation
    hefx owner comparison hlow hcomparison large hlarge hlargeCost
  refine ⟨large, ?_, hlargeCost⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · exact hlarge
  · intro item hitem
    exact Finset.card_le_one.mp hcard item hitem large hlarge

/-- A C-only bundle contains no A/B chores. -/
theorem po_AB_card_eq_zero_of_subset_C
    (n : ℕ) (bundle : Finset (Fin (2 * n + 1))) (hsubset : bundle ⊆ poCItems n) :
    (bundle ∩ poABItems n).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro item hitem
  exact Finset.disjoint_left.mp (poC_AB_disjoint n)
    (hsubset (Finset.mem_inter.mp hitem).1) (Finset.mem_inter.mp hitem).2

/-- The high-group counterpart of the singleton capacity argument: against a
C-only high-group comparison bundle, a high-group agent with a large chore
cannot own a second chore. -/
theorem po_high_bundle_card_le_one_of_large_and_high_no_large
    (n : ℕ) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hhigh : n / 2 ≤ owner.val)
    (hcomparison : allocation comparison ⊆ poCItems n)
    (large : Fin (2 * n + 1)) (hlarge : large ∈ allocation owner)
    (hlargeCost : poCost n r owner large = r) :
    (allocation owner).card ≤ 1 := by
  by_contra hnot
  have hcard : 1 < (allocation owner).card := by omega
  obtain ⟨removed, hremoved, hremovedNe⟩ := Finset.exists_mem_ne hcard large
  have hremain := po_cost_erase_ge_r_of_large n r (by linarith) owner (allocation owner)
    large removed hlarge hlargeCost hremovedNe
  have hcomparisonCost := po_high_C_bundle_cost_lt_r n r hr owner hhigh
    (allocation comparison) hcomparison
  have hnonempty : allocation owner ≠ ∅ := by
    intro hempty
    rw [hempty] at hlarge
    simp at hlarge
  have hEfx := (hefx owner comparison).resolve_left hnonempty removed hremoved
  linarith

/-- Relative to a C-only high-group comparison bundle, every high-group agent
receives at most one A/B chore. -/
theorem po_high_AB_card_le_one_of_high_no_large
    (n : ℕ) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hhigh : n / 2 ≤ owner.val)
    (hcomparison : allocation comparison ⊆ poCItems n) :
    (allocation owner ∩ poABItems n).card ≤ 1 := by
  by_cases hownerC : allocation owner ⊆ poCItems n
  · rw [po_AB_card_eq_zero_of_subset_C n (allocation owner) hownerC]
    omega
  · obtain ⟨large, hlarge, hlargeCost⟩ :=
      po_high_exists_large_of_not_subset_C n r owner hhigh (allocation owner) hownerC
    have hcard := po_high_bundle_card_le_one_of_large_and_high_no_large n r hr allocation hefx
      owner comparison hhigh hcomparison large hlarge hlargeCost
    exact (Finset.card_le_card Finset.inter_subset_left).trans hcard

/-- A high-group bundle not contained in C is a singleton large bundle when a
C-only high-group comparison bundle exists. -/
theorem po_high_bundle_eq_singleton_of_not_subset_C
    (n : ℕ) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hhigh : n / 2 ≤ owner.val)
    (hcomparison : allocation comparison ⊆ poCItems n)
    (hnotC : ¬ allocation owner ⊆ poCItems n) :
    ∃ large : Fin (2 * n + 1), allocation owner = {large} ∧ poCost n r owner large = r := by
  obtain ⟨large, hlarge, hlargeCost⟩ :=
    po_high_exists_large_of_not_subset_C n r owner hhigh (allocation owner) hnotC
  have hcard := po_high_bundle_card_le_one_of_large_and_high_no_large n r hr allocation hefx
    owner comparison hhigh hcomparison large hlarge hlargeCost
  refine ⟨large, ?_, hlargeCost⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · exact hlarge
  · intro item hitem
    exact Finset.card_le_one.mp hcard item hitem large hlarge

/-- The asymmetric second case of Proposition 2.  If one low-group bundle is
B-only, another low-group bundle is not B-only, and no high-group bundle is
C-only, then the A/C chores cannot fit within the EFX capacity bounds. -/
theorem po_one_low_no_large_one_low_large_contradiction
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (lowNoLarge lowLarge : Fin n)
    (hlowNoLarge : lowNoLarge.val < n / 2) (hlowLarge : lowLarge.val < n / 2)
    (hlowNoLargeB : allocation lowNoLarge ⊆ poBItems n)
    (hlowLargeNotB : ¬ allocation lowLarge ⊆ poBItems n)
    (hhighNotC : ∀ high : Fin n, n / 2 ≤ high.val → ¬ allocation high ⊆ poCItems n) :
    False := by
  let lowGroup : Finset (Fin n) := Finset.univ.filter fun agent => agent.val < n / 2
  let highGroup : Finset (Fin n) := Finset.univ.filter fun agent => n / 2 ≤ agent.val
  let acCounts : Fin n → ℕ := fun agent => (allocation agent ∩ poACItems n).card
  have hLowGroupCard : lowGroup.card = n / 2 := by
    dsimp [lowGroup]
    simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
      (Fin.card_filter_val_lt (n := n) (m := n / 2))
  have hHighGroupCard : highGroup.card = (n + 1) / 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun agent : Fin n => agent.val < n / 2)
    have hpartition' : lowGroup.card + highGroup.card = n := by
      simpa only [lowGroup, highGroup, Finset.card_univ, Fintype.card_fin, Nat.not_lt] using
        hpartition
    rw [hLowGroupCard] at hpartition'
    omega
  have htotal : Finset.univ.sum acCounts = n + (n + 1) / 2 := by
    dsimp [acCounts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poACItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poACItems_card n (by omega)]
  have hlowNoLargeMem : lowNoLarge ∈ lowGroup := by
    simp [lowGroup, hlowNoLarge]
  have hlowZero : acCounts lowNoLarge = 0 := by
    change (allocation lowNoLarge ∩ poACItems n).card = 0
    exact po_AC_card_eq_zero_of_subset_B n (allocation lowNoLarge) hlowNoLargeB
  have hLowCap : ∀ agent ∈ lowGroup, acCounts agent ≤ 1 := by
    intro agent hagent
    have hagentLow : agent.val < n / 2 := by
      exact (Finset.mem_filter.mp hagent).2
    change (allocation agent ∩ poACItems n).card ≤ 1
    exact po_low_AC_card_le_one_of_low_no_large n hn r hr allocation hefx agent lowNoLarge
      hagentLow hlowNoLargeB
  have hLowEraseBound : (lowGroup.erase lowNoLarge).sum acCounts ≤
      (lowGroup.erase lowNoLarge).sum (fun _ => 1) := by
    apply Finset.sum_le_sum
    intro agent hagent
    exact hLowCap agent (Finset.mem_of_mem_erase hagent)
  have hLowSplit := Finset.sum_erase_add lowGroup acCounts hlowNoLargeMem
  rw [hlowZero] at hLowSplit
  norm_num at hLowSplit
  have hLowEraseCard : (lowGroup.erase lowNoLarge).card = n / 2 - 1 := by
    rw [Finset.card_erase_of_mem hlowNoLargeMem]
    rw [hLowGroupCard]
  have hLowTotal : lowGroup.sum acCounts ≤ n / 2 - 1 := by
    rw [Finset.sum_const, hLowEraseCard] at hLowEraseBound
    simpa only [nsmul_eq_mul, Nat.mul_one, hLowSplit] using hLowEraseBound
  obtain ⟨comparisonItem, hcomparison, hcomparisonCost⟩ :=
    po_low_bundle_eq_singleton_of_not_subset_B n hn r hr allocation hefx lowLarge lowNoLarge
      hlowLarge hlowNoLargeB hlowLargeNotB
  have hHighCap : ∀ agent ∈ highGroup, acCounts agent ≤ 2 := by
    intro agent hagent
    have hagentHigh : n / 2 ≤ agent.val := (Finset.mem_filter.mp hagent).2
    obtain ⟨large, hlarge, hlargeCost⟩ := po_high_exists_large_of_not_subset_C n r agent
      hagentHigh (allocation agent) (hhighNotC agent hagentHigh)
    have hcard := po_high_bundle_card_le_two_of_large_vs_singleton n r hr allocation hefx
      agent lowLarge comparisonItem hcomparison large hlarge hlargeCost
    change (allocation agent ∩ poACItems n).card ≤ 2
    exact (Finset.card_le_card Finset.inter_subset_left).trans hcard
  have hHighTotal : highGroup.sum acCounts ≤ highGroup.card * 2 := by
    calc
      highGroup.sum acCounts ≤ highGroup.sum (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro agent hagent
        exact hHighCap agent hagent
      _ = highGroup.card * 2 := by
        exact Finset.sum_const_nat (fun _ _ => rfl)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun agent : Fin n => agent.val < n / 2) acCounts
  have hsplit' : lowGroup.sum acCounts + highGroup.sum acCounts = Finset.univ.sum acCounts := by
    simpa [lowGroup, highGroup, Nat.not_lt] using hsplit
  omega

/-- The B/C-swapped asymmetric case of Proposition 2.  If one high-group
bundle is C-only, another is not C-only, and no low-group bundle is B-only,
the A/B chores exceed the EFX capacity of the two groups. -/
theorem po_one_high_no_large_one_high_large_contradiction
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (highNoLarge highLarge : Fin n)
    (hhighNoLarge : n / 2 ≤ highNoLarge.val) (hhighLarge : n / 2 ≤ highLarge.val)
    (hhighNoLargeC : allocation highNoLarge ⊆ poCItems n)
    (hhighLargeNotC : ¬ allocation highLarge ⊆ poCItems n)
    (hlowNotB : ∀ low : Fin n, low.val < n / 2 → ¬ allocation low ⊆ poBItems n) :
    False := by
  let lowGroup : Finset (Fin n) := Finset.univ.filter fun agent => agent.val < n / 2
  let highGroup : Finset (Fin n) := Finset.univ.filter fun agent => n / 2 ≤ agent.val
  let abCounts : Fin n → ℕ := fun agent => (allocation agent ∩ poABItems n).card
  have hLowGroupCard : lowGroup.card = n / 2 := by
    dsimp [lowGroup]
    simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
      (Fin.card_filter_val_lt (n := n) (m := n / 2))
  have hHighGroupCard : highGroup.card = (n + 1) / 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun agent : Fin n => agent.val < n / 2)
    have hpartition' : lowGroup.card + highGroup.card = n := by
      simpa only [lowGroup, highGroup, Finset.card_univ, Fintype.card_fin, Nat.not_lt] using
        hpartition
    rw [hLowGroupCard] at hpartition'
    omega
  have htotal : Finset.univ.sum abCounts = n + n / 2 := by
    dsimp [abCounts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poABItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poABItems_card n (by omega)]
  have hhighNoLargeMem : highNoLarge ∈ highGroup := by
    simp [highGroup, hhighNoLarge]
  have hhighZero : abCounts highNoLarge = 0 := by
    change (allocation highNoLarge ∩ poABItems n).card = 0
    exact po_AB_card_eq_zero_of_subset_C n (allocation highNoLarge) hhighNoLargeC
  have hHighCap : ∀ agent ∈ highGroup, abCounts agent ≤ 1 := by
    intro agent hagent
    have hagentHigh : n / 2 ≤ agent.val := (Finset.mem_filter.mp hagent).2
    change (allocation agent ∩ poABItems n).card ≤ 1
    exact po_high_AB_card_le_one_of_high_no_large n r hr allocation hefx agent highNoLarge
      hagentHigh hhighNoLargeC
  have hHighEraseBound : (highGroup.erase highNoLarge).sum abCounts ≤
      (highGroup.erase highNoLarge).sum (fun _ => 1) := by
    apply Finset.sum_le_sum
    intro agent hagent
    exact hHighCap agent (Finset.mem_of_mem_erase hagent)
  have hHighSplit := Finset.sum_erase_add highGroup abCounts hhighNoLargeMem
  rw [hhighZero] at hHighSplit
  norm_num at hHighSplit
  have hHighEraseCard : (highGroup.erase highNoLarge).card = (n + 1) / 2 - 1 := by
    rw [Finset.card_erase_of_mem hhighNoLargeMem, hHighGroupCard]
  have hHighTotal : highGroup.sum abCounts ≤ (n + 1) / 2 - 1 := by
    rw [Finset.sum_const, hHighEraseCard] at hHighEraseBound
    simpa only [nsmul_eq_mul, Nat.mul_one, hHighSplit] using hHighEraseBound
  obtain ⟨comparisonItem, hcomparison, hcomparisonCost⟩ :=
    po_high_bundle_eq_singleton_of_not_subset_C n r hr allocation hefx highLarge highNoLarge
      hhighLarge hhighNoLargeC hhighLargeNotC
  have hLowCap : ∀ agent ∈ lowGroup, abCounts agent ≤ 2 := by
    intro agent hagent
    have hagentLow : agent.val < n / 2 := (Finset.mem_filter.mp hagent).2
    obtain ⟨large, hlarge, hlargeCost⟩ := po_low_exists_large_of_not_subset_B n r agent
      hagentLow (allocation agent) (hlowNotB agent hagentLow)
    have hcomparisonCost' : additiveChoreCost (poCost n r) agent (allocation highLarge) ≤ r := by
      rw [hcomparison]
      simp only [additiveChoreCost, Finset.sum_singleton]
      exact poCost_le_r n r (by linarith [po_r_gt_two n hn r hr]) agent comparisonItem
    have hcard := po_bundle_card_le_two_of_large_vs_cost_le_r n r
      (by linarith [po_r_gt_two n hn r hr]) allocation hefx agent highLarge hcomparisonCost'
      large hlarge hlargeCost
    change (allocation agent ∩ poABItems n).card ≤ 2
    exact (Finset.card_le_card Finset.inter_subset_left).trans hcard
  have hLowTotal : lowGroup.sum abCounts ≤ lowGroup.card * 2 := by
    calc
      lowGroup.sum abCounts ≤ lowGroup.sum (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro agent hagent
        exact hLowCap agent hagent
      _ = lowGroup.card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun agent : Fin n => agent.val < n / 2) abCounts
  have hsplit' : lowGroup.sum abCounts + highGroup.sum abCounts = Finset.univ.sum abCounts := by
    simpa [lowGroup, highGroup, Nat.not_lt] using hsplit
  omega

/-- The all-B-only low-group subcase of Proposition 2.  A low bundle with at
most one B-chore and a high bundle with two C-chores contradict EFX, because
every high bundle also has a large A/B-chore. -/
theorem po_all_low_no_large_contradiction
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (hlowB : ∀ low : Fin n, low.val < n / 2 → allocation low ⊆ poBItems n)
    (hhighNotC : ∀ high : Fin n, n / 2 ≤ high.val → ¬ allocation high ⊆ poCItems n) :
    False := by
  let lowGroup : Finset (Fin n) := Finset.univ.filter fun agent => agent.val < n / 2
  let highGroup : Finset (Fin n) := Finset.univ.filter fun agent => n / 2 ≤ agent.val
  let bCounts : Fin n → ℕ := fun agent => (allocation agent ∩ poBItems n).card
  let cCounts : Fin n → ℕ := fun agent => (allocation agent ∩ poCItems n).card
  have hLowGroupCard : lowGroup.card = n / 2 := by
    dsimp [lowGroup]
    simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
      (Fin.card_filter_val_lt (n := n) (m := n / 2))
  have hHighGroupCard : highGroup.card = (n + 1) / 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun agent : Fin n => agent.val < n / 2)
    have hpartition' : lowGroup.card + highGroup.card = n := by
      simpa only [lowGroup, highGroup, Finset.card_univ, Fintype.card_fin, Nat.not_lt] using
        hpartition
    rw [hLowGroupCard] at hpartition'
    omega
  have hBTotal : Finset.univ.sum bCounts = n / 2 + 1 := by
    dsimp [bCounts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poBItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poBItems_card n (by omega)]
  have hLowBTotal : lowGroup.sum bCounts ≤ n / 2 + 1 := by
    calc
      lowGroup.sum bCounts ≤ Finset.univ.sum bCounts :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by intros; omega)
      _ = n / 2 + 1 := hBTotal
  have hlowSmall : ∃ low ∈ lowGroup, (allocation low).card ≤ 1 := by
    by_contra hnot
    push Not at hnot
    have hpoint : ∀ low ∈ lowGroup, 2 ≤ bCounts low := by
      intro low hlow
      have hstrictCard : 1 < (allocation low).card := by
        have hnotSmall := hnot low hlow
        omega
      have hBcard : bCounts low = (allocation low).card := by
        change (allocation low ∩ poBItems n).card = (allocation low).card
        rw [Finset.inter_eq_left.mpr (hlowB low (Finset.mem_filter.mp hlow).2)]
      rw [hBcard]
      omega
    have hsumLower : lowGroup.card * 2 ≤ lowGroup.sum bCounts := by
      calc
        lowGroup.card * 2 = lowGroup.sum (fun _ => 2) :=
          (Finset.sum_const_nat (fun _ _ => rfl)).symm
        _ ≤ lowGroup.sum bCounts := by
          apply Finset.sum_le_sum
          intro low hlow
          exact hpoint low hlow
    rw [hLowGroupCard] at hsumLower
    omega
  obtain ⟨low, hlowMem, hlowCard⟩ := hlowSmall
  have hlowType : low.val < n / 2 := (Finset.mem_filter.mp hlowMem).2
  have hLowCZero : ∀ agent ∈ lowGroup, cCounts agent = 0 := by
    intro agent hagent
    have hagentLow : agent.val < n / 2 := (Finset.mem_filter.mp hagent).2
    change (allocation agent ∩ poCItems n).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poB_C_disjoint n)
      (hlowB agent hagentLow (Finset.mem_inter.mp hitem).1) (Finset.mem_inter.mp hitem).2
  have hLowCSum : lowGroup.sum cCounts = 0 := by
    exact Finset.sum_eq_zero fun agent hagent => hLowCZero agent hagent
  have hCTotal : Finset.univ.sum cCounts = (n + 1) / 2 + 1 := by
    dsimp [cCounts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poCItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poCItems_card]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun agent : Fin n => agent.val < n / 2) cCounts
  have hsplit' : lowGroup.sum cCounts + highGroup.sum cCounts = Finset.univ.sum cCounts := by
    simpa [lowGroup, highGroup, Nat.not_lt] using hsplit
  have hHighCSum : highGroup.sum cCounts = (n + 1) / 2 + 1 := by
    omega
  have hhighTwo : ∃ high ∈ highGroup, 2 ≤ cCounts high := by
    by_contra hnot
    push Not at hnot
    have hpoint : ∀ high ∈ highGroup, cCounts high ≤ 1 := by
      intro high hhigh
      have hnotTwo := hnot high hhigh
      have hlt : cCounts high < 2 := by omega
      omega
    have hsumUpper : highGroup.sum cCounts ≤ highGroup.card * 1 := by
      calc
        highGroup.sum cCounts ≤ highGroup.sum (fun _ => 1) := by
          apply Finset.sum_le_sum
          intro high hhigh
          exact hpoint high hhigh
        _ = highGroup.card * 1 := Finset.sum_const_nat (fun _ _ => rfl)
    rw [hHighGroupCard] at hsumUpper
    omega
  obtain ⟨high, hhighMem, hhighCcount⟩ := hhighTwo
  have hhighType : n / 2 ≤ high.val := (Finset.mem_filter.mp hhighMem).2
  obtain ⟨large, hlarge, hlargeCost⟩ := po_high_exists_large_of_not_subset_C n r high
    hhighType (allocation high) (hhighNotC high hhighType)
  have hlargeNotC : large ∉ poCItems n := by
    intro hlargeC
    have hCcost := poCost_on_C_high n r high hhighType large hlargeC
    have hrOne : 1 < r := by linarith [po_r_gt_two n hn r hr]
    linarith
  have hCpositive : 0 < (allocation high ∩ poCItems n).card := by
    change 0 < cCounts high
    omega
  obtain ⟨removed, hremovedInter⟩ := Finset.card_pos.mp hCpositive
  have hCerasePositive : 0 < ((allocation high ∩ poCItems n).erase removed).card := by
    rw [Finset.card_erase_of_mem hremovedInter]
    change 0 < cCounts high - 1
    omega
  obtain ⟨other, hotherErase⟩ := Finset.card_pos.mp hCerasePositive
  have hremoved : removed ∈ allocation high := (Finset.mem_inter.mp hremovedInter).1
  have hremovedC : removed ∈ poCItems n := (Finset.mem_inter.mp hremovedInter).2
  have hotherInter : other ∈ allocation high ∩ poCItems n := Finset.mem_erase.mp hotherErase |>.2
  have hother : other ∈ allocation high := (Finset.mem_inter.mp hotherInter).1
  have hotherC : other ∈ poCItems n := (Finset.mem_inter.mp hotherInter).2
  have hotherNeRemoved : other ≠ removed := Finset.mem_erase.mp hotherErase |>.1
  have hremovedNeLarge : removed ≠ large := by
    intro heq
    apply hlargeNotC
    simpa [heq] using hremovedC
  have hotherNeLarge : other ≠ large := by
    intro heq
    apply hlargeNotC
    simpa [heq] using hotherC
  have hremain := po_cost_erase_ge_r_add_one_of_large_and_other n r
    (by linarith [po_r_gt_two n hn r hr]) high (allocation high) large removed other hlarge
    hlargeCost hremovedNeLarge hother hotherNeLarge hotherNeRemoved
  have hnonempty : allocation high ≠ ∅ := by
    intro hempty
    rw [hempty] at hlarge
    simp at hlarge
  have hEfx := (hefx high low).resolve_left hnonempty removed hremoved
  have hcomparisonCost : additiveChoreCost (poCost n r) high (allocation low) ≤ r := by
    calc
      additiveChoreCost (poCost n r) high (allocation low) ≤ (allocation low).card • r :=
        additiveChoreCost_le_card_nsmul_of_le (poCost n r) high (allocation low) r
          (fun item hitem => poCost_le_r n r (by linarith [po_r_gt_two n hn r hr]) high item)
      _ ≤ 1 • r := nsmul_le_nsmul_left (by linarith [po_r_gt_two n hn r hr]) hlowCard
      _ = r := one_nsmul r
  linarith

/-- The all-C-only high-group subcase of Proposition 2.  A high bundle with
at most one C-chore and a low bundle with two B-chores violate EFX, since every
low bundle has a large A/C-chore. -/
theorem po_all_high_no_large_contradiction
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (hhighC : ∀ high : Fin n, n / 2 ≤ high.val → allocation high ⊆ poCItems n)
    (hlowNotB : ∀ low : Fin n, low.val < n / 2 → ¬ allocation low ⊆ poBItems n) :
    False := by
  let lowGroup : Finset (Fin n) := Finset.univ.filter fun agent => agent.val < n / 2
  let highGroup : Finset (Fin n) := Finset.univ.filter fun agent => n / 2 ≤ agent.val
  let bCounts : Fin n → ℕ := fun agent => (allocation agent ∩ poBItems n).card
  let cCounts : Fin n → ℕ := fun agent => (allocation agent ∩ poCItems n).card
  have hLowGroupCard : lowGroup.card = n / 2 := by
    dsimp [lowGroup]
    simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
      (Fin.card_filter_val_lt (n := n) (m := n / 2))
  have hHighGroupCard : highGroup.card = (n + 1) / 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun agent : Fin n => agent.val < n / 2)
    have hpartition' : lowGroup.card + highGroup.card = n := by
      simpa only [lowGroup, highGroup, Finset.card_univ, Fintype.card_fin, Nat.not_lt] using
        hpartition
    rw [hLowGroupCard] at hpartition'
    omega
  have hBTotal : Finset.univ.sum bCounts = n / 2 + 1 := by
    dsimp [bCounts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poBItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poBItems_card n (by omega)]
  have hHighBZero : ∀ high ∈ highGroup, bCounts high = 0 := by
    intro high hhigh
    have hhighType : n / 2 ≤ high.val := (Finset.mem_filter.mp hhigh).2
    change (allocation high ∩ poBItems n).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poB_C_disjoint n)
      (Finset.mem_inter.mp hitem).2 (hhighC high hhighType (Finset.mem_inter.mp hitem).1)
  have hHighBSum : highGroup.sum bCounts = 0 :=
    Finset.sum_eq_zero fun high hhigh => hHighBZero high hhigh
  have hBsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun agent : Fin n => agent.val < n / 2) bCounts
  have hBsplit' : lowGroup.sum bCounts + highGroup.sum bCounts = Finset.univ.sum bCounts := by
    simpa [lowGroup, highGroup, Nat.not_lt] using hBsplit
  have hLowBSum : lowGroup.sum bCounts = n / 2 + 1 := by
    omega
  have hlowTwo : ∃ low ∈ lowGroup, 2 ≤ bCounts low := by
    by_contra hnot
    push Not at hnot
    have hpoint : ∀ low ∈ lowGroup, bCounts low ≤ 1 := by
      intro low hlow
      have hnotTwo := hnot low hlow
      omega
    have hsumUpper : lowGroup.sum bCounts ≤ lowGroup.card * 1 := by
      calc
        lowGroup.sum bCounts ≤ lowGroup.sum (fun _ => 1) := by
          apply Finset.sum_le_sum
          intro low hlow
          exact hpoint low hlow
        _ = lowGroup.card * 1 := Finset.sum_const_nat (fun _ _ => rfl)
    rw [hLowGroupCard] at hsumUpper
    omega
  obtain ⟨low, hlowMem, hlowBcount⟩ := hlowTwo
  have hlowType : low.val < n / 2 := (Finset.mem_filter.mp hlowMem).2
  have hCTotal : Finset.univ.sum cCounts = (n + 1) / 2 + 1 := by
    dsimp [cCounts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poCItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poCItems_card]
  have hHighCTotal : highGroup.sum cCounts ≤ (n + 1) / 2 + 1 := by
    calc
      highGroup.sum cCounts ≤ Finset.univ.sum cCounts :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by intros; omega)
      _ = (n + 1) / 2 + 1 := hCTotal
  have hhighSmall : ∃ high ∈ highGroup, (allocation high).card ≤ 1 := by
    by_contra hnot
    push Not at hnot
    have hpoint : ∀ high ∈ highGroup, 2 ≤ cCounts high := by
      intro high hhigh
      have hstrictCard : 1 < (allocation high).card := by
        have hnotSmall := hnot high hhigh
        omega
      have hCcard : cCounts high = (allocation high).card := by
        change (allocation high ∩ poCItems n).card = (allocation high).card
        rw [Finset.inter_eq_left.mpr (hhighC high (Finset.mem_filter.mp hhigh).2)]
      rw [hCcard]
      omega
    have hsumLower : highGroup.card * 2 ≤ highGroup.sum cCounts := by
      calc
        highGroup.card * 2 = highGroup.sum (fun _ => 2) :=
          (Finset.sum_const_nat (fun _ _ => rfl)).symm
        _ ≤ highGroup.sum cCounts := by
          apply Finset.sum_le_sum
          intro high hhigh
          exact hpoint high hhigh
    rw [hHighGroupCard] at hsumLower
    omega
  obtain ⟨high, hhighMem, hhighCard⟩ := hhighSmall
  have hhighType : n / 2 ≤ high.val := (Finset.mem_filter.mp hhighMem).2
  obtain ⟨large, hlarge, hlargeCost⟩ := po_low_exists_large_of_not_subset_B n r low
    hlowType (allocation low) (hlowNotB low hlowType)
  have hlargeNotB : large ∉ poBItems n := by
    intro hlargeB
    have hBcost := poCost_on_B_low n r low hlowType large hlargeB
    have hrOne : 1 < r := by linarith [po_r_gt_two n hn r hr]
    linarith
  have hBpositive : 0 < (allocation low ∩ poBItems n).card := by
    change 0 < bCounts low
    omega
  obtain ⟨removed, hremovedInter⟩ := Finset.card_pos.mp hBpositive
  have hBerasePositive : 0 < ((allocation low ∩ poBItems n).erase removed).card := by
    rw [Finset.card_erase_of_mem hremovedInter]
    change 0 < bCounts low - 1
    omega
  obtain ⟨other, hotherErase⟩ := Finset.card_pos.mp hBerasePositive
  have hremoved : removed ∈ allocation low := (Finset.mem_inter.mp hremovedInter).1
  have hremovedB : removed ∈ poBItems n := (Finset.mem_inter.mp hremovedInter).2
  have hotherInter : other ∈ allocation low ∩ poBItems n := Finset.mem_erase.mp hotherErase |>.2
  have hother : other ∈ allocation low := (Finset.mem_inter.mp hotherInter).1
  have hotherB : other ∈ poBItems n := (Finset.mem_inter.mp hotherInter).2
  have hotherNeRemoved : other ≠ removed := Finset.mem_erase.mp hotherErase |>.1
  have hremovedNeLarge : removed ≠ large := by
    intro heq
    apply hlargeNotB
    simpa [heq] using hremovedB
  have hotherNeLarge : other ≠ large := by
    intro heq
    apply hlargeNotB
    simpa [heq] using hotherB
  have hremain := po_cost_erase_ge_r_add_one_of_large_and_other n r
    (by linarith [po_r_gt_two n hn r hr]) low (allocation low) large removed other hlarge
    hlargeCost hremovedNeLarge hother hotherNeLarge hotherNeRemoved
  have hnonempty : allocation low ≠ ∅ := by
    intro hempty
    rw [hempty] at hlarge
    simp at hlarge
  have hEfx := (hefx low high).resolve_left hnonempty removed hremoved
  have hcomparisonCost : additiveChoreCost (poCost n r) low (allocation high) ≤ r := by
    calc
      additiveChoreCost (poCost n r) low (allocation high) ≤ (allocation high).card • r :=
        additiveChoreCost_le_card_nsmul_of_le (poCost n r) low (allocation high) r
          (fun item hitem => poCost_le_r n r (by linarith [po_r_gt_two n hn r hr]) low item)
      _ ≤ 1 • r := nsmul_le_nsmul_left (by linarith [po_r_gt_two n hn r hr]) hhighCard
      _ = r := one_nsmul r
  linarith

/-- If a low-group no-large bundle exists, EFX forbids every low-group agent
from receiving two A-chores. -/
theorem po_low_A_card_le_one_of_low_no_large
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hlow : owner.val < n / 2)
    (hcomparison : allocation comparison ⊆ poBItems n) :
    (allocation owner ∩ poAItems n).card ≤ 1 := by
  by_contra hnot
  have hAtwo : 2 ≤ (allocation owner ∩ poAItems n).card := by omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp (by omega :
    0 < (allocation owner ∩ poAItems n).card)
  have hitem : item ∈ allocation owner := (Finset.mem_inter.mp hitemInter).1
  have hAitem : item ∈ poAItems n := (Finset.mem_inter.mp hitemInter).2
  have hrem := po_cost_erase_A_ge_r n r owner (allocation owner) item hitem hAitem hAtwo
    (by linarith [po_r_gt_two n hn r hr])
  have hcomp := po_low_B_bundle_cost_lt_r n hn r hr owner hlow (allocation comparison) hcomparison
  have hnonempty : allocation owner ≠ ∅ := by
    intro hempty
    rw [hempty] at hitem
    simp at hitem
  have hEfx := (hefx owner comparison).resolve_left hnonempty item hitem
  linarith

/-- The high-group counterpart, using a C-only no-large comparison bundle. -/
theorem po_high_A_card_le_one_of_high_no_large
    (n : ℕ) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (owner comparison : Fin n) (hhigh : n / 2 ≤ owner.val)
    (hcomparison : allocation comparison ⊆ poCItems n) :
    (allocation owner ∩ poAItems n).card ≤ 1 := by
  by_contra hnot
  have hAtwo : 2 ≤ (allocation owner ∩ poAItems n).card := by omega
  obtain ⟨item, hitemInter⟩ := Finset.card_pos.mp (by omega :
    0 < (allocation owner ∩ poAItems n).card)
  have hitem : item ∈ allocation owner := (Finset.mem_inter.mp hitemInter).1
  have hAitem : item ∈ poAItems n := (Finset.mem_inter.mp hitemInter).2
  have hrem := po_cost_erase_A_ge_r n r owner (allocation owner) item hitem hAitem hAtwo
    (by
      have hceil : 0 ≤ (((n + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
  have hcomp := po_high_C_bundle_cost_lt_r n r hr owner hhigh (allocation comparison) hcomparison
  have hnonempty : allocation owner ≠ ∅ := by
    intro hempty
    rw [hempty] at hitem
    simp at hitem
  have hEfx := (hefx owner comparison).resolve_left hnonempty item hitem
  linarith

/-- The first case in the source proof of Proposition 2: if both agent groups
contain a no-large bundle, each of the `n - 1` A-chores would have to fit in
only `n - 2` remaining bundles, contradicting EFX. -/
theorem po_both_groups_no_large_contradiction
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (low high : Fin n) (hlow : low.val < n / 2) (hhigh : n / 2 ≤ high.val)
    (hlowB : allocation low ⊆ poBItems n) (hhighC : allocation high ⊆ poCItems n) :
    False := by
  have hne : low ≠ high := by
    intro heq
    have hval := congrArg Fin.val heq
    omega
  have hlowAempty : allocation low ∩ poAItems n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poA_B_disjoint n)
      (Finset.mem_inter.mp hitem).2 (hlowB (Finset.mem_inter.mp hitem).1)
  have hhighAempty : allocation high ∩ poAItems n = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro item hitem
    exact Finset.disjoint_left.mp (poA_C_disjoint n)
      (Finset.mem_inter.mp hitem).2 (hhighC (Finset.mem_inter.mp hitem).1)
  have hcap : ∀ owner, (allocation owner ∩ poAItems n).card ≤ 1 := by
    intro owner
    by_cases hownerLow : owner.val < n / 2
    · exact po_low_A_card_le_one_of_low_no_large n hn r hr allocation hefx owner low hownerLow hlowB
    · have hownerHigh : n / 2 ≤ owner.val := by omega
      exact po_high_A_card_le_one_of_high_no_large n r hr allocation hefx owner high hownerHigh hhighC
  let counts : Fin n → ℕ := fun owner => (allocation owner ∩ poAItems n).card
  have htotal : Finset.univ.sum counts = n - 1 := by
    dsimp [counts]
    rw [sum_card_inter_allocation_eq_card_inter allocation Finset.univ (poAItems n) halloc,
      Finset.inter_eq_right.mpr (fun item _ => Finset.mem_univ _), poAItems_card]
  let rest : Finset (Fin n) := (Finset.univ.erase low).erase high
  have hhighMem : high ∈ Finset.univ.erase low :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
  have hsumLow : (Finset.univ.erase low).sum counts + counts low = Finset.univ.sum counts :=
    Finset.sum_erase_add Finset.univ counts (Finset.mem_univ low)
  have hsumHigh : rest.sum counts + counts high = (Finset.univ.erase low).sum counts := by
    dsimp [rest]
    exact Finset.sum_erase_add (Finset.univ.erase low) counts hhighMem
  have hlowZero : counts low = 0 := by
    change (allocation low ∩ poAItems n).card = 0
    simp [hlowAempty]
  have hhighZero : counts high = 0 := by
    change (allocation high ∩ poAItems n).card = 0
    simp [hhighAempty]
  have hrestTotal : rest.sum counts = n - 1 := by
    rw [hlowZero] at hsumLow
    rw [hhighZero] at hsumHigh
    norm_num at hsumLow hsumHigh
    omega
  have hrestBound : rest.sum counts ≤ rest.sum (fun _ => 1) := by
    apply Finset.sum_le_sum
    intro owner _
    exact hcap owner
  have hrestCard : rest.card = n - 2 := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hhighMem,
      Finset.card_erase_of_mem (Finset.mem_univ low), Finset.card_univ, Fintype.card_fin]
    omega
  rw [Finset.sum_const, hrestCard] at hrestBound
  have hrestBound' : rest.sum counts ≤ n - 2 := by
    simpa only [nsmul_eq_mul, Nat.mul_one] using hrestBound
  omega

/-- In the `r > 2` regime of Theorem 2, a low-group bundle whose every chore
has cost different from `r` is made entirely of B-chores. -/
theorem po_low_bundle_subset_B_of_no_large
    (n : ℕ) (r : ℝ) (agent : Fin n) (hlow : agent.val < n / 2)
    (bundle : Finset (Fin (2 * n + 1)))
    (hnoLarge : ∀ item ∈ bundle, poCost n r agent item ≠ r) :
    bundle ⊆ poBItems n := by
  intro item hitem
  have hclass : item ∈ poAItems n ∪ poBItems n ∪ poCItems n := by
    rw [po_item_partition]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hclass with hAB | hC
  · rcases Finset.mem_union.mp hAB with hA | hB
    · exact (hnoLarge item hitem (poCost_on_A n r agent item hA)).elim
    · exact hB
  · exact (hnoLarge item hitem (poCost_on_C_low n r agent hlow item hC)).elim

/-- The B/C-swapped classification for a high-group bundle with no large
chore. -/
theorem po_high_bundle_subset_C_of_no_large
    (n : ℕ) (r : ℝ) (agent : Fin n) (hhigh : n / 2 ≤ agent.val)
    (bundle : Finset (Fin (2 * n + 1)))
    (hnoLarge : ∀ item ∈ bundle, poCost n r agent item ≠ r) :
    bundle ⊆ poCItems n := by
  intro item hitem
  have hclass : item ∈ poAItems n ∪ poBItems n ∪ poCItems n := by
    rw [po_item_partition]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hclass with hAB | hC
  · rcases Finset.mem_union.mp hAB with hA | hB
    · exact (hnoLarge item hitem (poCost_on_A n r agent item hA)).elim
    · exact (hnoLarge item hitem (poCost_on_B_high n r agent hhigh item hB)).elim
  · exact hC

/-- The low and high groups have the source cardinalities
`floor(n/2)` and `ceil(n/2)`. -/
theorem po_low_group_card (n : ℕ) :
    (Finset.univ.filter fun agent : Fin n => agent.val < n / 2).card = n / 2 := by
  simpa [Nat.min_eq_right (Nat.div_le_self n 2)] using
    (Fin.card_filter_val_lt (n := n) (m := n / 2))

theorem po_high_group_card (n : ℕ) :
    (Finset.univ.filter fun agent : Fin n => n / 2 ≤ agent.val).card = (n + 1) / 2 := by
  let low : Finset (Fin n) := Finset.univ.filter fun agent => agent.val < n / 2
  have hlow : low.card = n / 2 := by
    dsimp [low]
    exact po_low_group_card n
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun agent : Fin n => agent.val < n / 2)
  have hpartition' : low.card +
      (Finset.univ.filter fun agent : Fin n => n / 2 ≤ agent.val).card = n := by
    simpa only [low, Finset.card_univ, Fintype.card_fin, Nat.not_lt] using hpartition
  rw [hlow] at hpartition'
  omega

/-- The complete low-group half of Proposition 2: in an EFX allocation every
low-group agent owns a large (A or C) chore.  The proof combines the two
source subcases and the previously formalized two-no-large-bundle case. -/
theorem po_every_low_agent_has_large
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (agent : Fin n) (hlow : agent.val < n / 2) :
    ∃ item ∈ allocation agent, poCost n r agent item = r := by
  by_contra hnoLarge
  have hagentNoLarge : ∀ item ∈ allocation agent, poCost n r agent item ≠ r := by
    intro item hitem hcost
    exact hnoLarge ⟨item, hitem, hcost⟩
  have hagentB : allocation agent ⊆ poBItems n :=
    po_low_bundle_subset_B_of_no_large n r agent hlow (allocation agent) hagentNoLarge
  by_cases hSomeHighNoLarge : ∃ high : Fin n, n / 2 ≤ high.val ∧
      ¬ ∃ item ∈ allocation high, poCost n r high item = r
  · obtain ⟨high, hhigh, hhighNoLarge⟩ := hSomeHighNoLarge
    have hhighNoLarge' : ∀ item ∈ allocation high, poCost n r high item ≠ r := by
      intro item hitem hcost
      exact hhighNoLarge ⟨item, hitem, hcost⟩
    have hhighC : allocation high ⊆ poCItems n :=
      po_high_bundle_subset_C_of_no_large n r high hhigh (allocation high) hhighNoLarge'
    exact po_both_groups_no_large_contradiction n hn r hr allocation halloc hefx agent high
      hlow hhigh hagentB hhighC
  · have hhighNotC : ∀ high : Fin n, n / 2 ≤ high.val → ¬ allocation high ⊆ poCItems n := by
      intro high hhigh hsubset
      apply hSomeHighNoLarge
      refine ⟨high, hhigh, ?_⟩
      intro hexists
      obtain ⟨item, hitem, hcost⟩ := hexists
      have hitemC : item ∈ poCItems n := hsubset hitem
      have hCcost := poCost_on_C_high n r high hhigh item hitemC
      have hrOne : 1 < r := by linarith [po_r_gt_two n hn r hr]
      linarith
    by_cases hAllLowB : ∀ low : Fin n, low.val < n / 2 → allocation low ⊆ poBItems n
    · exact po_all_low_no_large_contradiction n hn r hr allocation halloc hefx hAllLowB hhighNotC
    · have hSomeLowNotB : ∃ low : Fin n, low.val < n / 2 ∧ ¬ allocation low ⊆ poBItems n := by
        push Not at hAllLowB
        exact hAllLowB
      obtain ⟨otherLow, hotherLow, hotherNotB⟩ := hSomeLowNotB
      exact po_one_low_no_large_one_low_large_contradiction n hn r hr allocation halloc hefx
        agent otherLow hlow hotherLow hagentB hotherNotB hhighNotC

/-- The high-group half of Proposition 2.  Having first ruled out B-only
low-group bundles, the two C-only high-group subcases yield the symmetric
contradictions. -/
theorem po_every_high_agent_has_large
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (agent : Fin n) (hhigh : n / 2 ≤ agent.val) :
    ∃ item ∈ allocation agent, poCost n r agent item = r := by
  have hlowNotB : ∀ low : Fin n, low.val < n / 2 → ¬ allocation low ⊆ poBItems n := by
    intro low hlow hsubset
    obtain ⟨item, hitem, hcost⟩ := po_every_low_agent_has_large n hn r hr allocation halloc hefx
      low hlow
    have hBcost := poCost_on_B_low n r low hlow item (hsubset hitem)
    have hrOne : 1 < r := by linarith [po_r_gt_two n hn r hr]
    linarith
  by_contra hnoLarge
  have hagentNoLarge : ∀ item ∈ allocation agent, poCost n r agent item ≠ r := by
    intro item hitem hcost
    exact hnoLarge ⟨item, hitem, hcost⟩
  have hagentC : allocation agent ⊆ poCItems n :=
    po_high_bundle_subset_C_of_no_large n r agent hhigh (allocation agent) hagentNoLarge
  by_cases hAllHighC : ∀ high : Fin n, n / 2 ≤ high.val → allocation high ⊆ poCItems n
  · exact po_all_high_no_large_contradiction n hn r hr allocation halloc hefx hAllHighC hlowNotB
  · have hSomeHighNotC : ∃ high : Fin n, n / 2 ≤ high.val ∧ ¬ allocation high ⊆ poCItems n := by
      push Not at hAllHighC
      exact hAllHighC
    obtain ⟨otherHigh, hotherHigh, hotherNotC⟩ := hSomeHighNotC
    exact po_one_high_no_large_one_high_large_contradiction n hn r hr allocation halloc hefx
      agent otherHigh hhigh hotherHigh hagentC hotherNotC hlowNotB

/-- Proposition 2 of the source: every agent in an EFX allocation of the
Theorem-2 construction receives a chore of cost `r`. -/
theorem po_every_agent_has_large
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (agent : Fin n) :
    ∃ item ∈ allocation agent, poCost n r agent item = r := by
  by_cases hlow : agent.val < n / 2
  · exact po_every_low_agent_has_large n hn r hr allocation halloc hefx agent hlow
  · exact po_every_high_agent_has_large n hn r hr allocation halloc hefx agent (by omega)

/-- The first lower bound in Proposition 3 of the source: once every bundle
contains a large chore, no EFX bundle can cost less than `r + 1`. -/
theorem po_every_agent_cost_ge_r_add_one
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (agent : Fin n) :
    r + 1 ≤ additiveChoreCost (poCost n r) agent (allocation agent) := by
  by_contra hcost
  obtain ⟨large, hlarge, hlargeCost⟩ := po_every_agent_has_large n hn r hr allocation halloc hefx agent
  have hagentCard : (allocation agent).card ≤ 1 := by
    by_contra hnot
    have hcard : 1 < (allocation agent).card := by omega
    obtain ⟨other, hother, hotherNe⟩ := Finset.exists_mem_ne hcard large
    have hlower := po_cost_ge_r_add_one_of_large_and_other n r
      (by linarith [po_r_gt_two n hn r hr]) agent (allocation agent) large other hlarge
      hlargeCost hother hotherNe
    linarith
  have hagentSingleton : allocation agent = {large} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · exact hlarge
    · intro item hitem
      exact Finset.card_le_one.mp hagentCard item hitem large hlarge
  let counts : Fin n → ℕ := fun owner => (allocation owner).card
  have htotal : Finset.univ.sum counts = 2 * n + 1 := by
    dsimp [counts]
    simpa only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin] using
      (sum_card_inter_allocation_eq_card_inter allocation Finset.univ Finset.univ halloc)
  have hagentCount : counts agent = 1 := by
    change (allocation agent).card = 1
    rw [hagentSingleton]
    simp
  have hcomparisonCost : ∀ owner : Fin n,
      additiveChoreCost (poCost n r) owner (allocation agent) ≤ r := by
    intro owner
    rw [hagentSingleton]
    simp only [additiveChoreCost, Finset.sum_singleton]
    exact poCost_le_r n r (by linarith [po_r_gt_two n hn r hr]) owner large
  have hOtherCap : ∀ owner ∈ Finset.univ.erase agent, counts owner ≤ 2 := by
    intro owner howner
    obtain ⟨ownerLarge, hownerLarge, hownerLargeCost⟩ :=
      po_every_agent_has_large n hn r hr allocation halloc hefx owner
    change (allocation owner).card ≤ 2
    exact po_bundle_card_le_two_of_large_vs_cost_le_r n r
      (by linarith [po_r_gt_two n hn r hr]) allocation hefx owner agent
      (hcomparisonCost owner) ownerLarge hownerLarge hownerLargeCost
  have hrestBound : (Finset.univ.erase agent).sum counts ≤
      (Finset.univ.erase agent).sum (fun _ => 2) := by
    apply Finset.sum_le_sum
    intro owner howner
    exact hOtherCap owner howner
  have hrestCard : (Finset.univ.erase agent).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ agent), Finset.card_univ, Fintype.card_fin]
  have hrestBound' : (Finset.univ.erase agent).sum counts ≤ (n - 1) * 2 := by
    calc
      (Finset.univ.erase agent).sum counts ≤ (Finset.univ.erase agent).sum (fun _ => 2) :=
        hrestBound
      _ = (n - 1) * 2 := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), hrestCard]
  have hsplit := Finset.sum_erase_add Finset.univ counts (Finset.mem_univ agent)
  rw [hagentCount] at hsplit
  have hsum : (Finset.univ.erase agent).sum counts + 1 = 2 * n + 1 := by
    calc
      (Finset.univ.erase agent).sum counts + 1 = Finset.univ.sum counts := hsplit
      _ = 2 * n + 1 := htotal
  omega

/-- The second lower bound in Proposition 3: some EFX bundle has cost at
least `r + 2`.  Otherwise every bundle would contain exactly two chores,
contradicting the odd total `2n + 1`. -/
theorem po_some_agent_cost_ge_r_add_two
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation) :
    ∃ agent : Fin n, r + 2 ≤ additiveChoreCost (poCost n r) agent (allocation agent) := by
  by_contra hnot
  push Not at hnot
  let counts : Fin n → ℕ := fun owner => (allocation owner).card
  have hcountEqTwo : ∀ agent : Fin n, counts agent = 2 := by
    intro agent
    obtain ⟨large, hlarge, hlargeCost⟩ :=
      po_every_agent_has_large n hn r hr allocation halloc hefx agent
    have hupper : additiveChoreCost (poCost n r) agent (allocation agent) < r + 2 := by
      exact hnot agent
    have hcardUpper : counts agent ≤ 2 := by
      by_contra hnotUpper
      have hcard : 2 < (allocation agent).card := by
        change ¬ counts agent ≤ 2 at hnotUpper
        change 2 < counts agent
        omega
      have heraseCard : 1 < ((allocation agent).erase large).card := by
        rw [Finset.card_erase_of_mem hlarge]
        omega
      obtain ⟨first, hfirstErase, _⟩ := Finset.exists_mem_ne heraseCard large
      obtain ⟨second, hsecondErase, hsecondNeFirst⟩ := Finset.exists_mem_ne heraseCard first
      have hfirst : first ∈ allocation agent := Finset.mem_erase.mp hfirstErase |>.2
      have hfirstNeLarge : first ≠ large := Finset.mem_erase.mp hfirstErase |>.1
      have hsecond : second ∈ allocation agent := Finset.mem_erase.mp hsecondErase |>.2
      have hsecondNeLarge : second ≠ large := Finset.mem_erase.mp hsecondErase |>.1
      have hlower := po_cost_ge_r_add_two_of_large_and_others n r
        (by linarith [po_r_gt_two n hn r hr]) agent (allocation agent) large first second hlarge
        hlargeCost hfirst hfirstNeLarge hsecond hsecondNeLarge hsecondNeFirst
      linarith
    have hcardLower : 2 ≤ counts agent := by
      by_contra hnotLower
      have hcard : (allocation agent).card ≤ 1 := by
        change ¬ 2 ≤ counts agent at hnotLower
        change counts agent ≤ 1
        omega
      have hsingleton : allocation agent = {large} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        constructor
        · exact hlarge
        · intro item hitem
          exact Finset.card_le_one.mp hcard item hitem large hlarge
      have hlower := po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx agent
      rw [hsingleton] at hlower
      simp only [additiveChoreCost, Finset.sum_singleton, hlargeCost] at hlower
      linarith
    omega
  have htotal : Finset.univ.sum counts = 2 * n + 1 := by
    dsimp [counts]
    simpa only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin] using
      (sum_card_inter_allocation_eq_card_inter allocation Finset.univ Finset.univ halloc)
  have hsumEq : Finset.univ.sum counts = 2 * n := by
    calc
      Finset.univ.sum counts = Finset.univ.sum (fun _ => 2) := by
        apply Finset.sum_congr rfl
        intro agent _
        exact hcountEqTwo agent
      _ = 2 * n := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_comm _ _
  omega

/-- Owner map for the Pareto-improving allocation in the source when the
distinguished `focal` agent belongs to the low group.  A-items go to their
matching agents; the last B-item is the focal agent's second B-item; and the
last high agent receives the extra C-item. -/
def poLowImprovementOwner (n : ℕ) (focal : Fin n) (item : Fin (2 * n + 1)) : Fin n :=
  if hA : item.val < n - 1 then
    ⟨item.val, by omega⟩
  else if hB : item.val < n + n / 2 then
    if hBLast : item.val < n + n / 2 - 1 then
      ⟨item.val - (n - 1), by omega⟩
    else focal
  else if hCBeforeLast : item.val < 2 * n then
    ⟨item.val - n, by omega⟩
  else
    ⟨n - 1, by have hfocal := focal.isLt; omega⟩

/-- The source's low-focal Pareto-improving allocation, represented through
its total item-owner map. -/
noncomputable def poLowImprovement (n : ℕ) (focal : Fin n) :
    Allocation (Fin n) (Fin (2 * n + 1)) :=
  allocationOfOwner Finset.univ (fun item => some (poLowImprovementOwner n focal item))

theorem poLowImprovement_feasible (n : ℕ) (focal : Fin n) :
    IsAllocationOf (poLowImprovement n focal) (Finset.univ : Finset (Fin (2 * n + 1))) := by
  apply isAllocationOf_allocationOfOwner
  intro item _
  exact ⟨poLowImprovementOwner n focal item, rfl⟩

/-- Named representatives used to state the low-focal bundles of the explicit
Pareto improvement. -/
def poAFor (n : ℕ) (agent : Fin n) : Fin (2 * n + 1) :=
  ⟨agent.val, by omega⟩

def poBFor (n : ℕ) (low : Fin n) (hlow : low.val < n / 2) : Fin (2 * n + 1) :=
  ⟨n - 1 + low.val, by omega⟩

def poBLast (n : ℕ) (hn : 1 ≤ n) : Fin (2 * n + 1) :=
  ⟨n + n / 2 - 1, by omega⟩

def poCFor (n : ℕ) (high : Fin n) : Fin (2 * n + 1) :=
  ⟨n + high.val, by omega⟩

def poCLast (n : ℕ) : Fin (2 * n + 1) := ⟨2 * n, by omega⟩

theorem poLowImprovement_focal_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal : Fin n) (hlow : focal.val < n / 2) :
    poLowImprovement n focal focal =
      {poAFor n focal, poBFor n focal hlow, poBLast n (by omega)} := by
  classical
  ext item
  simp only [poLowImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poLowImprovementOwner
  split
  · simp [poAFor, poBFor, poBLast]
    omega
  · split
    · split
      · simp [poAFor, poBFor, poBLast]
        omega
      · simp [poAFor, poBFor, poBLast]
        omega
    · split
      · simp [poAFor, poBFor, poBLast]
        omega
      · simp [poAFor, poBFor, poBLast]
        omega

theorem poLowImprovement_focal_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal : Fin n) (hlow : focal.val < n / 2) :
    additiveChoreCost (poCost n r) focal (poLowImprovement n focal focal) = r + 2 := by
  rw [poLowImprovement_focal_bundle n hn focal hlow]
  rw [poCost_low_bundle n r focal hlow]
  have hA : ({poAFor n focal, poBFor n focal hlow, poBLast n (by omega)} ∩ poAItems n) =
      {poAFor n focal} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poAItems, poAFor, poBFor, poBLast, Fin.lt_def]
    omega
  have hB : ({poAFor n focal, poBFor n focal hlow, poBLast n (by omega)} ∩ poBItems n) =
      {poBFor n focal hlow, poBLast n (by omega)} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poBItems, poAFor, poBFor, poBLast, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  have hC : ({poAFor n focal, poBFor n focal hlow, poBLast n (by omega)} ∩ poCItems n) = ∅ := by
    ext item
    simp [poCItems, poAFor, poBFor, poBLast, Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  rw [hA, hB, hC]
  have hBne : poBFor n focal hlow ≠ poBLast n (by omega) := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [poBFor, poBLast] at hval
    omega
  rw [Finset.card_singleton, Finset.card_pair hBne]
  norm_num

theorem poLowImprovement_other_low_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal low : Fin n)
    (hfocal : focal.val < n / 2) (hlow : low.val < n / 2) (hne : low ≠ focal) :
    poLowImprovement n focal low = {poAFor n low, poBFor n low hlow} := by
  classical
  ext item
  simp only [poLowImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poLowImprovementOwner
  split
  · simp [poAFor, poBFor]
    omega
  · split
    · split
      · simp [poAFor, poBFor]
        omega
      · simp [poAFor, poBFor]
        omega
    · split
      · simp [poAFor, poBFor]
        omega
      · simp [poAFor, poBFor]
        omega

theorem poLowImprovement_other_low_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal low : Fin n)
    (hfocal : focal.val < n / 2) (hlow : low.val < n / 2) (hne : low ≠ focal) :
    additiveChoreCost (poCost n r) low (poLowImprovement n focal low) = r + 1 := by
  rw [poLowImprovement_other_low_bundle n hn focal low hfocal hlow hne]
  rw [poCost_low_bundle n r low hlow]
  have hA : ({poAFor n low, poBFor n low hlow} ∩ poAItems n) = {poAFor n low} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poAItems, poAFor, poBFor, Fin.lt_def]
    omega
  have hB : ({poAFor n low, poBFor n low hlow} ∩ poBItems n) = {poBFor n low hlow} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poBItems, poAFor, poBFor, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  have hC : ({poAFor n low, poBFor n low hlow} ∩ poCItems n) = ∅ := by
    ext item
    simp [poCItems, poAFor, poBFor, Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  rw [hA, hB, hC]
  norm_num

theorem poLowImprovement_nonlast_high_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal high : Fin n)
    (hfocal : focal.val < n / 2) (hhigh : n / 2 ≤ high.val) (hhighLast : high.val < n - 1) :
    poLowImprovement n focal high = {poAFor n high, poCFor n high} := by
  classical
  ext item
  simp only [poLowImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poLowImprovementOwner
  split
  · simp [poAFor, poCFor]
    omega
  · split
    · split
      · simp [poAFor, poCFor]
        omega
      · simp [poAFor, poCFor]
        omega
    · split
      · simp [poAFor, poCFor]
        omega
      · simp [poAFor, poCFor]
        omega

theorem poLowImprovement_nonlast_high_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal high : Fin n)
    (hfocal : focal.val < n / 2) (hhigh : n / 2 ≤ high.val) (hhighLast : high.val < n - 1) :
    additiveChoreCost (poCost n r) high (poLowImprovement n focal high) = r + 1 := by
  rw [poLowImprovement_nonlast_high_bundle n hn focal high hfocal hhigh hhighLast]
  rw [poCost_high_bundle n r high hhigh]
  have hA : ({poAFor n high, poCFor n high} ∩ poAItems n) = {poAFor n high} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poAItems, poAFor, poCFor, Fin.lt_def]
    omega
  have hB : ({poAFor n high, poCFor n high} ∩ poBItems n) = ∅ := by
    ext item
    simp [poBItems, poAFor, poCFor, Fin.lt_def, Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  have hC : ({poAFor n high, poCFor n high} ∩ poCItems n) = {poCFor n high} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poCItems, poAFor, poCFor, Fin.le_iff_val_le_val]
    omega
  rw [hA, hB, hC]
  norm_num

def poLastHigh (n : ℕ) (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

theorem poLowImprovement_last_high_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal : Fin n) (hfocal : focal.val < n / 2) :
    poLowImprovement n focal (poLastHigh n (by omega)) =
      {poCFor n (poLastHigh n (by omega)), poCLast n} := by
  classical
  ext item
  simp only [poLowImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poLowImprovementOwner
  split
  · simp [poCFor, poCLast, poLastHigh]
    omega
  · split
    · split
      · simp [poCFor, poCLast, poLastHigh]
        omega
      · simp [poCFor, poCLast, poLastHigh]
        omega
    · split
      · simp [poCFor, poCLast, poLastHigh]
        omega
      · simp [poCFor, poCLast, poLastHigh]
        omega

theorem poLowImprovement_last_high_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal : Fin n) (hfocal : focal.val < n / 2) :
    additiveChoreCost (poCost n r) (poLastHigh n (by omega))
      (poLowImprovement n focal (poLastHigh n (by omega))) = 2 := by
  rw [poLowImprovement_last_high_bundle n hn focal hfocal]
  rw [poCost_high_bundle n r (poLastHigh n (by omega)) (by
    change n / 2 ≤ n - 1
    omega)]
  have hA : ({poCFor n (poLastHigh n (by omega)), poCLast n} ∩ poAItems n) = ∅ := by
    ext item
    simp [poAItems, poCFor, poCLast, poLastHigh, Fin.lt_def, Fin.ext_iff]
    omega
  have hB : ({poCFor n (poLastHigh n (by omega)), poCLast n} ∩ poBItems n) = ∅ := by
    ext item
    simp [poBItems, poCFor, poCLast, poLastHigh, Fin.lt_def, Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  have hC : ({poCFor n (poLastHigh n (by omega)), poCLast n} ∩ poCItems n) =
      {poCFor n (poLastHigh n (by omega)), poCLast n} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poCItems, poCFor, poCLast, poLastHigh, Fin.le_iff_val_le_val]
    omega
  rw [hA, hB, hC]
  have hne : poCFor n (poLastHigh n (by omega)) ≠ poCLast n := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [poCFor, poCLast, poLastHigh] at hval
    omega
  rw [Finset.card_pair hne]
  norm_num

/-! ## Explicit EFX witness for the Theorem-2 instance

The paragraph immediately after the source's cost table is mathematically
important: it makes the EFX--Pareto incompatibility nonvacuous by exhibiting
an EFX allocation of the constructed instance.  Every agent except the final
high-group agent receives a matching A-item and a small group item.  The final
agent receives the remaining B-item and the last two C-items.
-/

/-- Total owner map for the source's explicit EFX witness. -/
def poEfxWitnessOwner (n : ℕ) (hn : 1 ≤ n)
    (item : Fin (2 * n + 1)) : Fin n :=
  if hA : item.val < n - 1 then
    ⟨item.val, by omega⟩
  else if hB : item.val < n + n / 2 then
    if hBLast : item.val < n + n / 2 - 1 then
      ⟨item.val - (n - 1), by omega⟩
    else
      poLastHigh n hn
  else if hCBeforeLast : item.val < 2 * n then
    ⟨item.val - n, by omega⟩
  else
    poLastHigh n hn

/-- The source's explicit EFX allocation of the Theorem-2 instance. -/
noncomputable def poEfxWitness (n : ℕ) (hn : 1 ≤ n) :
    Allocation (Fin n) (Fin (2 * n + 1)) :=
  allocationOfOwner Finset.univ (fun item => some (poEfxWitnessOwner n hn item))

theorem poEfxWitness_feasible (n : ℕ) (hn : 1 ≤ n) :
    IsAllocationOf (poEfxWitness n hn) (Finset.univ : Finset (Fin (2 * n + 1))) := by
  apply isAllocationOf_allocationOfOwner
  intro item _
  exact ⟨poEfxWitnessOwner n hn item, rfl⟩

theorem poEfxWitness_low_bundle
    (n : ℕ) (hn : 4 ≤ n) (low : Fin n) (hlow : low.val < n / 2) :
    poEfxWitness n (by omega) low = {poAFor n low, poBFor n low hlow} := by
  classical
  ext item
  simp only [poEfxWitness, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poEfxWitnessOwner
  split
  · simp [poAFor, poBFor, poLastHigh]
    omega
  · split
    · split
      · simp [poAFor, poBFor, poLastHigh]
        omega
      · simp [poAFor, poBFor, poLastHigh]
        omega
    · split
      · simp [poAFor, poBFor, poLastHigh]
        omega
      · simp [poAFor, poBFor, poLastHigh]
        omega

theorem poEfxWitness_nonlast_high_bundle
    (n : ℕ) (hn : 4 ≤ n) (high : Fin n)
    (hhigh : n / 2 ≤ high.val) (hnotLast : high.val < n - 1) :
    poEfxWitness n (by omega) high = {poAFor n high, poCFor n high} := by
  classical
  ext item
  simp only [poEfxWitness, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poEfxWitnessOwner
  split
  · simp [poAFor, poCFor, poLastHigh]
    omega
  · split
    · split
      · simp [poAFor, poCFor, poLastHigh]
        omega
      · simp [poAFor, poCFor, poLastHigh]
        omega
    · split
      · simp [poAFor, poCFor, poLastHigh]
        omega
      · simp [poAFor, poCFor, poLastHigh]
        omega

theorem poEfxWitness_last_high_bundle (n : ℕ) (hn : 4 ≤ n) :
    poEfxWitness n (by omega) (poLastHigh n (by omega)) =
      {poBLast n (by omega), poCFor n (poLastHigh n (by omega)), poCLast n} := by
  classical
  ext item
  simp only [poEfxWitness, allocationOfOwner, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poEfxWitnessOwner
  split
  · simp [poBLast, poCFor, poCLast, poLastHigh]
    omega
  · split
    · split
      · simp [poBLast, poCFor, poCLast, poLastHigh]
        omega
      · simp [poBLast, poCFor, poCLast, poLastHigh]
        omega
    · split
      · simp [poBLast, poCFor, poCLast, poLastHigh]
        omega
      · simp [poBLast, poCFor, poCLast, poLastHigh]
        omega

/-- Every bundle in the witness costs every observer at least `r + 1`. -/
theorem poEfxWitness_cost_lower
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (hr : 2 < r) (observer owner : Fin n) :
    r + 1 ≤ additiveChoreCost (poCost n r) observer (poEfxWitness n (by omega) owner) := by
  by_cases hownerLow : owner.val < n / 2
  · rw [poEfxWitness_low_bundle n hn owner hownerLow]
    apply po_cost_ge_r_add_one_of_large_and_other n r (by linarith) observer
      {poAFor n owner, poBFor n owner hownerLow} (poAFor n owner) (poBFor n owner hownerLow)
    · simp
    · apply poCost_on_A
      simp [poAItems, poAFor]
      omega
    · simp
    · intro heq
      have hval := congrArg Fin.val heq
      dsimp [poAFor, poBFor] at hval
      omega
  · have hownerHigh : n / 2 ≤ owner.val := le_of_not_gt hownerLow
    by_cases hownerLast : owner.val < n - 1
    · rw [poEfxWitness_nonlast_high_bundle n hn owner hownerHigh hownerLast]
      apply po_cost_ge_r_add_one_of_large_and_other n r (by linarith) observer
        {poAFor n owner, poCFor n owner} (poAFor n owner) (poCFor n owner)
      · simp
      · apply poCost_on_A
        simp [poAItems, poAFor]
        omega
      · simp
      · intro heq
        have hval := congrArg Fin.val heq
        dsimp [poAFor, poCFor] at hval
        omega
    · have hownerEq : owner = poLastHigh n (by omega) := by
        apply Fin.ext
        simp [poLastHigh]
        omega
      rw [hownerEq]
      rw [poEfxWitness_last_high_bundle n hn]
      by_cases hobserverLow : observer.val < n / 2
      · apply po_cost_ge_r_add_one_of_large_and_other n r (by linarith) observer
          {poBLast n (by omega), poCFor n (poLastHigh n (by omega)), poCLast n}
          (poCFor n (poLastHigh n (by omega))) (poBLast n (by omega))
        · simp
        · apply poCost_on_C_low n r observer hobserverLow
          simp [poCItems, poCFor, poLastHigh]
          omega
        · simp
        · intro heq
          have hval := congrArg Fin.val heq
          dsimp [poCFor, poLastHigh, poBLast] at hval
          omega
      · have hobserverHigh : n / 2 ≤ observer.val := le_of_not_gt hobserverLow
        apply po_cost_ge_r_add_one_of_large_and_other n r (by linarith) observer
          {poBLast n (by omega), poCFor n (poLastHigh n (by omega)), poCLast n}
          (poBLast n (by omega)) (poCFor n (poLastHigh n (by omega)))
        · simp
        · apply poCost_on_B_high n r observer hobserverHigh
          simp [poBItems, poBLast]
          omega
        · simp
        · intro heq
          have hval := congrArg Fin.val heq
          dsimp [poBLast, poCFor, poLastHigh] at hval
          omega

/-- Every owner values her own witness bundle at most `r + 2`. -/
theorem poEfxWitness_own_cost_upper
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (owner : Fin n) :
    additiveChoreCost (poCost n r) owner (poEfxWitness n (by omega) owner) ≤ r + 2 := by
  by_cases hownerLow : owner.val < n / 2
  · rw [poEfxWitness_low_bundle n hn owner hownerLow]
    have hA : poAFor n owner ∈ poAItems n := by
      simp [poAItems, poAFor]
      omega
    have hB : poBFor n owner hownerLow ∈ poBItems n := by
      simp [poBItems, poBFor]
      omega
    have hne : poBFor n owner hownerLow ≠ poAFor n owner := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [poAFor, poBFor] at hval
      omega
    unfold additiveChoreCost
    rw [Finset.sum_insert (by simpa using Ne.symm hne), Finset.sum_singleton,
      poCost_on_A n r owner (poAFor n owner) hA,
      poCost_on_B_low n r owner hownerLow (poBFor n owner hownerLow) hB]
    linarith
  · have hownerHigh : n / 2 ≤ owner.val := le_of_not_gt hownerLow
    by_cases hownerLast : owner.val < n - 1
    · rw [poEfxWitness_nonlast_high_bundle n hn owner hownerHigh hownerLast]
      have hA : poAFor n owner ∈ poAItems n := by
        simp [poAItems, poAFor]
        omega
      have hC : poCFor n owner ∈ poCItems n := by
        simp [poCItems, poCFor]
        omega
      have hne : poCFor n owner ≠ poAFor n owner := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [poAFor, poCFor] at hval
        omega
      unfold additiveChoreCost
      rw [Finset.sum_insert (by simpa using Ne.symm hne), Finset.sum_singleton,
        poCost_on_A n r owner (poAFor n owner) hA,
        poCost_on_C_high n r owner hownerHigh (poCFor n owner) hC]
      linarith
    · have hownerEq : owner = poLastHigh n (by omega) := by
        apply Fin.ext
        simp [poLastHigh]
        omega
      rw [hownerEq]
      rw [poEfxWitness_last_high_bundle n hn,
        poCost_high_bundle n r (poLastHigh n (by omega)) (by
          change n / 2 ≤ n - 1
          omega)]
      have hA : ({poBLast n (by omega), poCFor n (poLastHigh n (by omega)), poCLast n} ∩
          poAItems n) = ∅ := by
        ext item
        simp [poAItems, poBLast, poCFor, poCLast, poLastHigh, Fin.lt_def, Fin.ext_iff]
        omega
      have hB : ({poBLast n (by omega), poCFor n (poLastHigh n (by omega)), poCLast n} ∩
          poBItems n) = {poBLast n (by omega)} := by
        ext item
        simp [poBItems, poBLast, poCFor, poCLast, poLastHigh, Fin.lt_def,
          Fin.le_iff_val_le_val, Fin.ext_iff]
        omega
      have hC : ({poBLast n (by omega), poCFor n (poLastHigh n (by omega)), poCLast n} ∩
          poCItems n) = {poCFor n (poLastHigh n (by omega)), poCLast n} := by
        ext item
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        simp [poCItems, poBLast, poCFor, poCLast, poLastHigh, Fin.le_iff_val_le_val]
        omega
      rw [hA, hB, hC]
      have hne : poCFor n (poLastHigh n (by omega)) ≠ poCLast n := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [poCFor, poCLast, poLastHigh] at hval
        omega
      rw [Finset.card_singleton, Finset.card_pair hne]
      norm_num

/-- The source's displayed construction is an EFX allocation, so Theorem 2's
incompatibility instance is nonvacuous. -/
theorem poEfxWitness_is_efx
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (hr : 2 < r) :
    EFXForChores (additiveChoreCost (poCost n r)) (poEfxWitness n (by omega)) := by
  intro owner comparison
  right
  intro item hitem
  rw [additiveChoreCost_erase (poCost n r) owner
    (poEfxWitness n (by omega) owner) item hitem]
  have hitemLower : 1 ≤ poCost n r owner item := poCost_ge_one n r (by linarith) owner item
  have hown := poEfxWitness_own_cost_upper n hn r owner
  have hcomparison := poEfxWitness_cost_lower n hn r hr owner comparison
  linarith

/-- The source's explicit Pareto improvement when the agent whose original
EFX cost is at least `r + 2` lies in the low group. -/
theorem po_low_improvement_pareto_dominates
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (focal : Fin n) (hfocal : focal.val < n / 2)
    (hfocalCost : r + 2 ≤ additiveChoreCost (poCost n r) focal (allocation focal)) :
    ParetoDominatesForChores (additiveChoreCost (poCost n r)) allocation
      (poLowImprovement n focal) := by
  constructor
  · intro agent
    by_cases hlow : agent.val < n / 2
    · by_cases hagent : agent = focal
      · subst agent
        rw [poLowImprovement_focal_cost n hn r focal hfocal]
        exact hfocalCost
      · rw [poLowImprovement_other_low_cost n hn r focal agent hfocal hlow hagent]
        exact po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx agent
    · have hhigh : n / 2 ≤ agent.val := by omega
      by_cases hspecial : agent = poLastHigh n (by omega)
      · rw [hspecial, poLowImprovement_last_high_cost n hn r focal hfocal]
        have hlower := po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx
          (poLastHigh n (by omega))
        have hrTwo := po_r_gt_two n hn r hr
        linarith
      · have hnotLast : agent.val < n - 1 := by
          by_contra hnot
          have hlast : agent.val = n - 1 := by
            have hge : n - 1 ≤ agent.val := by omega
            omega
          apply hspecial
          apply Fin.ext
          simp [poLastHigh, hlast]
        rw [poLowImprovement_nonlast_high_cost n hn r focal agent hfocal hhigh hnotLast]
        exact po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx agent
  · refine ⟨poLastHigh n (by omega), ?_⟩
    rw [poLowImprovement_last_high_cost n hn r focal hfocal]
    have hlower := po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx
      (poLastHigh n (by omega))
    have hrTwo := po_r_gt_two n hn r hr
    linarith

/-- Owner map for the source's Pareto improvement when the focal agent is in
the high group.  The last low agent is the B-only special agent; the A-item
that would have gone to her supplies the last high agent instead. -/
def poHighImprovementOwner (n : ℕ) (focal : Fin n) (item : Fin (2 * n + 1)) : Fin n :=
  if hA : item.val < n - 1 then
    if hspecialLow : item.val = n / 2 - 1 then
      ⟨n - 1, by have hfocal := focal.isLt; omega⟩
    else ⟨item.val, by omega⟩
  else if hB : item.val < n + n / 2 then
    if hBLast : item.val < n + n / 2 - 1 then
      ⟨item.val - (n - 1), by omega⟩
    else ⟨n / 2 - 1, by have hfocal := focal.isLt; omega⟩
  else if hCBeforeLast : item.val < 2 * n then
    ⟨item.val - n, by omega⟩
  else focal

noncomputable def poHighImprovement (n : ℕ) (focal : Fin n) :
    Allocation (Fin n) (Fin (2 * n + 1)) :=
  allocationOfOwner Finset.univ (fun item => some (poHighImprovementOwner n focal item))

theorem poHighImprovement_feasible (n : ℕ) (focal : Fin n) :
    IsAllocationOf (poHighImprovement n focal) (Finset.univ : Finset (Fin (2 * n + 1))) := by
  apply isAllocationOf_allocationOfOwner
  intro item _
  exact ⟨poHighImprovementOwner n focal item, rfl⟩

def poLastLow (n : ℕ) (focal : Fin n) : Fin n :=
  ⟨n / 2 - 1, by have hfocal := focal.isLt; omega⟩

def poAForHigh (n : ℕ) (focal high : Fin n) : Fin (2 * n + 1) :=
  if high.val = n - 1 then poAFor n (poLastLow n focal) else poAFor n high

theorem poHighImprovement_focal_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal : Fin n) (hhigh : n / 2 ≤ focal.val) :
    poHighImprovement n focal focal =
      {poAForHigh n focal focal, poCFor n focal, poCLast n} := by
  classical
  by_cases hfocalLast : focal.val = n - 1
  · ext item
    simp only [poHighImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ,
      true_and, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    unfold poHighImprovementOwner
    split
    · split
      · simp [poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast]
        omega
      · simp [poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast]
        omega
    · split
      · split
        · simp [poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast]
          omega
      · split
        · simp [poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast]
          omega
  · ext item
    simp only [poHighImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ,
      true_and, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    unfold poHighImprovementOwner
    split
    · split
      · simp [poAForHigh, poAFor, poCFor, poCLast, hfocalLast]
        omega
      · simp [poAForHigh, poAFor, poCFor, poCLast, hfocalLast]
        omega
    · split
      · split
        · simp [poAForHigh, poAFor, poCFor, poCLast, hfocalLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, poCLast, hfocalLast]
          omega
      · split
        · simp [poAForHigh, poAFor, poCFor, poCLast, hfocalLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, poCLast, hfocalLast]
          omega

theorem poHighImprovement_focal_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal : Fin n) (hhigh : n / 2 ≤ focal.val) :
    additiveChoreCost (poCost n r) focal (poHighImprovement n focal focal) = r + 2 := by
  rw [poHighImprovement_focal_bundle n hn focal hhigh]
  rw [poCost_high_bundle n r focal hhigh]
  by_cases hfocalLast : focal.val = n - 1
  · have hA : ({poAForHigh n focal focal, poCFor n focal, poCLast n} ∩ poAItems n) =
        {poAForHigh n focal focal} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poAItems, poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast, Fin.lt_def]
      omega
    have hB : ({poAForHigh n focal focal, poCFor n focal, poCLast n} ∩ poBItems n) = ∅ := by
      ext item
      simp [poBItems, poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast,
        Fin.lt_def, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hC : ({poAForHigh n focal focal, poCFor n focal, poCLast n} ∩ poCItems n) =
        {poCFor n focal, poCLast n} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poCItems, poAForHigh, poAFor, poCFor, poCLast, poLastLow, hfocalLast,
        Fin.le_iff_val_le_val]
      omega
    rw [hA, hB, hC]
    have hCne : poCFor n focal ≠ poCLast n := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [poCFor, poCLast] at hval
      omega
    rw [Finset.card_singleton, Finset.card_pair hCne]
    norm_num
  · have hA : ({poAForHigh n focal focal, poCFor n focal, poCLast n} ∩ poAItems n) =
        {poAForHigh n focal focal} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poAItems, poAForHigh, poAFor, poCFor, poCLast, hfocalLast, Fin.lt_def]
      omega
    have hB : ({poAForHigh n focal focal, poCFor n focal, poCLast n} ∩ poBItems n) = ∅ := by
      ext item
      simp [poBItems, poAForHigh, poAFor, poCFor, poCLast, hfocalLast,
        Fin.lt_def, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hC : ({poAForHigh n focal focal, poCFor n focal, poCLast n} ∩ poCItems n) =
        {poCFor n focal, poCLast n} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poCItems, poAForHigh, poAFor, poCFor, poCLast, hfocalLast,
        Fin.le_iff_val_le_val]
      omega
    rw [hA, hB, hC]
    have hCne : poCFor n focal ≠ poCLast n := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [poCFor, poCLast] at hval
      omega
    rw [Finset.card_singleton, Finset.card_pair hCne]
    norm_num

theorem poHighImprovement_last_low_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal : Fin n) (hhigh : n / 2 ≤ focal.val) :
    poHighImprovement n focal (poLastLow n focal) =
      {poBFor n (poLastLow n focal) (by
        change n / 2 - 1 < n / 2
        omega), poBLast n (by omega)} := by
  classical
  ext item
  simp only [poHighImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ,
    true_and, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poHighImprovementOwner
  split
  · split
    · simp [poBFor, poBLast, poLastLow]
      omega
    · simp [poBFor, poBLast, poLastLow]
      omega
  · split
    · split
      · simp [poBFor, poBLast, poLastLow]
        omega
      · simp [poBFor, poBLast, poLastLow]
        omega
    · split
      · simp [poBFor, poBLast, poLastLow]
        omega
      · simp [poBFor, poBLast, poLastLow]
        omega

theorem poHighImprovement_last_low_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal : Fin n) (hhigh : n / 2 ≤ focal.val) :
    additiveChoreCost (poCost n r) (poLastLow n focal)
      (poHighImprovement n focal (poLastLow n focal)) = 2 := by
  have hlow : (poLastLow n focal).val < n / 2 := by
    change n / 2 - 1 < n / 2
    omega
  rw [poHighImprovement_last_low_bundle n hn focal hhigh]
  rw [poCost_low_bundle n r (poLastLow n focal) hlow]
  have hA : ({poBFor n (poLastLow n focal) hlow, poBLast n (by omega)} ∩ poAItems n) = ∅ := by
    ext item
    simp [poAItems, poBFor, poBLast, poLastLow, Fin.lt_def, Fin.ext_iff]
    omega
  have hB : ({poBFor n (poLastLow n focal) hlow, poBLast n (by omega)} ∩ poBItems n) =
      {poBFor n (poLastLow n focal) hlow, poBLast n (by omega)} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poBItems, poBFor, poBLast, poLastLow, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  have hC : ({poBFor n (poLastLow n focal) hlow, poBLast n (by omega)} ∩ poCItems n) = ∅ := by
    ext item
    simp [poCItems, poBFor, poBLast, poLastLow, Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  rw [hA, hB, hC]
  have hne : poBFor n (poLastLow n focal) hlow ≠ poBLast n (by omega) := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [poBFor, poBLast, poLastLow] at hval
    omega
  rw [Finset.card_pair hne]
  norm_num

theorem poHighImprovement_other_low_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal low : Fin n)
    (hhigh : n / 2 ≤ focal.val) (hlow : low.val < n / 2) (hne : low ≠ poLastLow n focal) :
    poHighImprovement n focal low = {poAFor n low, poBFor n low hlow} := by
  classical
  have hlowNotSpecial : low.val ≠ n / 2 - 1 := by
    intro heq
    apply hne
    apply Fin.ext
    simp [poLastLow, heq]
  ext item
  simp only [poHighImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ,
    true_and, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold poHighImprovementOwner
  split
  · split
    · simp [poAFor, poBFor]
      omega
    · simp [poAFor, poBFor]
      omega
  · split
    · split
      · simp [poAFor, poBFor]
        omega
      · simp [poAFor, poBFor]
        omega
    · split
      · simp [poAFor, poBFor]
        omega
      · simp [poAFor, poBFor]
        omega

theorem poHighImprovement_other_low_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal low : Fin n)
    (hhigh : n / 2 ≤ focal.val) (hlow : low.val < n / 2) (hne : low ≠ poLastLow n focal) :
    additiveChoreCost (poCost n r) low (poHighImprovement n focal low) = r + 1 := by
  rw [poHighImprovement_other_low_bundle n hn focal low hhigh hlow hne]
  rw [poCost_low_bundle n r low hlow]
  have hA : ({poAFor n low, poBFor n low hlow} ∩ poAItems n) = {poAFor n low} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poAItems, poAFor, poBFor, Fin.lt_def]
    omega
  have hB : ({poAFor n low, poBFor n low hlow} ∩ poBItems n) = {poBFor n low hlow} := by
    ext item
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp [poBItems, poAFor, poBFor, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  have hC : ({poAFor n low, poBFor n low hlow} ∩ poCItems n) = ∅ := by
    ext item
    simp [poCItems, poAFor, poBFor, Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  rw [hA, hB, hC]
  norm_num

theorem poHighImprovement_other_high_bundle
    (n : ℕ) (hn : 4 ≤ n) (focal high : Fin n)
    (hfocal : n / 2 ≤ focal.val) (hhigh : n / 2 ≤ high.val) (hne : high ≠ focal) :
    poHighImprovement n focal high = {poAForHigh n focal high, poCFor n high} := by
  classical
  have hvalNe : high.val ≠ focal.val := by
    intro heq
    apply hne
    apply Fin.ext
    exact heq
  by_cases hhighLast : high.val = n - 1
  · ext item
    simp only [poHighImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ,
      true_and, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    unfold poHighImprovementOwner
    split
    · split
      · simp [poAForHigh, poAFor, poCFor, poLastLow, hhighLast]
        omega
      · simp [poAForHigh, poAFor, poCFor, poLastLow, hhighLast]
        omega
    · split
      · split
        · simp [poAForHigh, poAFor, poCFor, poLastLow, hhighLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, poLastLow, hhighLast]
          omega
      · split
        · simp [poAForHigh, poAFor, poCFor, poLastLow, hhighLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, poLastLow, hhighLast]
          omega
  · ext item
    simp only [poHighImprovement, allocationOfOwner, Finset.mem_filter, Finset.mem_univ,
      true_and, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    unfold poHighImprovementOwner
    split
    · split
      · simp [poAForHigh, poAFor, poCFor, hhighLast]
        omega
      · simp [poAForHigh, poAFor, poCFor, hhighLast]
        omega
    · split
      · split
        · simp [poAForHigh, poAFor, poCFor, hhighLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, hhighLast]
          omega
      · split
        · simp [poAForHigh, poAFor, poCFor, hhighLast]
          omega
        · simp [poAForHigh, poAFor, poCFor, hhighLast]
          omega

theorem poHighImprovement_other_high_cost
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (focal high : Fin n)
    (hfocal : n / 2 ≤ focal.val) (hhigh : n / 2 ≤ high.val) (hne : high ≠ focal) :
    additiveChoreCost (poCost n r) high (poHighImprovement n focal high) = r + 1 := by
  rw [poHighImprovement_other_high_bundle n hn focal high hfocal hhigh hne]
  rw [poCost_high_bundle n r high hhigh]
  by_cases hhighLast : high.val = n - 1
  · have hA : ({poAForHigh n focal high, poCFor n high} ∩ poAItems n) =
        {poAForHigh n focal high} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poAItems, poAForHigh, poAFor, poCFor, poLastLow, hhighLast, Fin.lt_def]
      omega
    have hB : ({poAForHigh n focal high, poCFor n high} ∩ poBItems n) = ∅ := by
      ext item
      simp [poBItems, poAForHigh, poAFor, poCFor, poLastLow, hhighLast,
        Fin.lt_def, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hC : ({poAForHigh n focal high, poCFor n high} ∩ poCItems n) = {poCFor n high} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poCItems, poAForHigh, poAFor, poCFor, poLastLow, hhighLast,
        Fin.le_iff_val_le_val]
      omega
    rw [hA, hB, hC]
    norm_num
  · have hA : ({poAForHigh n focal high, poCFor n high} ∩ poAItems n) =
        {poAForHigh n focal high} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poAItems, poAForHigh, poAFor, poCFor, hhighLast, Fin.lt_def]
      omega
    have hB : ({poAForHigh n focal high, poCFor n high} ∩ poBItems n) = ∅ := by
      ext item
      simp [poBItems, poAForHigh, poAFor, poCFor, hhighLast,
        Fin.lt_def, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hC : ({poAForHigh n focal high, poCFor n high} ∩ poCItems n) = {poCFor n high} := by
      ext item
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      simp [poCItems, poAForHigh, poAFor, poCFor, hhighLast,
        Fin.le_iff_val_le_val]
      omega
    rw [hA, hB, hC]
    norm_num

/-- The B/C-swapped explicit Pareto improvement when the focal high-group
agent has original EFX cost at least `r + 2`. -/
theorem po_high_improvement_pareto_dominates
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation)
    (focal : Fin n) (hfocal : n / 2 ≤ focal.val)
    (hfocalCost : r + 2 ≤ additiveChoreCost (poCost n r) focal (allocation focal)) :
    ParetoDominatesForChores (additiveChoreCost (poCost n r)) allocation
      (poHighImprovement n focal) := by
  constructor
  · intro agent
    by_cases hlow : agent.val < n / 2
    · by_cases hspecial : agent = poLastLow n focal
      · rw [hspecial, poHighImprovement_last_low_cost n hn r focal hfocal]
        have hlower := po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx
          (poLastLow n focal)
        have hrTwo := po_r_gt_two n hn r hr
        linarith
      · rw [poHighImprovement_other_low_cost n hn r focal agent hfocal hlow hspecial]
        exact po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx agent
    · have hhigh : n / 2 ≤ agent.val := by omega
      by_cases hagent : agent = focal
      · subst agent
        rw [poHighImprovement_focal_cost n hn r focal hfocal]
        exact hfocalCost
      · rw [poHighImprovement_other_high_cost n hn r focal agent hfocal hhigh hagent]
        exact po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx agent
  · refine ⟨poLastLow n focal, ?_⟩
    rw [poHighImprovement_last_low_cost n hn r focal hfocal]
    have hlower := po_every_agent_cost_ge_r_add_one n hn r hr allocation halloc hefx
      (poLastLow n focal)
    have hrTwo := po_r_gt_two n hn r hr
    linarith

/-- Theorem 2's conclusion for the explicit `(1,r)` instance: an EFX
allocation is never Pareto-optimal because the source's low- or high-focal
allocation Pareto-dominates it. -/
theorem po_efx_not_pareto_optimal
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ)
    (hr : ((n + 1) / 2 : ℕ) + 1 < r)
    (allocation : Allocation (Fin n) (Fin (2 * n + 1)))
    (halloc : IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))))
    (hefx : EFXForChores (additiveChoreCost (poCost n r)) allocation) :
    ¬ ParetoOptimalForChores (additiveChoreCost (poCost n r)) Finset.univ allocation := by
  intro hoptimal
  obtain ⟨focal, hfocalCost⟩ := po_some_agent_cost_ge_r_add_two n hn r hr allocation halloc hefx
  unfold ParetoOptimalForChores at hoptimal
  apply hoptimal.2
  by_cases hlow : focal.val < n / 2
  · refine ⟨poLowImprovement n focal, poLowImprovement_feasible n focal, ?_⟩
    exact po_low_improvement_pareto_dominates n hn r hr allocation halloc hefx focal hlow hfocalCost
  · have hhigh : n / 2 ≤ focal.val := by omega
    refine ⟨poHighImprovement n focal, poHighImprovement_feasible n focal, ?_⟩
    exact po_high_improvement_pareto_dominates n hn r hr allocation halloc hefx focal hhigh hfocalCost

end HT26EFXChores
