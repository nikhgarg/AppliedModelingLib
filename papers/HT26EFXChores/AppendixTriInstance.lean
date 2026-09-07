import HT26EFXChores.AppendixTriConstruction

/-!
# Concrete Appendix-A tri-valued instance

This module instantiates the source's general Appendix-A construction on the
item type required by the public theorem.  The three intervals are the source
classes A, B, and C, and the cost table is deliberately kept in the exact form
used by `AppendixTriConstruction`.

Source: `EFXadditivechores.tex`, Appendix A, lines 2011--2034.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The source construction has `n - 1 + 2s` chores. -/
def appendixItemCount (n : ℕ) : ℕ := n - 1 + 2 * appendixS n

private theorem appendixS_positive (n : ℕ) : 0 < appendixS n := by
  simp only [appendixS]
  omega

private theorem appendixA_endpoint_lt (n : ℕ) : n - 1 < appendixItemCount n := by
  simp only [appendixItemCount]
  have hs := appendixS_positive n
  omega

private theorem appendixBC_endpoint_lt (n : ℕ) : n - 1 + appendixS n < appendixItemCount n := by
  simp only [appendixItemCount]
  have hs := appendixS_positive n
  omega

/-- The `n - 1` universally large chores. -/
def appendixAItems (n : ℕ) : Finset (Fin (appendixItemCount n)) :=
  Finset.Iio ⟨n - 1, appendixA_endpoint_lt n⟩

/-- The first cross-group chore class, of size `s`. -/
def appendixBItems (n : ℕ) : Finset (Fin (appendixItemCount n)) :=
  Finset.Ico ⟨n - 1, appendixA_endpoint_lt n⟩
    ⟨n - 1 + appendixS n, appendixBC_endpoint_lt n⟩

/-- The second cross-group chore class, also of size `s`. -/
def appendixCItems (n : ℕ) : Finset (Fin (appendixItemCount n)) :=
  Finset.Ici ⟨n - 1 + appendixS n, appendixBC_endpoint_lt n⟩

theorem appendixAItems_card (n : ℕ) : (appendixAItems n).card = n - 1 := by
  simp [appendixAItems]

theorem appendixBItems_card (n : ℕ) : (appendixBItems n).card = appendixS n := by
  simp [appendixBItems]

theorem appendixCItems_card (n : ℕ) : (appendixCItems n).card = appendixS n := by
  rw [appendixCItems, Fin.card_Ici]
  change appendixItemCount n - (n - 1 + appendixS n) = appendixS n
  simp only [appendixItemCount]
  omega

theorem appendixA_B_disjoint (n : ℕ) : Disjoint (appendixAItems n) (appendixBItems n) := by
  rw [Finset.disjoint_left]
  intro item hA hB
  simp only [appendixAItems, appendixBItems, Finset.mem_Iio, Finset.mem_Ico] at hA hB
  omega

theorem appendixA_C_disjoint (n : ℕ) : Disjoint (appendixAItems n) (appendixCItems n) := by
  rw [Finset.disjoint_left]
  intro item hA hC
  have hA' : item < (⟨n - 1, appendixA_endpoint_lt n⟩ : Fin (appendixItemCount n)) := by
    simpa [appendixAItems] using hA
  have hC' : (⟨n - 1 + appendixS n, appendixBC_endpoint_lt n⟩ :
      Fin (appendixItemCount n)) ≤ item := by
    simpa [appendixCItems] using hC
  have hAC : (⟨n - 1, appendixA_endpoint_lt n⟩ : Fin (appendixItemCount n)) ≤
      ⟨n - 1 + appendixS n, appendixBC_endpoint_lt n⟩ := by
    apply Fin.le_iff_val_le_val.mpr
    change n - 1 ≤ n - 1 + appendixS n
    omega
  exact (not_lt_of_ge (hAC.trans hC')) hA'

theorem appendixB_C_disjoint (n : ℕ) : Disjoint (appendixBItems n) (appendixCItems n) := by
  rw [Finset.disjoint_left]
  intro item hB hC
  simp only [appendixBItems, appendixCItems, Finset.mem_Ico, Finset.mem_Ici] at hB hC
  omega

theorem appendix_item_partition (n : ℕ) :
    appendixAItems n ∪ appendixBItems n ∪ appendixCItems n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro item
  by_cases hA : item < (⟨n - 1, appendixA_endpoint_lt n⟩ : Fin (appendixItemCount n))
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl (by simpa [appendixAItems] using hA))))
  · by_cases hB : item < (⟨n - 1 + appendixS n, appendixBC_endpoint_lt n⟩ :
        Fin (appendixItemCount n))
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      simp only [appendixBItems, Finset.mem_Ico]
      constructor
      · exact le_of_not_gt hA
      · exact hB
    · refine Finset.mem_union.mpr (Or.inr ?_)
      simp only [appendixCItems, Finset.mem_Ici]
      exact le_of_not_gt hB

/-- The source's two-agent-group tri-valued cost table. -/
def appendixTriCost (n : ℕ) (r q : ℝ)
    (agent : Fin n) (item : Fin (appendixItemCount n)) : ℝ :=
  if item ∈ appendixAItems n then r else
    if agent.val < n / 2 then
      if item ∈ appendixBItems n then 1 else q
    else if item ∈ appendixBItems n then q else 1

theorem appendixTriCost_table (n : ℕ) (r q : ℝ) :
    ∀ (agent : Fin n) item,
      (item ∈ appendixAItems n → appendixTriCost n r q agent item = r) ∧
      (item ∈ appendixBItems n → appendixTriCost n r q agent item =
        if agent.val < n / 2 then 1 else q) ∧
      (item ∈ appendixCItems n → appendixTriCost n r q agent item =
        if agent.val < n / 2 then q else 1) := by
  intro agent item
  constructor
  · intro hA
    simp [appendixTriCost, hA]
  constructor
  · intro hB
    have hnotA : item ∉ appendixAItems n := by
      intro hA
      exact Finset.disjoint_left.mp (appendixA_B_disjoint n) hA hB
    simp [appendixTriCost, hnotA, hB]
  · intro hC
    have hnotA : item ∉ appendixAItems n := by
      intro hA
      exact Finset.disjoint_left.mp (appendixA_C_disjoint n) hA hC
    have hnotB : item ∉ appendixBItems n := by
      intro hB
      exact Finset.disjoint_left.mp (appendixB_C_disjoint n) hB hC
    simp [appendixTriCost, hnotA, hnotB]

theorem appendixTriCost_nonneg (n : ℕ) (r q : ℝ)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (agent : Fin n) (item : Fin (appendixItemCount n)) :
    0 ≤ appendixTriCost n r q agent item := by
  have hqnonneg : 0 ≤ q := by
    rw [hq]
    exact Nat.cast_nonneg _
  have hrnonneg : 0 ≤ r := by
    rw [hr]
    have hs : 0 ≤ (appendixS n : ℝ) := Nat.cast_nonneg _
    have hqone : 0 ≤ q + 1 := by linarith
    exact div_nonneg (mul_nonneg hs hqone) (by norm_num)
  by_cases hA : item ∈ appendixAItems n
  · simp [appendixTriCost, hA, hrnonneg]
  · by_cases hlow : agent.val < n / 2
    · by_cases hB : item ∈ appendixBItems n
      · simp [appendixTriCost, hA, hlow, hB]
      · simp [appendixTriCost, hA, hlow, hB, hqnonneg]
    · by_cases hB : item ∈ appendixBItems n
      · simp [appendixTriCost, hA, hlow, hB, hqnonneg]
      · simp [appendixTriCost, hA, hlow, hB]

theorem appendixTriCost_tri_valued (n : ℕ) (r q : ℝ)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2) :
    IsTriValuedChoreCost (appendixTriCost n r q) := by
  have hqnonneg : 0 ≤ q := by
    rw [hq]
    exact Nat.cast_nonneg _
  have hrnonneg : 0 ≤ r := by
    rw [hr]
    have hs : 0 ≤ (appendixS n : ℝ) := Nat.cast_nonneg _
    have hqone : 0 ≤ q + 1 := by linarith
    exact div_nonneg (mul_nonneg hs hqone) (by norm_num)
  refine ⟨1, q, r, by norm_num, hqnonneg, hrnonneg, ?_⟩
  · intro agent item
    by_cases hA : item ∈ appendixAItems n
    · exact Or.inr (Or.inr (by simp [appendixTriCost, hA]))
    · by_cases hlow : agent.val < n / 2
      · by_cases hB : item ∈ appendixBItems n
        · exact Or.inl (by simp [appendixTriCost, hA, hlow, hB])
        · exact Or.inr (Or.inl (by simp [appendixTriCost, hA, hlow, hB]))
      · by_cases hB : item ∈ appendixBItems n
        · exact Or.inr (Or.inl (by simp [appendixTriCost, hA, hlow, hB]))
        · exact Or.inl (by simp [appendixTriCost, hA, hlow, hB])

/-- The source's middle and largest cost values, attached to the concrete
finite item labelling. -/
noncomputable def appendixTriQ (n : ℕ) : ℝ := appendixQ n

noncomputable def appendixTriR (n : ℕ) : ℝ :=
  (appendixS n : ℝ) * (appendixTriQ n + 1) / 2

/-- The explicit tri-valued instance used for every `n ≥ 4` in Theorem 1. -/
noncomputable def appendixTriInstance (n : ℕ) :
    AdditiveChoreInstance (Fin n) (Fin (appendixItemCount n)) where
  chores := Finset.univ
  cost := appendixTriCost n (appendixTriR n) (appendixTriQ n)
  nonneg := by
    intro agent item
    exact appendixTriCost_nonneg n (appendixTriR n) (appendixTriQ n) rfl rfl agent item

theorem appendixTriInstance_tri_valued (n : ℕ) :
    IsTriValuedChoreCost (appendixTriInstance n).cost := by
  exact appendixTriCost_tri_valued n (appendixTriR n) (appendixTriQ n) rfl rfl

/-- The concrete Appendix-A instance admits no EFX allocation.  Minima are
obtained from the finite agent set, then the generic source-faithful
`appendix_no_efx_proof` discharges the contradiction. -/
theorem appendixTriInstance_no_efx (n : ℕ) (hn : 4 ≤ n)
    (allocation : Allocation (Fin n) (Fin (appendixItemCount n)))
    (halloc : (appendixTriInstance n).IsFeasible allocation) :
    ¬ (appendixTriInstance n).IsEFX allocation := by
  intro hefx
  let r : ℝ := appendixTriR n
  let q : ℝ := appendixTriQ n
  let A : Finset (Fin (appendixItemCount n)) := appendixAItems n
  let B : Finset (Fin (appendixItemCount n)) := appendixBItems n
  let C : Finset (Fin (appendixItemCount n)) := appendixCItems n
  let P1 : Bundle (Fin (appendixItemCount n)) → ℝ := fun bundle =>
    r * (bundle ∩ A).card + (bundle ∩ B).card + q * (bundle ∩ C).card
  let P2 : Bundle (Fin (appendixItemCount n)) → ℝ := fun bundle =>
    r * (bundle ∩ A).card + q * (bundle ∩ B).card + (bundle ∩ C).card
  obtain ⟨min1, _, hmin1⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun agent => P1 (allocation agent)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨min2, _, hmin2⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun agent => P2 (allocation agent)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hq : q = appendixQ n := rfl
  have hr : r = (appendixS n : ℝ) * (q + 1) / 2 := rfl
  have halloc' : IsAllocationOf allocation (Finset.univ : Finset (Fin (appendixItemCount n))) :=
    halloc
  have hefx' : EFXForChores (additiveChoreCost (appendixTriCost n r q)) allocation := hefx
  have hP1 : ∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card +
      q * (bundle ∩ C).card := fun _ => rfl
  have hP2 : ∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card +
      (bundle ∩ C).card := fun _ => rfl
  have hcost := appendixTriCost_table n r q
  have hcostP1 : ∀ (agent : Fin n), agent.val < n / 2 →
      additiveChoreCost (appendixTriCost n r q) agent = P1 := by
    intro agent hlow
    funext bundle
    have hsubset : bundle ⊆ (Finset.univ : Finset (Fin (appendixItemCount n))) := by
      intro item _
      exact Finset.mem_univ _
    simpa [P1, A, B, C] using
      (appendix_cost_low_bundle n (Fin (appendixItemCount n)) r q (appendixTriCost n r q)
        (Finset.univ : Finset (Fin (appendixItemCount n))) A B C bundle
        (by simpa [A, B] using appendixA_B_disjoint n)
        (by simpa [A, C] using appendixA_C_disjoint n)
        (by simpa [B, C] using appendixB_C_disjoint n)
        (by simpa [A, B, C] using appendix_item_partition n) hcost hsubset agent hlow)
  have hcostP2 : ∀ (agent : Fin n), n / 2 ≤ agent.val →
      additiveChoreCost (appendixTriCost n r q) agent = P2 := by
    intro agent hhigh
    funext bundle
    have hsubset : bundle ⊆ (Finset.univ : Finset (Fin (appendixItemCount n))) := by
      intro item _
      exact Finset.mem_univ _
    simpa [P2, A, B, C] using
      (appendix_cost_high_bundle n (Fin (appendixItemCount n)) r q (appendixTriCost n r q)
        (Finset.univ : Finset (Fin (appendixItemCount n))) A B C bundle
        (by simpa [A, B] using appendixA_B_disjoint n)
        (by simpa [A, C] using appendixA_C_disjoint n)
        (by simpa [B, C] using appendixB_C_disjoint n)
        (by simpa [A, B, C] using appendix_item_partition n) hcost hsubset agent hhigh)
  exact appendix_no_efx_proof n (Fin (appendixItemCount n)) r q (appendixTriCost n r q)
    (Finset.univ : Finset (Fin (appendixItemCount n))) A B C allocation P1 P2
    (P1 (allocation min1)) (P2 (allocation min2)) hn hq hr
    (by simpa [A] using appendixAItems_card n)
    (by simpa [B] using appendixBItems_card n)
    (by simpa [C] using appendixCItems_card n)
    (by simpa [A, B] using appendixA_B_disjoint n)
    (by simpa [A, C] using appendixA_C_disjoint n)
    (by simpa [B, C] using appendixB_C_disjoint n)
    (by simpa [A, B, C] using appendix_item_partition n) hcost halloc' hefx' hP1 hP2 hcostP1 hcostP2
    ⟨min1, rfl⟩ (fun agent => hmin1 agent (Finset.mem_univ _))
    ⟨min2, rfl⟩ (fun agent => hmin2 agent (Finset.mem_univ _))

end HT26EFXChores
