import HT26EFXChores.M2Orientation

/-!
# Equal-value bi-valued chores

The paper's definition permits the two advertised values to coincide.  In
that homogeneous case, a balanced-cardinality allocation is EFX directly.
This is kept separate from positive normalization, which requires distinct
strictly positive values.

Source: `EFXadditivechores.tex`, lines 294--296.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Every homogeneous four-agent additive chore pool has a balanced-cardinality
EFX allocation. -/
theorem existsEfxOfConstantChoreCost
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (value : ℝ)
    (hnonneg : 0 ≤ value)
    (hconstant : ∀ agent item, cost agent item = value) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let q : ℕ := chores.card / 4
  let b : ℕ := chores.card % 4
  have hb : b ≤ (Finset.univ : Finset (Fin 4)).card := by
    dsimp [b]
    have hlt : chores.card % 4 < 4 := Nat.mod_lt _ (by omega)
    norm_num
    omega
  obtain ⟨longAgents, _, hlongCard⟩ :=
    (Finset.univ : Finset (Fin 4)).exists_subset_card_eq hb
  let quota : Fin 4 → ℕ := m2Quota q longAgents
  have hquotaSum : Finset.univ.sum quota = chores.card := by
    rw [show quota = m2Quota q longAgents by rfl, m2Quota_sum, hlongCard]
    dsimp [q, b] at hlongCard ⊢
    omega
  obtain ⟨allocation, halloc, hcard⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores quota hquotaSum
  have hbalanced : ∀ first second, (allocation first).card ≤ (allocation second).card + 1 := by
    intro first second
    rw [hcard first, hcard second]
    dsimp [quota, m2Quota]
    by_cases hfirst : first ∈ longAgents
    · by_cases hsecond : second ∈ longAgents
      · simp [hfirst, hsecond]
      · simp [hfirst, hsecond]
    · by_cases hsecond : second ∈ longAgents
      · simp [hfirst, hsecond]
        omega
      · simp [hfirst, hsecond]
  refine ⟨allocation, halloc, ?_⟩
  exact efxForChores_of_balanced_card_and_agentwise_constant cost allocation
    (fun _ => value) (fun _ => hnonneg)
    (fun agent _ item _ => hconstant agent item) hbalanced

/-- The coincident-value branch of a bi-valued profile is homogeneous and
therefore has EFX. -/
theorem existsEfxOfEqualBiValuedChoreCost
    (Item : Type) [DecidableEq Item] (p q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hpq : p = q) (hp : 0 ≤ p)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  apply existsEfxOfConstantChoreCost Item cost chores p hp
  intro agent item
  rcases hvalues agent item with hvalue | hvalue
  · exact hvalue
  · exact hvalue.trans hpq.symm

end HT26EFXChores
