import PG24NoisyMatchingMarkets.MainTheorems

/-!
# PG24 Theorem 4 Coalition-Subset Transport

The analytic proof indexes a coalition by `Fin n`.  The paper's conclusion is
about an actual subset of the coalition inside the broader college market.
These lemmas transport the cardinality certificate across that embedding.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

universe v

/-- The finite coalition represented by an injective index map. -/
def theorem4EmbeddedCoalition {n : ℕ} {GlobalCollege : Type v}
    (embedding : Fin n ↪ GlobalCollege) : Finset GlobalCollege :=
  (Finset.univ : Finset (Fin n)).map embedding

/-- An indexed coalition subset viewed in the broader college carrier. -/
def theorem4EmbeddedCoalitionSubset {n : ℕ} {GlobalCollege : Type v}
    (embedding : Fin n ↪ GlobalCollege) (active : Finset (Fin n)) :
    Finset GlobalCollege :=
  active.map embedding

theorem theorem4EmbeddedCoalitionSubset_subset
    {n : ℕ} {GlobalCollege : Type v}
    (embedding : Fin n ↪ GlobalCollege) (active : Finset (Fin n)) :
    theorem4EmbeddedCoalitionSubset embedding active ⊆
      theorem4EmbeddedCoalition embedding := by
  intro college hcollege
  rcases Finset.mem_map.1 hcollege with ⟨index, _hindex, hindex⟩
  apply Finset.mem_map.2
  exact ⟨index, Finset.mem_univ _, hindex⟩

theorem theorem4EmbeddedCoalition_card
    {n : ℕ} {GlobalCollege : Type v}
    (embedding : Fin n ↪ GlobalCollege) :
    (theorem4EmbeddedCoalition embedding).card = n := by
  simp [theorem4EmbeddedCoalition]

theorem theorem4EmbeddedCoalitionSubset_card
    {n : ℕ} {GlobalCollege : Type v}
    (embedding : Fin n ↪ GlobalCollege) (active : Finset (Fin n)) :
    (theorem4EmbeddedCoalitionSubset embedding active).card = active.card := by
  simp [theorem4EmbeddedCoalitionSubset]

/-- The indexed eventual threshold implies the source theorem's strict size bound. -/
theorem theorem4EmbeddedCoalition_card_gt_of_threshold_le
    {C N : ℕ} {GlobalCollege : Type v}
    (embedding : Fin (C + 1) ↪ GlobalCollege) (hthreshold : N ≤ C) :
    N < (theorem4EmbeddedCoalition embedding).card := by
  rw [theorem4EmbeddedCoalition_card]
  exact Nat.lt_succ_of_le hthreshold

/-- A large indexed subset remains a large actual subset of the embedded coalition. -/
theorem coalitionLargeSubset_embedded_of_indexed
    {n : ℕ} {GlobalCollege : Type v} {epsilon : ℝ}
    (embedding : Fin n ↪ GlobalCollege) (active : Finset (Fin n))
    (hlarge : CoalitionLargeSubset
      (Finset.univ : Finset (Fin n)) active epsilon) :
    CoalitionLargeSubset
      (theorem4EmbeddedCoalition embedding)
      (theorem4EmbeddedCoalitionSubset embedding active) epsilon := by
  refine ⟨theorem4EmbeddedCoalitionSubset_subset embedding active, ?_, ?_⟩
  · simpa [theorem4EmbeddedCoalition] using hlarge.coalition_card_pos
  · simpa [theorem4EmbeddedCoalition, theorem4EmbeddedCoalitionSubset] using
      hlarge.large_ratio

end

end PG24NoisyMatchingMarkets
