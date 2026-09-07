import HT26EFXChores.B1DirectAllocation

/-!
# The source's small-M₂ matching allocation

This file composes the Hall matching for a pool of at most three M₂ chores
with the canonical M₀₁ prefix construction.  It formalizes the allocation in
Case B.2.2(b) of the source: match each M₂ chore to a distinct small endpoint,
make the unmatched agent long in the canonical prefix, and give her no M₂
chore.

Source: `EFXadditivechores.tex`, lines 2506--2524.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- An injective small-endpoint matching, with its unused endpoint made long
in a canonical M₀₁ prefix, gives an EFX allocation. -/
theorem existsEfxOfB1LowMultiplicity_smallMatchingOfEndpointCanonical
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (endpoint : { item // item ∈ m2Chores } → Fin 4)
    (a : ℕ) (long : Fin 4) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquotaLong : quota long = a + 1)
    (hquotaShort : ∀ short : Fin 4, short ≠ long → quota short = a)
    (hinjective : Function.Injective endpoint)
    (hendpointSmall : ∀ item, IsSmallChore cost (endpoint item) item)
    (hunused : ∀ item, endpoint item ≠ long) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  exact ⟨fun agent => prefixAllocation agent ∪ smallEndpointAllocation m2Chores endpoint agent,
    efxForChores_union_of_canonicalLongAndUnitSmallSuffix Item r cost
      prefixChores m2Chores a long quota prefixAllocation
      (smallEndpointAllocation m2Chores endpoint) hr hcost hprefixM2 hcanonical
      hquotaLong hquotaShort (isAllocationOf_smallEndpointAllocation Item m2Chores endpoint)
      (smallEndpointAllocation_eq_empty_of_unused Item m2Chores endpoint long hunused)
      (by
        intro short hshort item hitem
        exact smallEndpointAllocation_mem_small Item cost m2Chores endpoint hendpointSmall short item hitem)
      (by
        intro short _hshort
        exact smallEndpointAllocation_card_le_one_of_injective Item m2Chores endpoint hinjective short)⟩

/-- The complete `|M₂|≤3` branch of source Case B.2.2(b).  The M₀₁ chores
are allocated canonically with the matching's unused agent long; each of the
at most three M₂ chores is then assigned to a distinct agent who finds it
small. -/
theorem existsEfxOfB1LowMultiplicity_m2_card_le_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 2)
    (hm2Card : m2Chores.card ≤ 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨endpoint, long, hinjective, hendpointSmall, hunused⟩ :=
    exists_smallEndpointMatching_with_unused_of_m2_card_le_three Item cost m2Chores
      hm2Small htypeCard hm2Card
  let quota : Fin 4 → ℕ := canonicalQuota a {long}
  have hsum : Finset.univ.sum quota = prefixChores.card := by
    calc
      Finset.univ.sum quota = 4 * a + ({long} : Finset (Fin 4)).card := by
        simpa [quota] using canonicalQuota_sum a ({long} : Finset (Fin 4))
      _ = 4 * a + 1 := by simp
      _ = prefixChores.card := hprefixCard.symm
  obtain ⟨prefixAllocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores quota hsum hprefixSmall
  apply existsEfxOfB1LowMultiplicity_smallMatchingOfEndpointCanonical Item r cost
    prefixChores m2Chores endpoint a long quota prefixAllocation hr hcost hprefixM2 hcanonical
  · simp [quota, canonicalQuota]
  · intro short hshort
    simp [quota, canonicalQuota, hshort]
  · exact hinjective
  · exact hendpointSmall
  · exact hunused

end HT26EFXChores
