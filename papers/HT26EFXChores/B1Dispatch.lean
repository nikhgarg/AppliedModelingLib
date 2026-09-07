import HT26EFXChores.B1LargeIncidenceAllocation
import HT26EFXChores.B1SmallMatchingAllocation
import HT26EFXChores.B1FourEdgeProfileAllocation
import HT26EFXChores.M34Extension

/-!
# Outer dispatch for source Case B.2.2

The two source schedules for a low-multiplicity M₂ pool are joined here.  The
first branch uses an agent with three large chores; otherwise the complementary
large-incidence bounds force the M₂ pool to have at most four chores.

Source: `EFXadditivechores.tex`, lines 2472--2542.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- A quota vector of total size `4a+1` with entries in `{a,a+1}` has one
long agent.  The relabelling names that agent `0`. -/
theorem exists_b1_quota_relabelling
    (a : ℕ) (quota : Fin 4 → ℕ)
    (hquota : ∀ agent, quota agent = a ∨ quota agent = a + 1)
    (hsum : Finset.univ.sum quota = 4 * a + 1) :
    ∃ labels : Fin 4 ≃ Fin 4,
      quota (labels 0) = a + 1 ∧ quota (labels 1) = a ∧
        quota (labels 2) = a ∧ quota (labels 3) = a := by
  have hsumFour : quota 0 + quota 1 + quota 2 + quota 3 = 4 * a + 1 := by
    simpa [Fin.sum_univ_four, Nat.add_assoc] using hsum
  rcases hquota 0 with h0 | h0
  · rcases hquota 1 with h1 | h1
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · omega
        · exact ⟨Equiv.swap 0 3, by simpa [Equiv.swap_apply_def] using h3,
            by simpa [Equiv.swap_apply_def] using h1,
            by simpa [Equiv.swap_apply_def] using h2,
            by simpa [Equiv.swap_apply_def] using h0⟩
      · rcases hquota 3 with h3 | h3
        · exact ⟨Equiv.swap 0 2, by simpa [Equiv.swap_apply_def] using h2,
            by simpa [Equiv.swap_apply_def] using h1,
            by simpa [Equiv.swap_apply_def] using h0,
            by simpa [Equiv.swap_apply_def] using h3⟩
        · omega
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · exact ⟨Equiv.swap 0 1, by simpa [Equiv.swap_apply_def] using h1,
            by simpa [Equiv.swap_apply_def] using h0,
            by simpa [Equiv.swap_apply_def] using h2,
            by simpa [Equiv.swap_apply_def] using h3⟩
        · omega
      · rcases hquota 3 with h3 | h3 <;> omega
  · rcases hquota 1 with h1 | h1
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · exact ⟨Equiv.refl (Fin 4), h0, h1, h2, h3⟩
        · omega
      · rcases hquota 3 with h3 | h3 <;> omega
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3 <;> omega
      · rcases hquota 3 with h3 | h3 <;> omega

/-- The four-chore no-three-large schedule transports across a relabelling
that names the unique long canonical-prefix agent `0`. -/
theorem existsEfxOfB1LowMultiplicity_four_of_relabelled_prefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hm2Card : m2Chores.card = 4)
    (hsmall : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hlarge : ∀ agent : Fin 4, (largeChoreSet cost r agent m2Chores).card ≤ 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1LowMultiplicity_m2_card_four_of_no_three_large Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a
    (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
  · simpa [relabelQuota] using hquota0
  · simpa [relabelQuota] using hquota1
  · simpa [relabelQuota] using hquota2
  · simpa [relabelQuota] using hquota3
  · intro short hshort
    have hshortQuota : quota (labels short) = a := by
      fin_cases short
      · exact (hshort rfl).elim
      · exact hquota1
      · exact hquota2
      · exact hquota3
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) (labels 0)
        hshortQuota
        (by simpa [relabelQuota] using hquota0)
  · exact hm2Card
  · intro item hitem
    exact (hsmall item hitem).relabel labels cost item
  · intro agent
    simpa only [largeChoreSet_relabel] using hlarge (labels agent)

/-- Complete source Case B.2.2.  If an agent has three M₂ chores large for
her, the source's triple matching fills the three short bundles.  Otherwise
every large-incidence degree is at most two, which counts each M₂ chore twice
and gives `|M₂|≤4`; the matching and four-edge schedules then finish the two
remaining cardinality cases. -/
theorem existsEfxOfB1LowMultiplicity_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  by_cases hthree : ∃ agent : Fin 4, 3 ≤ (largeChoreSet cost r agent m2Chores).card
  · obtain ⟨agent, hagent⟩ := hthree
    let quota : Fin 4 → ℕ := canonicalQuota a {agent}
    have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
      calc
        Finset.univ.sum quota = 4 * a + ({agent} : Finset (Fin 4)).card := by
          simpa [quota] using canonicalQuota_sum a ({agent} : Finset (Fin 4))
        _ = 4 * a + 1 := by simp
        _ = prefixChores.card := hprefixCard.symm
    obtain ⟨prefixAllocation, hcanonical⟩ :=
      existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
    fin_cases agent
    · exact existsEfxOfB1LowMultiplicity_threeLarge_of_relabelled Item r cost
        (Equiv.refl (Fin 4)) prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2
        hcanonical (by simp [quota, canonicalQuota]) (by simp [quota, canonicalQuota])
        (by simp [quota, canonicalQuota]) (by simp [quota, canonicalQuota]) hm2Small htypeCard
        (by simpa using hagent)
    · exact existsEfxOfB1LowMultiplicity_threeLarge_of_relabelled Item r cost
        (Equiv.swap 0 1) prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2
        hcanonical (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def]) hm2Small htypeCard
        (by simpa [Equiv.swap_apply_def] using hagent)
    · exact existsEfxOfB1LowMultiplicity_threeLarge_of_relabelled Item r cost
        (Equiv.swap 0 2) prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2
        hcanonical (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def]) hm2Small htypeCard
        (by simpa [Equiv.swap_apply_def] using hagent)
    · exact existsEfxOfB1LowMultiplicity_threeLarge_of_relabelled Item r cost
        (Equiv.swap 0 3) prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2
        hcanonical (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def])
        (by simp [quota, canonicalQuota, Equiv.swap_apply_def]) hm2Small htypeCard
        (by simpa [Equiv.swap_apply_def] using hagent)
  · have hlarge : ∀ agent : Fin 4, (largeChoreSet cost r agent m2Chores).card ≤ 2 := by
      intro agent
      by_contra hnot
      apply hthree
      refine ⟨agent, ?_⟩
      omega
    have hm2CardLeFour : m2Chores.card ≤ 4 :=
      m2_card_le_four_of_no_three_large Item r cost m2Chores hcost hm2Small hlarge
    by_cases hm2CardLeThree : m2Chores.card ≤ 3
    · exact existsEfxOfB1LowMultiplicity_m2_card_le_three Item r cost prefixChores m2Chores a
        hr hcost hprefixM2 hprefixCard hprefixSmall hm2Small htypeCard hm2CardLeThree
    · have hm2Card : m2Chores.card = 4 := by omega
      obtain ⟨quota, prefixAllocation, hquota, hcanonical, hsuper⟩ :=
        existsSuperCanonicalSmallChoreAllocation Item r cost prefixChores a 1 (by linarith)
          hcost (by omega) (by omega) hprefixCard hprefixSmall
      have hquotaSum : Finset.univ.sum quota = 4 * a + 1 := by
        calc
          Finset.univ.sum quota =
              Finset.univ.sum (fun agent => (prefixAllocation agent).card) := by
            apply Finset.sum_congr rfl
            intro agent _
            symm
            exact (hcanonical.2 agent).1
          _ = prefixChores.card :=
            sum_card_allocation_eq_card_of_isAllocation prefixAllocation prefixChores hcanonical.1
          _ = 4 * a + 1 := hprefixCard
      obtain ⟨labels, hquota0, hquota1, hquota2, hquota3⟩ :=
        exists_b1_quota_relabelling a quota hquota hquotaSum
      exact existsEfxOfB1LowMultiplicity_four_of_relabelled_prefix Item r cost labels
        prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2 hcanonical
        hquota0 hquota1 hquota2 hquota3 hsuper hm2Card hm2Small hlarge

/-- The complete low-multiplicity `b = 1` source case after the paper's
iterated M₃₄ insertion restores the remaining chores. -/
theorem existsEfxOfM01M2M34_b1Low
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 1)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEFX⟩ :=
    existsEfxOfB1LowMultiplicity_dispatch Item r cost prefixChores m2Chores a hr hcost
      hprefixCard hprefixSmall hm2Small hprefixM2 htypeCard
  have hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores := by
    rw [Finset.disjoint_left]
    intro item hbase hm34
    rcases Finset.mem_union.mp hbase with hprefix | hm2
    · exact (Finset.disjoint_left.mp hprefixM34 hprefix hm34).elim
    · exact (Finset.disjoint_left.mp hm2M34 hm2 hm34).elim
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEFX

/-- Every normalized remainder-one instance with no M₂ edge fibre of
multiplicity above two admits EFX. -/
theorem existsEfxOfOneOrR_b1_of_m2TypeCard_le_two
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcard : (m01ChorePool cost chores).card = 4 * a + 1)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost (m2ChorePool cost chores) smallAgents).card ≤ 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfM01M2M34_b1Low Item r cost (m01ChorePool cost chores)
      (m2ChorePool cost chores) (m34ChorePool cost chores) a hr hcost
      (m01ChorePool_disjoint_m2ChorePool cost chores)
      (m01ChorePool_disjoint_m34ChorePool cost chores)
      (m2ChorePool_disjoint_m34ChorePool cost chores) hcard
      (m01ChorePool_small cost chores) (m2ChorePool_small cost chores)
      (m34ChorePool_small cost chores) htypeCard
  refine ⟨allocation, ?_, hefx⟩
  simpa only [← Finset.union_assoc, m01_m2_m34_union_eq] using hallocation

end HT26EFXChores
